use std::fmt;
use std::ops::{AddAssign, Mul, Neg, SubAssign};

use bls12_381::G2Projective;
use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
use curv::arithmetic::traits::*;
use curv::BigInt;
use curv::elliptic::curves::{Curve, DeserializationError, ECPoint, ECScalar, NotOnCurve, PointCoords};
use generic_array::GenericArray;
use pairing::group::Curve as GroupCurve;
use serde::{Deserialize, Deserializer};
use serde::de::{Error, MapAccess, SeqAccess, Visitor};
use serde::ser::{Serialize, Serializer};
use serde::ser::SerializeStruct;
use zeroize::Zeroize;

use super::scalar::FieldScalar;

lazy_static::lazy_static! {
    static ref GENERATOR: G2Point = G2Point {
        purpose: "generator",
        ge: PK::generator(),
    };

    static ref BASE_POINT2: G2Point = {
        const BASE_POINT2: [u8; 192] = [
            10, 171, 191, 0, 165, 128, 154, 219, 38, 59, 180, 198, 223, 124, 148, 112, 212, 13,
            121, 116, 67, 51, 69, 225, 123, 58, 65, 247, 156, 59, 136, 127, 69, 195, 145, 42, 129,
            183, 180, 24, 133, 235, 91, 7, 8, 124, 159, 252, 12, 127, 52, 139, 183, 175, 115, 201,
            98, 117, 239, 5, 116, 244, 30, 150, 215, 90, 75, 40, 43, 154, 34, 140, 116, 245, 205,
            90, 220, 100, 102, 223, 78, 183, 184, 218, 235, 225, 202, 36, 15, 111, 170, 6, 172,
            81, 126, 81, 12, 152, 225, 206, 104, 117, 104, 117, 192, 83, 226, 193, 223, 117, 136,
            3, 86, 37, 33, 84, 159, 218, 122, 29, 245, 222, 52, 17, 136, 82, 60, 224, 174, 55,
            210, 63, 163, 136, 8, 162, 196, 226, 13, 134, 142, 254, 149, 231, 12, 212, 187, 122,
            205, 1, 14, 82, 30, 254, 55, 188, 248, 119, 91, 122, 89, 184, 151, 106, 209, 15, 63,
            178, 4, 71, 17, 156, 195, 3, 58, 72, 212, 27, 84, 79, 252, 133, 68, 160, 240, 188, 95,
            162, 172, 87, 115, 19
        ];

        let g2_affine = bls12_381::G2Affine::from_uncompressed(&BASE_POINT2);
        G2Point {
            purpose: "base_point2",
            ge: g2_affine.unwrap(),
        }
    };
}

pub const SECRET_KEY_SIZE: usize = 32;
pub const COMPRESSED_SIZE: usize = 96;

pub type SK = bls12_381::Scalar;
pub type PK = bls12_381::G2Affine;

/// Bls12-381-2 (G2) curve implementation based on [pairing_plus] library
#[derive(PartialEq, Debug, Clone)]
pub enum Bls12_381_2 {}

#[derive(Clone, Copy)]
pub struct G2Point {
    purpose: &'static str,
    ge: PK,
}

pub type GE2 = G2Point;

impl Curve for Bls12_381_2 {
    type Point = GE2;
    type Scalar = FieldScalar;

    const CURVE_NAME: &'static str = "bls12_381_1";
}

impl ECPoint for G2Point {
    type Scalar = FieldScalar;
    type Underlying = PK;

    type CompressedPointLength = typenum::U96;
    type UncompressedPointLength = typenum::U192;

    fn zero() -> G2Point {
        G2Point {
            purpose: "zero",
            ge: PK::identity(),
        }
    }

    fn is_zero(&self) -> bool {
        self.ge.is_identity().into()
    }

    fn generator() -> &'static G2Point {
        &GENERATOR
    }

    fn base_point2() -> &'static G2Point {
        &BASE_POINT2
    }

    fn from_coords(x: &BigInt, y: &BigInt) -> Result<G2Point, NotOnCurve> {
        let vec_x = x.to_bytes();
        let vec_y = y.to_bytes();
        if vec_x.len() > COMPRESSED_SIZE || vec_y.len() > COMPRESSED_SIZE {
            return Err(NotOnCurve);
        }
        let mut uncompressed = [0u8; 2 * COMPRESSED_SIZE];
        uncompressed[COMPRESSED_SIZE - vec_x.len()..COMPRESSED_SIZE].copy_from_slice(&vec_x);
        uncompressed[(2 * COMPRESSED_SIZE) - vec_y.len()..].copy_from_slice(&vec_y);
        debug_assert_eq!(x, &BigInt::from_bytes(&uncompressed[..COMPRESSED_SIZE]));
        debug_assert_eq!(y, &BigInt::from_bytes(&uncompressed[COMPRESSED_SIZE..]));

        let g2_affine = bls12_381::G2Affine::from_uncompressed(&uncompressed);

        match Option::from(g2_affine) {
            Some(g2_affine) => {
                Ok(G2Point {
                    purpose: "from_coords",
                    ge: g2_affine,
                })
            }
            None => { Err(NotOnCurve) }
        }
    }

    fn x_coord(&self) -> Option<BigInt> {
        if self.is_zero() {
            None
        } else {
            let uncompressed = self.ge.to_uncompressed();
            let x_coord = &uncompressed.as_ref()[0..COMPRESSED_SIZE];
            let bn = BigInt::from_bytes(x_coord);
            Some(bn)
        }
    }

    fn y_coord(&self) -> Option<BigInt> {
        if self.is_zero() {
            None
        } else {
            let uncompressed = self.ge.to_uncompressed();
            let y_coord = &uncompressed.as_ref()[COMPRESSED_SIZE..COMPRESSED_SIZE * 2];
            let bn = BigInt::from_bytes(y_coord);
            Some(bn)
        }
    }

    fn coords(&self) -> Option<PointCoords> {
        if self.is_zero() {
            None
        } else {
            let uncompressed = self.ge.to_uncompressed();
            let x = &uncompressed.as_ref()[0..COMPRESSED_SIZE];
            let y = &uncompressed.as_ref()[COMPRESSED_SIZE..COMPRESSED_SIZE * 2];
            let x = BigInt::from_bytes(x);
            let y = BigInt::from_bytes(y);
            Some(PointCoords { x, y })
        }
    }

    fn serialize_compressed(&self) -> GenericArray<u8, Self::CompressedPointLength> {
        let compressed = self.ge.to_compressed();
        *GenericArray::from_slice(compressed.as_slice())
    }

    fn serialize_uncompressed(&self) -> GenericArray<u8, Self::UncompressedPointLength> {
        let uncompressed = self.ge.to_uncompressed();
        *GenericArray::from_slice(uncompressed.as_slice())
    }

    fn deserialize(bytes: &[u8]) -> Result<G2Point, DeserializationError> {
        if bytes.len() == COMPRESSED_SIZE {
            let mut bytes_array_comp = [0u8; COMPRESSED_SIZE];
            bytes_array_comp.copy_from_slice(&bytes[..COMPRESSED_SIZE]);
            let g2_affine = bls12_381::G2Affine::from_compressed(&bytes_array_comp);
            match Option::from(g2_affine) {
                Some(g2_affine) => {
                    Ok(G2Point {
                        purpose: "deserialize",
                        ge: g2_affine,
                    })
                }
                None => { Err(DeserializationError) }
            }
        } else if bytes.len() == 2 * COMPRESSED_SIZE {
            let mut bytes_array_uncomp = [0u8; 2 * COMPRESSED_SIZE];
            bytes_array_uncomp.copy_from_slice(&bytes[..2 * COMPRESSED_SIZE]);
            let g2_affine = bls12_381::G2Affine::from_uncompressed(&bytes_array_uncomp);
            match Option::from(g2_affine) {
                Some(g2_affine) => {
                    Ok(G2Point {
                        purpose: "deserialize",
                        ge: g2_affine,
                    })
                }
                None => { Err(DeserializationError) }
            }
        } else {
            Err(DeserializationError)
        }
    }

    fn check_point_order_equals_group_order(&self) -> bool {
        !self.is_zero() && self.in_subgroup()
    }

    fn scalar_mul(&self, scalar: &Self::Scalar) -> G2Point {
        let result = self.ge.mul(scalar.underlying_ref());
        G2Point {
            purpose: "scalar_mul",
            ge: result.to_affine(),
        }
    }

    fn add_point(&self, other: &Self) -> G2Point {
        let mut result = bls12_381::G2Projective::from(self.ge);
        result.add_assign(&other.ge);
        G2Point {
            purpose: "add_point",
            ge: result.to_affine(),
        }
    }

    fn sub_point(&self, other: &Self) -> G2Point {
        let mut result = bls12_381::G2Projective::from(self.ge);
        result.sub_assign(&other.ge);
        G2Point {
            purpose: "sub_point",
            ge: result.to_affine(),
        }
    }

    fn neg_point(&self) -> Self {
        let mut result = self.ge;
        result = result.neg();
        G2Point {
            purpose: "neg",
            ge: result,
        }
    }

    fn neg_point_assign(&mut self) {
        self.ge = self.ge.neg();
    }

    fn underlying_ref(&self) -> &Self::Underlying {
        &self.ge
    }
    fn underlying_mut(&mut self) -> &mut Self::Underlying {
        &mut self.ge
    }
    fn from_underlying(ge: Self::Underlying) -> G2Point {
        G2Point {
            purpose: "from_underlying",
            ge,
        }
    }
}

impl G2Point {
    fn in_subgroup(&self) -> bool {
        bool::from(self.ge.is_on_curve()) && self.is_in_correct_subgroup_assuming_on_curve()
    }

    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        self.scalar_mul(&FieldScalar::from_bigint(FieldScalar::group_order())).is_zero()
    }

    pub fn hash_to_curve(message: &[u8], dst: &[u8]) -> Self {
        let projective = <G2Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(
            message, dst,
        );
        G2Point {
            purpose: "hash_to_curve",
            ge: projective.to_affine(),
        }
    }
}

impl fmt::Debug for G2Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Point {{ purpose: {:?}, uncompressed: {:?} }}",
            self.purpose,
            hex::encode(self.serialize_uncompressed()),
        )
    }
}

impl PartialEq for G2Point {
    fn eq(&self, other: &G2Point) -> bool {
        self.ge == other.ge
    }
}

impl Zeroize for G2Point {
    fn zeroize(&mut self) {
        self.ge.zeroize()
    }
}


impl Serialize for G2Point {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
    {
        let bytes = self.serialize_compressed();
        let bytes_as_bn = BigInt::from_bytes(&bytes[..]);
        let mut state = serializer.serialize_struct("Bls12381G2Point", 1)?;
        state.serialize_field("bytes_str", &bytes_as_bn.to_hex())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for G2Point {
    fn deserialize<D>(deserializer: D) -> Result<G2Point, D::Error>
        where
            D: Deserializer<'de>,
    {
        const FIELDS: &[&str] = &["bytes_str"];
        deserializer.deserialize_struct("Bls12381G2Point", FIELDS, Bls12381G2PointVisitor)
    }
}

struct Bls12381G2PointVisitor;

impl<'de> Visitor<'de> for Bls12381G2PointVisitor {
    type Value = G2Point;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("Bls12381G2Point")
    }

    fn visit_seq<V>(self, mut seq: V) -> Result<G2Point, V::Error>
        where
            V: SeqAccess<'de>,
    {
        let bytes_str = seq
            .next_element()?
            .ok_or_else(|| V::Error::invalid_length(0, &"a single element"))?;
        let bytes_bn = BigInt::from_hex(bytes_str).map_err(V::Error::custom)?;
        let bytes = BigInt::to_bytes(&bytes_bn);
        <G2Point as ECPoint>::deserialize(&bytes[..]).map_err(|_| V::Error::custom("failed to parse g2 point"))
    }

    fn visit_map<E: MapAccess<'de>>(self, mut map: E) -> Result<G2Point, E::Error> {
        let mut bytes_str: String = "".to_string();

        while let Some(key) = map.next_key::<&'de str>()? {
            let v = map.next_value::<&'de str>()?;
            match key {
                "bytes_str" => {
                    bytes_str = String::from(v);
                }
                _ => return Err(E::Error::unknown_field(key, &["bytes_str"])),
            }
        }
        let bytes_bn = BigInt::from_hex(&bytes_str).map_err(E::Error::custom)?;
        let bytes = BigInt::to_bytes(&bytes_bn);

        <G2Point as ECPoint>::deserialize(&bytes[..]).map_err(|_| E::Error::custom("failed to parse g2 point"))
    }
}


#[cfg(test)]
mod tests {
    use bls12_381::G2Projective;
    use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
    use curv::arithmetic::{Converter, Modulo};
    use curv::BigInt;
    use pairing::group::Curve;

    use crate::g2::{ECScalar, G2Point, GE2, PK};
    use crate::scalar::FieldScalar;

    use super::ECPoint;

    #[test]
    fn test_serdes_pk() {
        let pk = GE2::generator().clone();
        let s = serde_json::to_string(&pk).expect("Failed in serialization");
        let des_pk: GE2 = serde_json::from_str(&s).expect("Failed in deserialization");
        assert_eq!(des_pk, pk);

        let pk = GE2::base_point2().clone();
        let s = serde_json::to_string(&pk).expect("Failed in serialization");
        let des_pk: GE2 = serde_json::from_str(&s).expect("Failed in deserialization");
        assert_eq!(des_pk, pk);
    }

    #[test]
    fn bincode_pk() {
        let pk = GE2::generator().clone();
        let bin = bincode::serialize(&pk).unwrap();
        let decoded: G2Point = bincode::deserialize(bin.as_slice()).unwrap();
        assert_eq!(decoded, pk);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::op_ref)] // Enables type inference.
    fn test_serdes_bad_pk() {
        let pk = GE2::generator();
        let s = serde_json::to_string(&pk).expect("Failed in serialization");
        // we make sure that the string encodes invalid point:
        let s: String = s.replace("30", "20");
        let des_pk: GE2 = serde_json::from_str(&s).expect("Failed in deserialization");
        let eight = ECScalar::from_bigint(&BigInt::from(8));
        assert_eq!(des_pk, pk.scalar_mul(&eight));
    }

    #[test]
    fn test_from_mpz() {
        let rand_scalar: FieldScalar = ECScalar::random();
        let rand_bn = rand_scalar.to_bigint();
        let rand_scalar2: FieldScalar = ECScalar::from_bigint(&rand_bn);
        assert_eq!(rand_scalar, rand_scalar2);
    }

    #[test]
    fn test_minus_point() {
        let a: FieldScalar = ECScalar::random();
        let b: FieldScalar = ECScalar::random();
        let a_minus_b_fe: FieldScalar = a.sub(&b);
        let base: GE2 = *ECPoint::generator();

        let point_ab1 = base.scalar_mul(&a_minus_b_fe);
        let point_a = base.scalar_mul(&a);
        let point_b = base.scalar_mul(&b);
        let point_ab2 = point_a.sub_point(&point_b);
        println!(
            "point ab1: {:?}",
            hex::encode(point_ab1.serialize_compressed())
        );
        println!(
            "point ab2: {:?}",
            hex::encode(point_ab2.serialize_compressed())
        );

        assert_eq!(point_ab1, point_ab2);
    }

    #[test]
    fn test_add_point() {
        let a: FieldScalar = ECScalar::random();
        let b: FieldScalar = ECScalar::random();
        let a_plus_b_fe = a.add(&b);
        let base: GE2 = *ECPoint::generator();
        let point_ab1 = base.scalar_mul(&a_plus_b_fe);
        let point_a = base.scalar_mul(&a);
        let point_b = base.scalar_mul(&b);
        let point_ab2 = point_a.add_point(&point_b);

        assert_eq!(point_ab1, point_ab2);
    }

    #[test]
    fn test_add_scalar() {
        let a: FieldScalar = ECScalar::random();
        let zero: FieldScalar = FieldScalar::zero();
        let a_plus_zero: FieldScalar = a.add(&zero);

        assert_eq!(a_plus_zero, a);
    }

    #[test]
    fn test_mul_scalar() {
        let a = [
            10, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 10, 10, 10,
        ];

        let a_bn = BigInt::from_bytes(&a[..]);
        let a_fe: FieldScalar = ECScalar::from_bigint(&a_bn);

        let five = BigInt::from(5);
        let five_fe: FieldScalar = ECScalar::from_bigint(&five);
        println!("five_fe: {:?}", five_fe.clone());
        let five_a_bn = BigInt::mod_mul(&a_bn, &five, &FieldScalar::group_order());
        let five_a_fe = five_fe.mul(&a_fe);
        let five_a_fe_2: FieldScalar = ECScalar::from_bigint(&five_a_bn);

        assert_eq!(five_a_fe, five_a_fe_2);
    }

    #[test]
    fn test_mul_point() {
        let a: FieldScalar = ECScalar::random();
        let b: FieldScalar = ECScalar::random();
        let a_mul_b_fe = a.mul(&b);
        let base: GE2 = *ECPoint::generator();
        let point_ab1 = base.scalar_mul(&a_mul_b_fe);
        let point_a = base.scalar_mul(&a);
        let point_ab2 = point_a.scalar_mul(&b);

        assert_eq!(point_ab1, point_ab2);
    }

    #[test]
    fn test_invert() {
        let a: FieldScalar = ECScalar::random();

        let a_bn = a.to_bigint();

        let a_inv = a.invert().unwrap();
        let a_inv_bn_1 = BigInt::mod_inv(&a_bn, &FieldScalar::group_order()).unwrap();
        let a_inv_bn_2 = a_inv.to_bigint();

        assert_eq!(a_inv_bn_1, a_inv_bn_2);
    }

    #[test]
    fn test_scalar_mul_multiply_by_1() {
        let g: GE2 = *ECPoint::generator();

        let fe: FieldScalar = ECScalar::from_bigint(&BigInt::from(1));
        let b_tag = g.scalar_mul(&fe);
        assert_eq!(b_tag, g);
    }

    #[test]
    fn base_point2_nothing_up_my_sleeve() {
        // Generate base_point2
        let cs = &[1u8];
        let msg = &[1u8];
        println!("{}", hex::encode(cs));
        println!("{}", hex::encode(msg));
        let projective = <G2Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(msg, cs);
        let point = G2Point {
            purpose: "test",
            ge: projective.to_affine(),
        };

        assert!(point.in_subgroup());

        // Check that ECPoint::base_point2() returns generated point
        let base_point2 = G2Point::base_point2();

        assert!(base_point2.in_subgroup());
        assert_eq!(projective.to_affine(), base_point2.ge);
    }

    #[test]
    fn test_serde() {
        use serde::{Serialize, Deserialize};
        #[derive(Debug, PartialEq, Serialize, Deserialize)]
        struct Wrapper {
            inner: G2Point,
        }
        let wrapper = Wrapper {
            inner: G2Point {
                purpose: "example",
                ge: PK::generator(),
            }
        };
        let json_str = serde_json::to_string(&wrapper);
        assert!(json_str.is_ok());
        let deserialized = serde_json::from_slice::<Wrapper>(json_str.unwrap().as_bytes());
        assert_eq!(wrapper.inner.ge, deserialized.unwrap().inner.ge);
    }
}
