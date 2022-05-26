use std::fmt;
use std::ops::{AddAssign, Mul, Neg, SubAssign};

use bls12_381::G1Projective;
use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
use curv::arithmetic::traits::*;
use curv::BigInt;
use curv::elliptic::curves::{Curve, DeserializationError, ECPoint, ECScalar, NotOnCurve, PointCoords};
use generic_array::GenericArray;
use pairing::group::Curve as pCurve;
use serde::{Deserialize, Deserializer};
use serde::de::{Error, MapAccess, SeqAccess, Visitor};
use serde::ser::{Serialize, Serializer};
use serde::ser::SerializeStruct;
use zeroize::Zeroize;

use super::scalar::FieldScalar;

lazy_static::lazy_static! {
    static ref GENERATOR: G1Point = G1Point {
        purpose: "generator",
        ge: PK::generator(),
    };

    static ref BASE_POINT2: G1Point = {
        const BASE_POINT2: [u8; 96] = [
            10, 18, 122, 36, 178, 251, 236, 31, 139, 88, 242, 163, 21, 198, 168, 208, 122, 195,
            135, 122, 7, 153, 197, 255, 160, 0, 89, 138, 39, 245, 105, 108, 99, 113, 78, 70, 130,
            172, 183, 57, 170, 180, 39, 32, 173, 29, 238, 62, 12, 90, 164, 143, 132, 110, 153,
            163, 48, 128, 36, 227, 49, 32, 193, 77, 130, 190, 120, 248, 189, 49, 40, 218, 132,
            234, 16, 110, 191, 60, 17, 33, 170, 200, 32, 223, 12, 44, 64, 46, 136, 127, 149, 59,
            132, 184, 99, 184
        ];
        let g1_affine = bls12_381::G1Affine::from_uncompressed(&BASE_POINT2);
        G1Point {
            purpose: "base_point2",
            ge: g1_affine.unwrap(),
        }
    };
}

pub const SECRET_KEY_SIZE: usize = 32;
pub const COMPRESSED_SIZE: usize = 48;

pub type PK = bls12_381::G1Affine;

/// Bls12-381-1 (G1) curve implementation based on [pairing_plus] library
#[derive(Debug, PartialEq, Clone)]
pub enum Bls12_381_1 {}

#[derive(Clone, Copy)]
pub struct G1Point {
    purpose: &'static str,
    ge: PK,
}

pub type GE1 = G1Point;

impl Curve for Bls12_381_1 {
    type Point = GE1;
    type Scalar = FieldScalar;

    const CURVE_NAME: &'static str = "bls12_381_1";
}

impl ECPoint for G1Point {
    type Scalar = FieldScalar;
    type Underlying = PK;

    type CompressedPointLength = typenum::U48;
    type UncompressedPointLength = typenum::U96;

    fn zero() -> G1Point {
        G1Point {
            purpose: "zero",
            ge: PK::identity(),
        }
    }

    fn is_zero(&self) -> bool {
        self.ge.is_identity().into()
    }

    fn generator() -> &'static G1Point {
        &GENERATOR
    }

    fn base_point2() -> &'static G1Point {
        &BASE_POINT2
    }

    fn from_coords(x: &BigInt, y: &BigInt) -> Result<G1Point, NotOnCurve> {
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

        let g1_affine = bls12_381::G1Affine::from_uncompressed(&uncompressed);
        match Option::from(g1_affine) {
            Some(g1_affine) => {
                Ok(G1Point {
                    purpose: "from_coords",
                    ge: g1_affine,
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
        *GenericArray::from_slice(&uncompressed.as_slice())
    }

    fn deserialize(bytes: &[u8]) -> Result<G1Point, DeserializationError> {
        if bytes.len() == COMPRESSED_SIZE {
            let mut bytes_array_comp = [0u8; COMPRESSED_SIZE];
            bytes_array_comp.copy_from_slice(&bytes[..COMPRESSED_SIZE]);
            let g1_affine = bls12_381::G1Affine::from_compressed(&bytes_array_comp);
            match Option::from(g1_affine) {
                Some(g1_affine) => {
                    Ok(G1Point {
                        purpose: "deserialize",
                        ge: g1_affine,
                    })
                }
                None => { Err(DeserializationError) }
            }
        } else if bytes.len() == 2 * COMPRESSED_SIZE {
            let mut bytes_array_uncomp = [0u8; 2 * COMPRESSED_SIZE];
            bytes_array_uncomp.copy_from_slice(&bytes[..2 * COMPRESSED_SIZE]);
            let g1_affine = bls12_381::G1Affine::from_uncompressed(&bytes_array_uncomp);
            match Option::from(g1_affine) {
                Some(g1_affine) => {
                    Ok(G1Point {
                        purpose: "deserialize",
                        ge: g1_affine,
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

    fn scalar_mul(&self, scalar: &Self::Scalar) -> G1Point {
        let result = self.ge.mul(scalar.underlying_ref());
        G1Point {
            purpose: "scalar_mul",
            ge: result.to_affine(),
        }
    }

    fn add_point(&self, other: &Self) -> G1Point {
        let mut result = G1Projective::from(self.ge);
        result.add_assign(&other.ge);
        G1Point {
            purpose: "add_point",
            ge: result.to_affine(),
        }
    }

    fn sub_point(&self, other: &Self) -> G1Point {
        let mut result = G1Projective::from(self.ge);
        result.sub_assign(&other.ge);
        G1Point {
            purpose: "sub_point",
            ge: result.to_affine(),
        }
    }

    fn neg_point(&self) -> Self {
        let mut result = self.ge;
        result = result.neg();
        G1Point {
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
    fn from_underlying(ge: Self::Underlying) -> G1Point {
        G1Point {
            purpose: "from_underlying",
            ge,
        }
    }
}


impl G1Point {
    fn in_subgroup(&self) -> bool {
        bool::from(self.ge.is_on_curve()) && self.is_in_correct_subgroup_assuming_on_curve()
    }

    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        self.scalar_mul(&FieldScalar::from_bigint(FieldScalar::group_order())).is_zero()
    }

    pub fn hash_to_curve(message: &[u8], dst: &[u8]) -> Self {
        let projective = <G1Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(
            message, dst,
        );
        G1Point {
            purpose: "hash_to_curve",
            ge: projective.to_affine(),
        }
    }
}

impl fmt::Debug for G1Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Point {{ purpose: {:?}, uncompressed: {:?} }}",
            self.purpose,
            hex::encode(self.serialize_uncompressed()),
        )
    }
}

impl PartialEq for G1Point {
    fn eq(&self, other: &G1Point) -> bool {
        self.ge == other.ge
    }
}

impl Zeroize for G1Point {
    fn zeroize(&mut self) {
        self.ge.zeroize()
    }
}


impl Serialize for G1Point {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
    {
        let bytes = self.serialize_compressed();
        let bytes_as_bn = BigInt::from_bytes(&bytes[..]);
        let mut state = serializer.serialize_struct("Bls12381G1Point", 1)?;
        state.serialize_field("bytes_str", &bytes_as_bn.to_hex())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for G1Point {
    fn deserialize<D>(deserializer: D) -> Result<G1Point, D::Error>
        where
            D: Deserializer<'de>,
    {
        const FIELDS: &[&str] = &["bytes_str"];
        deserializer.deserialize_struct("Bls12381G1Point", FIELDS, Bls12381G1PointVisitor)
    }
}

struct Bls12381G1PointVisitor;

impl<'de> Visitor<'de> for Bls12381G1PointVisitor {
    type Value = G1Point;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("Bls12381G1Point")
    }

    fn visit_seq<V>(self, mut seq: V) -> Result<G1Point, V::Error>
        where
            V: SeqAccess<'de>,
    {
        let bytes_str = seq
            .next_element()?
            .ok_or_else(|| V::Error::invalid_length(0, &"a single element"))?;
        let bytes_bn = BigInt::from_hex(bytes_str).map_err(V::Error::custom)?;
        let bytes = BigInt::to_bytes(&bytes_bn);
        <G1Point as ECPoint>::deserialize(&bytes[..]).map_err(|_| V::Error::custom("failed to parse g1 point"))
    }

    fn visit_map<E: MapAccess<'de>>(self, mut map: E) -> Result<G1Point, E::Error> {
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

        <G1Point as ECPoint>::deserialize(&bytes[..]).map_err(|_| E::Error::custom("failed to parse g1 point"))
    }
}

#[test]
fn test_serde() {
    use serde::{Serialize, Deserialize};
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Wrapper {
        inner: G1Point,
    }
    let wrapper = Wrapper {
        inner: G1Point {
            purpose: "example",
            ge: PK::generator(),
        }
    };
    let json_str = serde_json::to_string(&wrapper);
    assert!(json_str.is_ok());
    let deserialized = serde_json::from_slice::<Wrapper>(json_str.unwrap().as_bytes());
    assert_eq!(wrapper.inner.ge, deserialized.unwrap().inner.ge);
}

#[cfg(test)]
mod tests {
    use bls12_381::G1Projective;
    use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
    use curv::arithmetic::{Converter, Modulo};
    use curv::BigInt;
    use curv::elliptic::curves::ECScalar;
    use pairing::group::Curve;

    use crate::g1::{G1Point, GE1};
    use crate::scalar::FieldScalar;

    use super::ECPoint;

    #[test]
    fn test_serdes_pk() {
        let pk = *GE1::generator();
        let s = serde_json::to_string(&pk).expect("Failed in serialization");
        let des_pk: GE1 = serde_json::from_str(&s).expect("Failed in deserialization");
        assert_eq!(des_pk, pk);

        let pk = *GE1::base_point2();
        let s = serde_json::to_string(&pk).expect("Failed in serialization");
        let des_pk: GE1 = serde_json::from_str(&s).expect("Failed in deserialization");
        assert_eq!(des_pk, pk);
    }

    #[test]
    fn bincode_pk() {
        let pk = *GE1::generator();
        let bin = bincode::serialize(&pk).unwrap();
        let decoded: G1Point = bincode::deserialize(bin.as_slice()).unwrap();
        assert_eq!(decoded, pk);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::op_ref)] // Enables type inference.
    fn test_serdes_bad_pk() {
        let pk = *GE1::generator();
        let s = serde_json::to_string(&pk).expect("Failed in serialization");
        // we make sure that the string encodes invalid point:
        let s: String = s.replace("30", "20");
        let des_pk: GE1 = serde_json::from_str(&s).expect("Failed in deserialization");
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
        let base: GE1 = *ECPoint::generator();

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
        let base: GE1 = *ECPoint::generator();
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
        let a_mul_b_fe = a.mul(&b); // a*b
        let base: GE1 = *ECPoint::generator();
        let point_ab1 = base.scalar_mul(&a_mul_b_fe); // G * (a*b)
        let point_a = base.scalar_mul(&a); // G * a
        let point_ab2 = point_a.scalar_mul(&b); // G * a * b

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
        let g: GE1 = *ECPoint::generator();

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
        let projective = <G1Projective as HashToCurve<ExpandMsgXmd<sha2::Sha256>>>::hash_to_curve(msg, cs);
        let point = G1Point {
            purpose: "test",
            ge: projective.to_affine(),
        };

        assert!(point.in_subgroup());

        // Check that ECPoint::base_point2() returns generated point
        let base_point2 = G1Point::base_point2();

        assert!(base_point2.in_subgroup());
        assert_eq!(projective.to_affine(), base_point2.ge);
    }
}
