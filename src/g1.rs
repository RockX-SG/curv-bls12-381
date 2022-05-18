use std::fmt;
use std::ops::{AddAssign, Mul, Neg, SubAssign};

use bls12_381::G1Projective;
use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
use curv::arithmetic::traits::*;
use curv::BigInt;
use curv::elliptic::curves::{Curve, DeserializationError, ECPoint, ECScalar, NotOnCurve, PointCoords};
use generic_array::GenericArray;
use pairing::group::Curve as pCurve;
use zeroize::Zeroize;

use serde::de::{Error, MapAccess, SeqAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::ser::{Serialize, Serializer};
use serde::{Deserialize, Deserializer};

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
            172, 183, 57, 170, 180, 39, 32, 173, 29, 238, 62, 13, 166, 109, 90, 181, 17, 76, 247,
            26, 155, 130, 211, 18, 42, 235, 137, 225, 184, 210, 140, 54, 83, 233, 228, 226, 70,
            194, 50, 55, 116, 229, 2, 115, 227, 223, 31, 165, 39, 191, 209, 49, 127, 106, 196, 123,
            71, 70, 243,
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
        bool::from(self.ge.is_on_curve()) && bool::from(self.ge.is_torsion_free())// TODO: Check this
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


#[cfg(test)]
mod tests {
    /*
    use pairing_plus::bls12_381::{G1Uncompressed, G1};
    use pairing_plus::hash_to_curve::HashToCurve;
    use pairing_plus::hash_to_field::ExpandMsgXmd;
    use pairing_plus::{CurveProjective, SubgroupCheck};

    use super::{ECPoint, GE1};

    #[test]
    fn base_point2_nothing_up_my_sleeve() {
        // Generate base_point2
        let cs = &[1u8];
        let msg = &[1u8];
        let point = <G1 as HashToCurve<ExpandMsgXmd<old_sha2::Sha256>>>::hash_to_curve(msg, cs)
            .into_affine();
        assert!(point.in_subgroup());

        // Print in uncompressed form
        use pairing_plus::EncodedPoint;
        let point_uncompressed = G1Uncompressed::from_affine(point);
        println!("Uncompressed base_point2: {:?}", point_uncompressed);

        // Check that ECPoint::base_point2() returns generated point
        let base_point2: &GE1 = ECPoint::base_point2();
        assert_eq!(point, base_point2.ge);
    }*/
}
