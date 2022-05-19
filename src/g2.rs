use std::fmt;
use std::ops::{AddAssign, Mul, Neg, SubAssign};

use bls12_381::G2Projective;
use bls12_381::hash_to_curve::{ExpandMsgXmd, HashToCurve};
use curv::arithmetic::traits::*;
use curv::BigInt;
use curv::elliptic::curves::{Curve, DeserializationError, ECPoint, ECScalar, NotOnCurve, PointCoords};
use generic_array::GenericArray;
use pairing::group::Curve as GroupCurve;
use zeroize::Zeroize;

use serde::de::{Error, MapAccess, SeqAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::ser::{Serialize, Serializer};
use serde::{Deserialize, Deserializer};

use super::scalar::FieldScalar;

lazy_static::lazy_static! {
    static ref GENERATOR: G2Point = G2Point {
        purpose: "generator",
        ge: PK::generator(),
    };

    static ref BASE_POINT2: G2Point = {
        const BASE_POINT2: [u8; 192] = [
            0, 204, 165, 72, 21, 96, 36, 119, 117, 242, 58, 55, 105, 140, 136, 76, 180, 140, 92,
            212, 55, 3, 146, 72, 120, 181, 37, 205, 165, 221, 144, 86, 57, 124, 16, 19, 160, 215,
            21, 251, 236, 99, 91, 147, 237, 113, 223, 70, 14, 223, 81, 150, 157, 235, 107, 225,
            151, 227, 119, 53, 195, 46, 25, 54, 57, 158, 156, 122, 75, 152, 119, 51, 137, 131, 43,
            34, 68, 24, 24, 210, 18, 75, 36, 20, 232, 76, 38, 84, 44, 112, 213, 217, 192, 122, 177,
            186, 5, 113, 25, 229, 205, 55, 65, 191, 147, 1, 212, 194, 151, 141, 43, 223, 68, 185,
            183, 66, 163, 62, 96, 92, 36, 209, 216, 40, 16, 132, 231, 104, 179, 248, 189, 53, 154,
            106, 83, 159, 5, 54, 86, 87, 45, 68, 52, 247, 3, 90, 148, 187, 234, 213, 114, 244, 52,
            137, 201, 13, 165, 57, 217, 190, 150, 103, 223, 193, 129, 198, 47, 86, 122, 196, 22,
            200, 123, 89, 178, 216, 11, 238, 155, 106, 172, 125, 164, 95, 2, 136, 132, 137, 27,
            184, 237, 169,
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
        bool::from(self.ge.is_on_curve()) && bool::from(self.ge.is_torsion_free())// TODO: Check this
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

#[test]
fn test_serde(){
    use serde::{Serialize, Deserialize};
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Wrapper {
        inner: G2Point
    }
    let wrapper = Wrapper{
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