use std::fmt;
use std::ops::{AddAssign, MulAssign, SubAssign};

use curv::arithmetic::Converter;
use curv::arithmetic::Modulo;
use curv::arithmetic::Zero;
use curv::BigInt;
use curv::elliptic::curves::{DeserializationError, ECScalar};
use generic_array::GenericArray;
use pairing::group::ff::{Field, PrimeField};
use rand::rngs::OsRng;

lazy_static::lazy_static! {
    static ref GROUP_ORDER: BigInt = {
        let q_u64: [u64; 4] = [
            0xffffffff00000001,
            0x53bda402fffe5bfe,
            0x3339d80809a1d805,
            0x73eda753299d7d48,
        ];
        let to_bn = q_u64.iter().rev().fold(BigInt::zero(), |acc, x| {
            let element_bn = BigInt::from(*x);
            element_bn + (acc << 64)
        });
        to_bn
    };
}

const SECRET_KEY_SIZE: usize = 32;

pub type FE = FieldScalar;
pub type SK = bls12_381::Scalar;

#[derive(Clone)]
pub struct FieldScalar {
    purpose: &'static str,
    fe: SK,
}

impl ECScalar for FieldScalar {
    type Underlying = SK;

    type ScalarLength = typenum::U32;

    fn random() -> FieldScalar {
        let sk = bls12_381::Scalar::random(&mut OsRng);
        FieldScalar {
            purpose: "random",
            fe: sk,
        }
    }

    fn zero() -> FieldScalar {
        FieldScalar {
            purpose: "zero",
            fe: SK::zero(),
        }
    }

    fn from_bigint(n: &BigInt) -> FieldScalar {
        let bytes = n
            .modulus(Self::group_order())
            .to_bytes_array::<SECRET_KEY_SIZE>()
            .expect("n mod curve_order must be equal or less than 32 bytes");

        let sk = SK::from_repr(bytes).unwrap();
        FieldScalar {
            purpose: "from_bigint",
            fe: sk,
        }
    }

    fn to_bigint(&self) -> BigInt {
        let repr = self.fe.to_repr();
        let mut be_bytes = [0u8; SECRET_KEY_SIZE];
        be_bytes.copy_from_slice(repr.as_slice());
        be_bytes.reverse();
        BigInt::from_bytes(&be_bytes)
    }

    fn serialize(&self) -> GenericArray<u8, Self::ScalarLength> {
        let repr = self.fe.to_repr();
        *GenericArray::from_slice(repr.as_slice())
    }

    fn deserialize(bytes: &[u8]) -> Result<Self, DeserializationError> {
        if bytes.len() != SECRET_KEY_SIZE {
            return Err(DeserializationError);
        }

        let mut bytes_array_sk = [0u8; SECRET_KEY_SIZE];
        bytes_array_sk.copy_from_slice(&bytes[..SECRET_KEY_SIZE]);

        let sk = SK::from_repr(bytes_array_sk).unwrap();

        Ok(FieldScalar {
            purpose: "deserialize",
            fe: sk.into(),
        })
    }

    fn add(&self, other: &Self) -> FieldScalar {
        let mut result = self.fe.clone();
        result.add_assign(&other.fe);
        FieldScalar {
            purpose: "add",
            fe: result,
        }
    }

    fn mul(&self, other: &Self) -> FieldScalar {
        let mut result = self.fe.clone();
        result.mul_assign(&other.fe);
        FieldScalar {
            purpose: "mul",
            fe: result,
        }
    }

    fn sub(&self, other: &Self) -> FieldScalar {
        let mut result = self.fe.clone();
        result.sub_assign(&other.fe);
        FieldScalar {
            purpose: "sub",
            fe: result,
        }
    }

    fn neg(&self) -> FieldScalar {
        let mut result = self.fe.clone();
        result = result.neg();
        FieldScalar {
            purpose: "neg",
            fe: result.into(),
        }
    }

    fn invert(&self) -> Option<FieldScalar> {
        Some(FieldScalar {
            purpose: "invert",
            fe: self.fe.invert().unwrap(),
        })
    }

    fn add_assign(&mut self, other: &Self) {
        self.fe.add_assign(&other.fe);
    }
    fn mul_assign(&mut self, other: &Self) {
        self.fe.mul_assign(&other.fe);
    }
    fn sub_assign(&mut self, other: &Self) {
        self.fe.sub_assign(&other.fe);
    }
    fn neg_assign(&mut self) {
        self.fe.neg();
    }

    fn group_order() -> &'static BigInt {
        &GROUP_ORDER
    }

    fn underlying_ref(&self) -> &Self::Underlying {
        &self.fe
    }
    fn underlying_mut(&mut self) -> &mut Self::Underlying {
        &mut self.fe
    }
    fn from_underlying(fe: Self::Underlying) -> FieldScalar {
        FieldScalar {
            purpose: "from_underlying",
            fe: fe.into(),
        }
    }
}

impl fmt::Debug for FieldScalar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Point {{ purpose: {:?}, bytes: {:?} }}",
            self.purpose, self.fe,
        )
    }
}

impl PartialEq for FieldScalar {
    fn eq(&self, other: &FieldScalar) -> bool {
        self.fe == other.fe
    }
}
