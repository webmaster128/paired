use std::fmt;

use fff::{BitIterator, Field, PrimeField, PrimeFieldRepr, SqrtField};
use groupy::{CurveAffine, CurveProjective, EncodedPoint, GroupDecodingError};
use lazy_static::lazy_static;
use rand_core::RngCore;

use super::super::{Bls12, Fq, Fq12, Fq2, FqRepr, Fr, FrRepr, IsogenyMap, OsswuMap};
use super::chain::chain_p2m9div16;
use super::g1::G1Affine;
use super::util::osswu_helper;
use crate::{Engine, PairingCurveAffine, Signum0};

curve_impl!(
    "G2",
    G2,
    G2Affine,
    G2Prepared,
    Fq2,
    Fr,
    G2Uncompressed,
    G2Compressed,
    G1Affine,
    4,
    3
);

#[derive(Copy, Clone)]
pub struct G2Uncompressed([u8; 192]);

encoded_point_delegations!(G2Uncompressed);

impl fmt::Debug for G2Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl EncodedPoint for G2Uncompressed {
    type Affine = G2Affine;

    fn empty() -> Self {
        G2Uncompressed([0; 192])
    }
    fn size() -> usize {
        192
    }
    fn into_affine(&self) -> Result<G2Affine, GroupDecodingError> {
        let affine = self.into_affine_unchecked()?;

        if !affine.is_on_curve() {
            Err(GroupDecodingError::NotOnCurve)
        } else if !affine.is_in_correct_subgroup_assuming_on_curve() {
            Err(GroupDecodingError::NotInSubgroup)
        } else {
            Ok(affine)
        }
    }
    fn into_affine_unchecked(&self) -> Result<G2Affine, GroupDecodingError> {
        // Create a copy of this representation.
        let mut copy = self.0;

        if copy[0] & (1 << 7) != 0 {
            // Distinguisher bit is set, but this should be uncompressed!
            return Err(GroupDecodingError::UnexpectedCompressionMode);
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G2Affine::zero())
            } else {
                Err(GroupDecodingError::UnexpectedInformation)
            }
        } else {
            if copy[0] & (1 << 5) != 0 {
                // The bit indicating the y-coordinate should be lexicographically
                // largest is set, but this is an uncompressed element.
                return Err(GroupDecodingError::UnexpectedInformation);
            }

            // Unset the three most significant bits.
            copy[0] &= 0x1f;

            let mut x_c0 = FqRepr([0; 6]);
            let mut x_c1 = FqRepr([0; 6]);
            let mut y_c0 = FqRepr([0; 6]);
            let mut y_c1 = FqRepr([0; 6]);

            {
                let mut reader = &copy[..];

                x_c1.read_be(&mut reader).unwrap();
                x_c0.read_be(&mut reader).unwrap();
                y_c1.read_be(&mut reader).unwrap();
                y_c0.read_be(&mut reader).unwrap();
            }

            Ok(G2Affine {
                x: Fq2 {
                    c0: Fq::from_repr(x_c0).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("x coordinate (c0)", e)
                    })?,
                    c1: Fq::from_repr(x_c1).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("x coordinate (c1)", e)
                    })?,
                },
                y: Fq2 {
                    c0: Fq::from_repr(y_c0).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("y coordinate (c0)", e)
                    })?,
                    c1: Fq::from_repr(y_c1).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("y coordinate (c1)", e)
                    })?,
                },
                infinity: false,
            })
        }
    }
    fn from_affine(affine: G2Affine) -> Self {
        let mut res = Self::empty();

        if affine.is_zero() {
            // Set the second-most significant bit to indicate this point
            // is at infinity.
            res.0[0] |= 1 << 6;
        } else {
            let mut writer = &mut res.0[..];

            affine.x.c1.into_repr().write_be(&mut writer).unwrap();
            affine.x.c0.into_repr().write_be(&mut writer).unwrap();
            affine.y.c1.into_repr().write_be(&mut writer).unwrap();
            affine.y.c0.into_repr().write_be(&mut writer).unwrap();
        }

        res
    }
}

#[derive(Copy, Clone)]
pub struct G2Compressed([u8; 96]);

encoded_point_delegations!(G2Compressed);

impl fmt::Debug for G2Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl EncodedPoint for G2Compressed {
    type Affine = G2Affine;

    fn empty() -> Self {
        G2Compressed([0; 96])
    }
    fn size() -> usize {
        96
    }
    fn into_affine(&self) -> Result<G2Affine, GroupDecodingError> {
        let affine = self.into_affine_unchecked()?;

        // NB: Decompression guarantees that it is on the curve already.

        if !affine.is_in_correct_subgroup_assuming_on_curve() {
            Err(GroupDecodingError::NotInSubgroup)
        } else {
            Ok(affine)
        }
    }
    fn into_affine_unchecked(&self) -> Result<G2Affine, GroupDecodingError> {
        // Create a copy of this representation.
        let mut copy = self.0;

        if copy[0] & (1 << 7) == 0 {
            // Distinguisher bit isn't set.
            return Err(GroupDecodingError::UnexpectedCompressionMode);
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G2Affine::zero())
            } else {
                Err(GroupDecodingError::UnexpectedInformation)
            }
        } else {
            // Determine if the intended y coordinate must be greater
            // lexicographically.
            let greatest = copy[0] & (1 << 5) != 0;

            // Unset the three most significant bits.
            copy[0] &= 0x1f;

            let mut x_c1 = FqRepr([0; 6]);
            let mut x_c0 = FqRepr([0; 6]);

            {
                let mut reader = &copy[..];

                x_c1.read_be(&mut reader).unwrap();
                x_c0.read_be(&mut reader).unwrap();
            }

            // Interpret as Fq element.
            let x = Fq2 {
                c0: Fq::from_repr(x_c0).map_err(|e| {
                    GroupDecodingError::CoordinateDecodingError("x coordinate (c0)", e)
                })?,
                c1: Fq::from_repr(x_c1).map_err(|e| {
                    GroupDecodingError::CoordinateDecodingError("x coordinate (c1)", e)
                })?,
            };

            G2Affine::get_point_from_x(x, greatest).ok_or(GroupDecodingError::NotOnCurve)
        }
    }
    fn from_affine(affine: G2Affine) -> Self {
        let mut res = Self::empty();

        if affine.is_zero() {
            // Set the second-most significant bit to indicate this point
            // is at infinity.
            res.0[0] |= 1 << 6;
        } else {
            {
                let mut writer = &mut res.0[..];

                affine.x.c1.into_repr().write_be(&mut writer).unwrap();
                affine.x.c0.into_repr().write_be(&mut writer).unwrap();
            }

            let mut negy = affine.y;
            negy.negate();

            // Set the third most significant bit if the correct y-coordinate
            // is lexicographically largest.
            if affine.y > negy {
                res.0[0] |= 1 << 5;
            }
        }

        // Set highest bit to distinguish this as a compressed element.
        res.0[0] |= 1 << 7;

        res
    }
}

impl G2Affine {
    fn get_generator() -> Self {
        G2Affine {
            x: Fq2 {
                c0: super::super::fq::G2_GENERATOR_X_C0,
                c1: super::super::fq::G2_GENERATOR_X_C1,
            },
            y: Fq2 {
                c0: super::super::fq::G2_GENERATOR_Y_C0,
                c1: super::super::fq::G2_GENERATOR_Y_C1,
            },
            infinity: false,
        }
    }

    fn get_coeff_b() -> Fq2 {
        Fq2 {
            c0: super::super::fq::B_COEFF,
            c1: super::super::fq::B_COEFF,
        }
    }

    fn scale_by_cofactor(&self) -> G2 {
        // G2 cofactor = (x^8 - 4 x^7 + 5 x^6) - (4 x^4 + 6 x^3 - 4 x^2 - 4 x + 13) // 9
        // 0x5d543a95414e7f1091d50792876a202cd91de4547085abaa68a205b2e5a7ddfa628f1cb4d9e82ef21537e293a6691ae1616ec6e786f0c70cf1c38e31c7238e5
        let cofactor = BitIterator::new([
            0xcf1c38e31c7238e5,
            0x1616ec6e786f0c70,
            0x21537e293a6691ae,
            0xa628f1cb4d9e82ef,
            0xa68a205b2e5a7ddf,
            0xcd91de4547085aba,
            0x91d50792876a202,
            0x5d543a95414e7f1,
        ]);
        self.mul_bits(cofactor)
    }

    fn perform_pairing(&self, other: &G1Affine) -> Fq12 {
        super::super::Bls12::pairing(*other, *self)
    }
}

impl G2 {
    fn empirical_recommended_wnaf_for_scalar(scalar: FrRepr) -> usize {
        let num_bits = scalar.num_bits() as usize;

        if num_bits >= 103 {
            4
        } else if num_bits >= 37 {
            3
        } else {
            2
        }
    }

    fn empirical_recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 11] = [1, 3, 8, 20, 47, 126, 260, 826, 1501, 4555, 84071];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

#[derive(Clone, Debug)]
pub struct G2Prepared {
    pub(crate) coeffs: Vec<(Fq2, Fq2, Fq2)>,
    pub(crate) infinity: bool,
}

lazy_static! {
    /// Coefficients of the 3-isogeny x map's numerator
    static ref XNUM: [Fq2; 4] = unsafe {[
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x47f671c71ce05e62,
                0x06dd57071206393e,
                0x7c80cd2af3fd71a2,
                0x048103ea9e6cd062,
                0xc54516acc8d037f6,
                0x13808f550920ea41,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x47f671c71ce05e62,
                0x06dd57071206393e,
                0x7c80cd2af3fd71a2,
                0x048103ea9e6cd062,
                0xc54516acc8d037f6,
                0x13808f550920ea41,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x5fe55555554c71d0,
                0x873fffdd236aaaa3,
                0x6a6b4619b26ef918,
                0x21c2888408874945,
                0x2836cda7028cabc5,
                0x0ac73310a7fd5abd,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x0a0c5555555971c3,
                0xdb0c00101f9eaaae,
                0xb1fb2f941d797997,
                0xd3960742ef416e1c,
                0xb70040e2c20556f4,
                0x149d7861e581393b,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0xaff2aaaaaaa638e8,
                0x439fffee91b55551,
                0xb535a30cd9377c8c,
                0x90e144420443a4a2,
                0x941b66d3814655e2,
                0x0563998853fead5e,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x40aac71c71c725ed,
                0x190955557a84e38e,
                0xd817050a8f41abc3,
                0xd86485d4c87f6fb1,
                0x696eb479f885d059,
                0x198e1a74328002d2,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
        },
    ]};

    /// Coefficients of the 3-isogeny x map's denominator
    static ref XDEN: [Fq2; 3] = unsafe {[
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x1f3affffff13ab97,
                0xf25bfc611da3ff3e,
                0xca3757cb3819b208,
                0x3e6427366f8cec18,
                0x03977bc86095b089,
                0x04f69db13f39a952,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x447600000027552e,
                0xdcb8009a43480020,
                0x6f7ee9ce4a6e8b59,
                0xb10330b7c0a95bc6,
                0x6140b1fcfb1e54b7,
                0x0381be097f0bb4e1,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x7588ffffffd8557d,
                0x41f3ff646e0bffdf,
                0xf7b1e8d2ac426aca,
                0xb3741acd32dbb6f8,
                0xe9daf5b9482d581f,
                0x167f53e0ba7431b8,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
        },
    ]};

    /// Coefficients of the 3-isogeny y map's numerator
    static ref YNUM: [Fq2; 4] = unsafe {[
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x96d8f684bdfc77be,
                0xb530e4f43b66d0e2,
                0x184a88ff379652fd,
                0x57cb23ecfae804e1,
                0x0fd2e39eada3eba9,
                0x08c8055e31c5d5c3,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x96d8f684bdfc77be,
                0xb530e4f43b66d0e2,
                0x184a88ff379652fd,
                0x57cb23ecfae804e1,
                0x0fd2e39eada3eba9,
                0x08c8055e31c5d5c3,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0xbf0a71c71c91b406,
                0x4d6d55d28b7638fd,
                0x9d82f98e5f205aee,
                0xa27aa27b1d1a18d5,
                0x02c3b2b2d2938e86,
                0x0c7d13420b09807f,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0xd7f9555555531c74,
                0x21cffff748daaaa8,
                0x5a9ad1866c9bbe46,
                0x4870a2210221d251,
                0x4a0db369c0a32af1,
                0x02b1ccc429ff56af,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0xe205aaaaaaac8e37,
                0xfcdc000768795556,
                0x0c96011a8a1537dd,
                0x1c06a963f163406e,
                0x010df44c82a881e6,
                0x174f45260f808feb,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0xa470bda12f67f35c,
                0xc0fe38e23327b425,
                0xc9d3d0f2c6f0678d,
                0x1c55c9935b5a982e,
                0x27f6c0e2f0746764,
                0x117c5e6e28aa9054,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
        },
    ]};

    /// Coefficients of the 3-isogeny y map's denominator
    static ref YDEN: [Fq2; 4] = unsafe {[
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x0162fffffa765adf,
                0x8f7bea480083fb75,
                0x561b3c2259e93611,
                0x11e19fc1a9c875d5,
                0xca713efc00367660,
                0x03c6a03d41da1151,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x0162fffffa765adf,
                0x8f7bea480083fb75,
                0x561b3c2259e93611,
                0x11e19fc1a9c875d5,
                0xca713efc00367660,
                0x03c6a03d41da1151,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x5db0fffffd3b02c5,
                0xd713f52358ebfdba,
                0x5ea60761a84d161a,
                0xbb2c75a34ea6c44a,
                0x0ac6735921c1119b,
                0x0ee3d913bdacfbf6,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x66b10000003affc5,
                0xcb1400e764ec0030,
                0xa73e5eb56fa5d106,
                0x8984c913a0fe09a9,
                0x11e10afb78ad7f13,
                0x05429d0e3e918f52,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x534dffffffc4aae6,
                0x5397ff174c67ffcf,
                0xbff273eb870b251d,
                0xdaf2827152870915,
                0x393a9cbaca9e2dc3,
                0x14be74dbfaee5748,
            ])),
        },
        Fq2 {
            c0: Fq::from_repr_raw(FqRepr([
                0x760900000002fffd,
                0xebf4000bc40c0002,
                0x5f48985753c758ba,
                0x77ce585370525745,
                0x5c071a97a256ec6d,
                0x15f65ec3fa80e493,
            ])),
            c1: Fq::from_repr_raw(FqRepr([
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
                0x0000000000000000,
            ])),
        },
    ]};

    static ref ELLP_A: Fq2 = Fq2 {
        c0: unsafe { Fq::from_repr_raw(FqRepr([
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
        ])) },
        c1: unsafe { Fq::from_repr_raw(FqRepr([
            0xe53a000003135242u64,
            0x01080c0fdef80285u64,
            0xe7889edbe340f6bdu64,
            0x0b51375126310601u64,
            0x02d6985717c744abu64,
            0x1220b4e979ea5467u64,
        ])) },
    };

    static ref ELLP_B: Fq2 = Fq2 {
        c0: unsafe { Fq::from_repr_raw(FqRepr([
            0x22ea00000cf89db2u64,
            0x6ec832df71380aa4u64,
            0x6e1b94403db5a66eu64,
            0x75bf3c53a79473bau64,
            0x3dd3a569412c0a34u64,
            0x125cdb5e74dc4fd1u64,
        ])) },
        c1: unsafe { Fq::from_repr_raw(FqRepr([
            0x22ea00000cf89db2u64,
            0x6ec832df71380aa4u64,
            0x6e1b94403db5a66eu64,
            0x75bf3c53a79473bau64,
            0x3dd3a569412c0a34u64,
            0x125cdb5e74dc4fd1u64,
        ])) },
    };

    static ref XI: Fq2 = Fq2 {
        c0: unsafe { Fq::from_repr_raw(FqRepr([
            0x87ebfffffff9555cu64,
            0x656fffe5da8ffffau64,
            0xfd0749345d33ad2u64,
            0xd951e663066576f4u64,
            0xde291a3d41e980d3u64,
            0x815664c7dfe040du64,
        ])) },
        c1: unsafe { Fq::from_repr_raw(FqRepr([
            0x43f5fffffffcaaaeu64,
            0x32b7fff2ed47fffdu64,
            0x7e83a49a2e99d69u64,
            0xeca8f3318332bb7au64,
            0xef148d1ea0f4c069u64,
            0x40ab3263eff0206u64,
        ])) },
    };

    static ref ETAS: [Fq2; 4] = [
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x5e514668ac736d2u64,
                0x9089b4d6b84f3ea5u64,
                0x603c384c224a8b32u64,
                0xf3257909536afea6u64,
                0x5c5cdbabae656d81u64,
                0x75bfa0863c987e9u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x338d9bfe08087330u64,
                0x7b8e48b2bd83cefeu64,
                0x530dad5d306b5be7u64,
                0x5a4d7e8e6c408b6du64,
                0x6258f7a6232cab9bu64,
                0xb985811cce14db5u64,
            ])) },
        },
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x86716401f7f7377bu64,
                0xa31db74bf3d03101u64,
                0x14232543c6459a3cu64,
                0xa29ccf687448752u64,
                0xe8c2b010201f013cu64,
                0xe68b9d86c9e98e4u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x5e514668ac736d2u64,
                0x9089b4d6b84f3ea5u64,
                0x603c384c224a8b32u64,
                0xf3257909536afea6u64,
                0x5c5cdbabae656d81u64,
                0x75bfa0863c987e9u64,
            ])) },
        },
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x718fdad24ee1d90fu64,
                0xa58c025bed8276afu64,
                0xc3a10230ab7976fu64,
                0xf0c54df5c8f275e1u64,
                0x4ec2478c28baf465u64,
                0x1129373a90c508e6u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x19af5f980a3680cu64,
                0x4ed7da0e66063afau64,
                0x600354723b5d9972u64,
                0x8b2f958b20d09d72u64,
                0x474938f02d461dbu64,
                0xdcf8b9e0684ab1cu64,
            ])) },
        },
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0xb8640a067f5c429fu64,
                0xcfd425f04b4dc505u64,
                0x72d7e2ebb535cb1u64,
                0xd947b5f9d2b4754du64,
                0x46a7142740774afbu64,
                0xc31864c32fb3b7eu64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x718fdad24ee1d90fu64,
                0xa58c025bed8276afu64,
                0xc3a10230ab7976fu64,
                0xf0c54df5c8f275e1u64,
                0x4ec2478c28baf465u64,
                0x1129373a90c508e6u64,
            ])) },
        },
    ];

    static ref ROOTS_OF_UNITY: [Fq2; 4] = [
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x760900000002fffdu64,
                0xebf4000bc40c0002u64,
                0x5f48985753c758bau64,
                0x77ce585370525745u64,
                0x5c071a97a256ec6du64,
                0x15f65ec3fa80e493u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
            ])) },
        },
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
                0x0000000000000000u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x760900000002fffdu64,
                0xebf4000bc40c0002u64,
                0x5f48985753c758bau64,
                0x77ce585370525745u64,
                0x5c071a97a256ec6du64,
                0x15f65ec3fa80e493u64,
            ])) },
        },
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x7bcfa7a25aa30fdau64,
                0xdc17dec12a927e7cu64,
                0x2f088dd86b4ebef1u64,
                0xd1ca2087da74d4a7u64,
                0x2da2596696cebc1du64,
                0x0e2b7eedbbfd87d2u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x7bcfa7a25aa30fdau64,
                0xdc17dec12a927e7cu64,
                0x2f088dd86b4ebef1u64,
                0xd1ca2087da74d4a7u64,
                0x2da2596696cebc1du64,
                0x0e2b7eedbbfd87d2u64,
            ])) },
        },
        Fq2 {
            c0: unsafe { Fq::from_repr_raw(FqRepr([
                0x7bcfa7a25aa30fdau64,
                0xdc17dec12a927e7cu64,
                0x2f088dd86b4ebef1u64,
                0xd1ca2087da74d4a7u64,
                0x2da2596696cebc1du64,
                0x0e2b7eedbbfd87d2u64,
            ])) },
            c1: unsafe { Fq::from_repr_raw(FqRepr([
                0x3e2f585da55c9ad1u64,
                0x4294213d86c18183u64,
                0x382844c88b623732u64,
                0x92ad2afd19103e18u64,
                0x1d794e4fac7cf0b9u64,
                0x0bd592fc7d825ec8u64,
            ])) },
        },
    ];
}

impl IsogenyMap for G2 {
    fn isogeny_map(&mut self) {
        self.eval_iso([&XNUM[..], &XDEN[..], &YNUM[..], &YDEN[..]]);
    }
}

impl OsswuMap for G2 {
    fn osswu_map(u: &Fq2) -> G2 {
        // compute x0 and g(x0)
        let [usq, xi_usq, xi2_u4, x0_num, x0_den, gx0_num, gx0_den] =
            osswu_helper(u, &XI, &ELLP_A, &ELLP_B);

        // compute g(x0(u)) ^ ((p - 9) // 16)
        let sqrt_candidate = {
            let mut tmp1 = gx0_den; // v
            tmp1.square(); // v^2
            let mut tmp2 = tmp1;
            tmp1.square(); // v^4
            tmp2.mul_assign(&tmp1); // v^6
            tmp2.mul_assign(&gx0_den); // v^7
            tmp2.mul_assign(&gx0_num); // u v^7
            tmp1.square(); // v^8
            tmp1.mul_assign(&tmp2); // u v^15
            let tmp3 = tmp1;
            chain_p2m9div16(&mut tmp1, &tmp3); // (u v^15) ^ ((p - 9) // 16)
            tmp1.mul_assign(&tmp2); // u v^7 (u v^15) ^ ((p - 9) // 16)
            tmp1
        };

        for root in &ROOTS_OF_UNITY[..] {
            let mut y0 = *root;
            y0.mul_assign(&sqrt_candidate);

            let mut tmp = y0;
            tmp.square();
            tmp.mul_assign(&gx0_den);
            if tmp == gx0_num {
                let sgn0_y_xor_u = y0.sgn0() ^ u.sgn0();
                y0.negate_if(sgn0_y_xor_u);
                y0.mul_assign(&gx0_den); // y * x0_den^3 / x0_den^3 = y

                tmp = x0_num;
                tmp.mul_assign(&x0_den); // x0_num * x0_den / x0_den^2 = x0_num / x0_den

                return G2 {
                    x: tmp,
                    y: y0,
                    z: x0_den,
                };
            }
        }

        // If we've gotten here, g(X0(u)) is not square. Use X1 instead.
        let x1_num = {
            let mut tmp = x0_num;
            tmp.mul_assign(&xi_usq);
            tmp
        };
        let gx1_num = {
            let mut tmp = xi2_u4;
            tmp.mul_assign(&xi_usq); // xi^3 u^6
            tmp.mul_assign(&gx0_num);
            tmp
        };
        let sqrt_candidate = {
            let mut tmp = sqrt_candidate;
            tmp.mul_assign(&usq);
            tmp.mul_assign(u);
            tmp
        };
        for eta in &ETAS[..] {
            let mut y1 = *eta;
            y1.mul_assign(&sqrt_candidate);

            let mut tmp = y1;
            tmp.square();
            tmp.mul_assign(&gx0_den);
            if tmp == gx1_num {
                let sgn0_y_xor_u = y1.sgn0() ^ u.sgn0();
                y1.negate_if(sgn0_y_xor_u);
                y1.mul_assign(&gx0_den); // y * x0_den^3 / x0_den^3 = y

                tmp = x1_num;
                tmp.mul_assign(&x0_den); // x1_num * x0_den / x0_den^2 = x1_num / x0_den

                return G2 {
                    x: tmp,
                    y: y1,
                    z: x0_den,
                };
            }
        }

        panic!("Failed to find square root in G2 osswu_map");
    }
}

#[cfg(test)]
mod tests {
    use super::super::util::check_g_prime;
    use super::*;

    #[test]
    fn g2_generator() {
        use crate::SqrtField;

        let mut x = Fq2::zero();
        let mut i = 0;
        loop {
            // y^2 = x^3 + b
            let mut rhs = x;
            rhs.square();
            rhs.mul_assign(&x);
            rhs.add_assign(&G2Affine::get_coeff_b());

            if let Some(y) = rhs.sqrt() {
                let mut negy = y;
                negy.negate();

                let p = G2Affine {
                    x,
                    y: if y < negy { y } else { negy },
                    infinity: false,
                };

                assert!(!p.is_in_correct_subgroup_assuming_on_curve());

                let g2 = p.scale_by_cofactor();
                if !g2.is_zero() {
                    assert_eq!(i, 2);
                    let g2 = G2Affine::from(g2);

                    assert!(g2.is_in_correct_subgroup_assuming_on_curve());
                    assert_eq!(g2, G2Affine::one());
                    break;
                }
            }

            i += 1;
            x.add_assign(&Fq2::one());
        }
    }

    #[test]
    fn g2_test_is_valid() {
        // Reject point on isomorphic twist (b = 3 * (u + 1))
        {
            let p = G2Affine {
                x: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0xa757072d9fa35ba9,
                        0xae3fb2fb418f6e8a,
                        0xc1598ec46faa0c7c,
                        0x7a17a004747e3dbe,
                        0xcc65406a7c2e5a73,
                        0x10b8c03d64db4d0c,
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0xd30e70fe2f029778,
                        0xda30772df0f5212e,
                        0x5b47a9ff9a233a50,
                        0xfb777e5b9b568608,
                        0x789bac1fec71a2b9,
                        0x1342f02e2da54405,
                    ]))
                    .unwrap(),
                },
                y: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0xfe0812043de54dca,
                        0xe455171a3d47a646,
                        0xa493f36bc20be98a,
                        0x663015d9410eb608,
                        0x78e82a79d829a544,
                        0x40a00545bb3c1e,
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0x4709802348e79377,
                        0xb5ac4dc9204bcfbd,
                        0xda361c97d02f42b2,
                        0x15008b1dc399e8df,
                        0x68128fd0548a3829,
                        0x16a613db5c873aaa,
                    ]))
                    .unwrap(),
                },
                infinity: false,
            };
            assert!(!p.is_on_curve());
            assert!(p.is_in_correct_subgroup_assuming_on_curve());
        }

        // Reject point on a twist (b = 2 * (u + 1))
        {
            let p = G2Affine {
                x: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0xf4fdfe95a705f917,
                        0xc2914df688233238,
                        0x37c6b12cca35a34b,
                        0x41abba710d6c692c,
                        0xffcc4b2b62ce8484,
                        0x6993ec01b8934ed,
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0xb94e92d5f874e26,
                        0x44516408bc115d95,
                        0xe93946b290caa591,
                        0xa5a0c2b7131f3555,
                        0x83800965822367e7,
                        0x10cf1d3ad8d90bfa,
                    ]))
                    .unwrap(),
                },
                y: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0xbf00334c79701d97,
                        0x4fe714f9ff204f9a,
                        0xab70b28002f3d825,
                        0x5a9171720e73eb51,
                        0x38eb4fd8d658adb7,
                        0xb649051bbc1164d,
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0x9225814253d7df75,
                        0xc196c2513477f887,
                        0xe05e2fbd15a804e0,
                        0x55f2b8efad953e04,
                        0x7379345eda55265e,
                        0x377f2e6208fd4cb,
                    ]))
                    .unwrap(),
                },
                infinity: false,
            };
            assert!(!p.is_on_curve());
            assert!(!p.is_in_correct_subgroup_assuming_on_curve());
        }

        // Reject point in an invalid subgroup
        // There is only one r-order subgroup, as r does not divide the cofactor.
        {
            let p = G2Affine {
                x: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0x262cea73ea1906c,
                        0x2f08540770fabd6,
                        0x4ceb92d0a76057be,
                        0x2199bc19c48c393d,
                        0x4a151b732a6075bf,
                        0x17762a3b9108c4a7,
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0x26f461e944bbd3d1,
                        0x298f3189a9cf6ed6,
                        0x74328ad8bc2aa150,
                        0x7e147f3f9e6e241,
                        0x72a9b63583963fff,
                        0x158b0083c000462,
                    ]))
                    .unwrap(),
                },
                y: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0x91fb0b225ecf103b,
                        0x55d42edc1dc46ba0,
                        0x43939b11997b1943,
                        0x68cad19430706b4d,
                        0x3ccfb97b924dcea8,
                        0x1660f93434588f8d,
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0xaaed3985b6dcb9c7,
                        0xc1e985d6d898d9f4,
                        0x618bd2ac3271ac42,
                        0x3940a2dbb914b529,
                        0xbeb88137cf34f3e7,
                        0x1699ee577c61b694,
                    ]))
                    .unwrap(),
                },
                infinity: false,
            };
            assert!(p.is_on_curve());
            assert!(!p.is_in_correct_subgroup_assuming_on_curve());
        }
    }

    #[test]
    fn test_g2_addition_correctness() {
        let mut p = G2 {
            x: Fq2 {
                c0: Fq::from_repr(FqRepr([
                    0x6c994cc1e303094e,
                    0xf034642d2c9e85bd,
                    0x275094f1352123a9,
                    0x72556c999f3707ac,
                    0x4617f2e6774e9711,
                    0x100b2fe5bffe030b,
                ]))
                .unwrap(),
                c1: Fq::from_repr(FqRepr([
                    0x7a33555977ec608,
                    0xe23039d1fe9c0881,
                    0x19ce4678aed4fcb5,
                    0x4637c4f417667e2e,
                    0x93ebe7c3e41f6acc,
                    0xde884f89a9a371b,
                ]))
                .unwrap(),
            },
            y: Fq2 {
                c0: Fq::from_repr(FqRepr([
                    0xe073119472e1eb62,
                    0x44fb3391fe3c9c30,
                    0xaa9b066d74694006,
                    0x25fd427b4122f231,
                    0xd83112aace35cae,
                    0x191b2432407cbb7f,
                ]))
                .unwrap(),
                c1: Fq::from_repr(FqRepr([
                    0xf68ae82fe97662f5,
                    0xe986057068b50b7d,
                    0x96c30f0411590b48,
                    0x9eaa6d19de569196,
                    0xf6a03d31e2ec2183,
                    0x3bdafaf7ca9b39b,
                ]))
                .unwrap(),
            },
            z: Fq2::one(),
        };

        p.add_assign(&G2 {
            x: Fq2 {
                c0: Fq::from_repr(FqRepr([
                    0xa8c763d25910bdd3,
                    0x408777b30ca3add4,
                    0x6115fcc12e2769e,
                    0x8e73a96b329ad190,
                    0x27c546f75ee1f3ab,
                    0xa33d27add5e7e82,
                ]))
                .unwrap(),
                c1: Fq::from_repr(FqRepr([
                    0x93b1ebcd54870dfe,
                    0xf1578300e1342e11,
                    0x8270dca3a912407b,
                    0x2089faf462438296,
                    0x828e5848cd48ea66,
                    0x141ecbac1deb038b,
                ]))
                .unwrap(),
            },
            y: Fq2 {
                c0: Fq::from_repr(FqRepr([
                    0xf5d2c28857229c3f,
                    0x8c1574228757ca23,
                    0xe8d8102175f5dc19,
                    0x2767032fc37cc31d,
                    0xd5ee2aba84fd10fe,
                    0x16576ccd3dd0a4e8,
                ]))
                .unwrap(),
                c1: Fq::from_repr(FqRepr([
                    0x4da9b6f6a96d1dd2,
                    0x9657f7da77f1650e,
                    0xbc150712f9ffe6da,
                    0x31898db63f87363a,
                    0xabab040ddbd097cc,
                    0x11ad236b9ba02990,
                ]))
                .unwrap(),
            },
            z: Fq2::one(),
        });

        let p = G2Affine::from(p);

        assert_eq!(
            p,
            G2Affine {
                x: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0xcde7ee8a3f2ac8af,
                        0xfc642eb35975b069,
                        0xa7de72b7dd0e64b7,
                        0xf1273e6406eef9cc,
                        0xababd760ff05cb92,
                        0xd7c20456617e89
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0xd1a50b8572cbd2b8,
                        0x238f0ac6119d07df,
                        0x4dbe924fe5fd6ac2,
                        0x8b203284c51edf6b,
                        0xc8a0b730bbb21f5e,
                        0x1a3b59d29a31274
                    ]))
                    .unwrap(),
                },
                y: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0x9e709e78a8eaa4c9,
                        0xd30921c93ec342f4,
                        0x6d1ef332486f5e34,
                        0x64528ab3863633dc,
                        0x159384333d7cba97,
                        0x4cb84741f3cafe8
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0x242af0dc3640e1a4,
                        0xe90a73ad65c66919,
                        0x2bd7ca7f4346f9ec,
                        0x38528f92b689644d,
                        0xb6884deec59fb21f,
                        0x3c075d3ec52ba90
                    ]))
                    .unwrap(),
                },
                infinity: false,
            }
        );
    }

    #[test]
    fn test_g2_doubling_correctness() {
        let mut p = G2 {
            x: Fq2 {
                c0: Fq::from_repr(FqRepr([
                    0x6c994cc1e303094e,
                    0xf034642d2c9e85bd,
                    0x275094f1352123a9,
                    0x72556c999f3707ac,
                    0x4617f2e6774e9711,
                    0x100b2fe5bffe030b,
                ]))
                .unwrap(),
                c1: Fq::from_repr(FqRepr([
                    0x7a33555977ec608,
                    0xe23039d1fe9c0881,
                    0x19ce4678aed4fcb5,
                    0x4637c4f417667e2e,
                    0x93ebe7c3e41f6acc,
                    0xde884f89a9a371b,
                ]))
                .unwrap(),
            },
            y: Fq2 {
                c0: Fq::from_repr(FqRepr([
                    0xe073119472e1eb62,
                    0x44fb3391fe3c9c30,
                    0xaa9b066d74694006,
                    0x25fd427b4122f231,
                    0xd83112aace35cae,
                    0x191b2432407cbb7f,
                ]))
                .unwrap(),
                c1: Fq::from_repr(FqRepr([
                    0xf68ae82fe97662f5,
                    0xe986057068b50b7d,
                    0x96c30f0411590b48,
                    0x9eaa6d19de569196,
                    0xf6a03d31e2ec2183,
                    0x3bdafaf7ca9b39b,
                ]))
                .unwrap(),
            },
            z: Fq2::one(),
        };

        p.double();

        let p = G2Affine::from(p);

        assert_eq!(
            p,
            G2Affine {
                x: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0x91ccb1292727c404,
                        0x91a6cb182438fad7,
                        0x116aee59434de902,
                        0xbcedcfce1e52d986,
                        0x9755d4a3926e9862,
                        0x18bab73760fd8024
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0x4e7c5e0a2ae5b99e,
                        0x96e582a27f028961,
                        0xc74d1cf4ef2d5926,
                        0xeb0cf5e610ef4fe7,
                        0x7b4c2bae8db6e70b,
                        0xf136e43909fca0
                    ]))
                    .unwrap(),
                },
                y: Fq2 {
                    c0: Fq::from_repr(FqRepr([
                        0x954d4466ab13e58,
                        0x3ee42eec614cf890,
                        0x853bb1d28877577e,
                        0xa5a2a51f7fde787b,
                        0x8b92866bc6384188,
                        0x81a53fe531d64ef
                    ]))
                    .unwrap(),
                    c1: Fq::from_repr(FqRepr([
                        0x4c5d607666239b34,
                        0xeddb5f48304d14b3,
                        0x337167ee6e8e3cb6,
                        0xb271f52f12ead742,
                        0x244e6c2015c83348,
                        0x19e2deae6eb9b441
                    ]))
                    .unwrap(),
                },
                infinity: false,
            }
        );
    }

    #[test]
    fn test_g2_sw_encode_degenerate() {
        // test the degenerate cases t = 0 and t^2 = - b - 1
        let p = G2Affine::sw_encode(Fq2::zero());
        assert!(p.is_on_curve());
        assert!(p.is_zero());

        let mut t = Fq2::one();
        t.add_assign(&G2Affine::get_coeff_b());
        t.negate();
        assert_eq!(t.sqrt(), None);
    }

    #[test]
    fn g2_hash_test_vectors() {
        // Obtained via python/sage

        let p = G2::hash(&[]);
        let q = G2 {
            x: Fq2 {
                c0: Fq::from_str("1703269368484048424021410903959703695180015303406562561298910892586704964724393392000690938204229678426081532099421").unwrap(),
                c1: Fq::from_str("1899273078921065702469032215023284089292737398509481436818508674759333584516218669155175722702009534138251936259418").unwrap(),
            },
            y: Fq2 {
                c0: Fq::from_str("1983733072556618192444995460520049530986901623449598282145749270559646083332830971089171683246431283765594628842386").unwrap(),
                c1: Fq::from_str("915456324395362816875268588526293724551529076411493014293832389675785871078275824878933205442411635336958461433442").unwrap(),
            },
            z: Fq2::one()
        };

        assert_eq!(p, q);
    }

    #[test]
    fn g2_curve_tests() {
        use groupy::tests::curve_tests;
        curve_tests::<G2>();
    }

    #[test]
    fn test_iso3_zero() {
        let zero = Fq2::zero();
        let mut pt = G2 {
            x: Fq2::zero(),
            y: Fq2::zero(),
            z: Fq2::zero(),
        };
        pt.isogeny_map();
        assert_eq!(pt.x, zero);
        assert_eq!(pt.y, zero);
        assert_eq!(pt.z, zero);
    }

    #[test]
    fn test_iso3_one() {
        let mut pt = G2 {
            x: Fq2::one(),
            y: Fq2::one(),
            z: Fq2::one(),
        };
        pt.isogeny_map();
        let c0 = FqRepr([
            0x57c6555579807bcau64,
            0xc285c71b6d7a38e3u64,
            0xde7b4e7d31a614c6u64,
            0x31b21e4af64b0e94u64,
            0x8fc02d1bfb73bf52u64,
            0x1439b899baf1b35bu64,
        ]);
        let c1 = FqRepr([
            0xf58daaab358a307bu64,
            0x665f8e3829a071c6u64,
            0x55c5ca596c9b3369u64,
            0xfeecf110f9110a6au64,
            0xd464b281b39bd1ccu64,
            0x0e725f493c63801cu64,
        ]);
        let x_expect = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let c0 = FqRepr([
            0xa72f3db7cb8405a4u64,
            0x221fda12b88ad097u64,
            0x71ec98c879891123u64,
            0x54f9a5b05305ae23u64,
            0xf176e62b3bde9b44u64,
            0x04d0ca6dbecbd55eu64,
        ]);
        let c1 = FqRepr([
            0xe1b3626ab65e39a9u64,
            0x4e79097a56dc4bd9u64,
            0xb0e977c69aa27452u64,
            0x761b0f37a1e26286u64,
            0xfbf7043de3811ad0u64,
            0x124c9ad43b6cf79bu64,
        ]);
        let y_expect = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let c0 = FqRepr([
            0xb9fefffffffebb2au64,
            0x1eabfffeb153ffffu64,
            0x6730d2a0f6b0f624u64,
            0x64774b84f38512bfu64,
            0x4b1ba7b6434bacd7u64,
            0x1a0111ea397fe69au64,
        ]);
        let c1 = FqRepr([
            0x00000000000065b2u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
            0x0000000000000000u64,
        ]);
        let z_expect = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        assert_eq!(pt.x, x_expect);
        assert_eq!(pt.y, y_expect);
        assert_eq!(pt.z, z_expect);
    }

    #[test]
    fn test_iso3_fixed() {
        let c0 = FqRepr([
            0x0018c03388164247u64,
            0xc4c8890b30d528ebu64,
            0xd52d2a45caca6edau64,
            0x89b3941228dae354u64,
            0x3f3f7d07e4c40a93u64,
            0x0530990b2b3e9a8au64,
        ]);
        let c1 = FqRepr([
            0x6b90db064d0030e9u64,
            0xd6a6501c1871b906u64,
            0x11c92e91687441adu64,
            0xf974e31a71e5fe1fu64,
            0x87933ab312f66f88u64,
            0x117d0dba9f178439u64,
        ]);
        let xi = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let c0 = FqRepr([
            0x6dee4915e87b601au64,
            0xad55ed81ecc390ffu64,
            0xa9c3c810a96f8ca7u64,
            0x0c7d97874f6f026du64,
            0x967de59661e37bb5u64,
            0x11b94175e3be4de8u64,
        ]);
        let c1 = FqRepr([
            0x53563b5cfa722ba8u64,
            0x41b7f7263e23c28eu64,
            0x17cf622d5607fbcau64,
            0xe8722180e02d0818u64,
            0xf8c75b4c8b66c965u64,
            0x035eea1ab1a2a087u64,
        ]);
        let yi = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let c0 = FqRepr([
            0x71f8d78673dbfa39u64,
            0x62d7bae1a74336dcu64,
            0x53bf87ae6e302bd3u64,
            0x4d197aa97c5317f5u64,
            0xc41aa271acd3a3a1u64,
            0x189add484077dd45u64,
        ]);
        let c1 = FqRepr([
            0x9a214bfcea21674fu64,
            0x3a5d62187b013310u64,
            0xc15f3a4db5bc86a7u64,
            0x96b99fa5eb4f47c8u64,
            0xb36b52b4a8696193u64,
            0x0e613ba7c4916c20u64,
        ]);
        let zi = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let mut pt = G2 {
            x: xi,
            y: yi,
            z: zi,
        };
        pt.isogeny_map();
        let c0 = FqRepr([
            0xf119e132b7ebd22cu64,
            0x37932278669819e7u64,
            0xdb71788e6d1c6512u64,
            0x678934e396004f81u64,
            0x55213880b7ed140du64,
            0x181403b14aa19327u64,
        ]);
        let c1 = FqRepr([
            0xdaac25bd8310aef3u64,
            0xbdaab7e27633f5d2u64,
            0x2e8422b082fc8c69u64,
            0xf6b6f9af2f2fc258u64,
            0x8b649eeb97f5676eu64,
            0x13f21dc8a4dfcc1au64,
        ]);
        let x_expect = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let c0 = FqRepr([
            0xbe1f08d76520ec2au64,
            0xd9ef23f135188a36u64,
            0x3b97d6bb83c22918u64,
            0x6a2ce7736962cd7cu64,
            0x95d5421d9c9465deu64,
            0x09cab53c88c263bdu64,
        ]);
        let c1 = FqRepr([
            0x3e6a004356660064u64,
            0x0b182f682ab74743u64,
            0xc53c7316655326eau64,
            0x669c0d885b42452au64,
            0x97df98a239aa957du64,
            0x06299d091ec0ed11u64,
        ]);
        let y_expect = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        let c0 = FqRepr([
            0xe518e02aaa358acdu64,
            0x4c00a671fa8fc185u64,
            0xf88193c7dd618937u64,
            0x2d6e07a3e0ca5733u64,
            0x121d7ae073e479fdu64,
            0x00644ae14e9341fbu64,
        ]);
        let c1 = FqRepr([
            0x9bed7fa96e783e15u64,
            0xde7d5d396f73c236u64,
            0x491857011bcac282u64,
            0x82d08553b1dacca2u64,
            0x41def4997b2fc93fu64,
            0x14474088f5b1d2e3u64,
        ]);
        let z_expect = Fq2 {
            c0: Fq::from_repr(c0).unwrap(),
            c1: Fq::from_repr(c1).unwrap(),
        };
        assert_eq!(pt.x, x_expect);
        assert_eq!(pt.y, y_expect);
        assert_eq!(pt.z, z_expect);
    }

    fn check_g2_prime(x: &Fq2, y: &Fq2, z: &Fq2) {
        check_g_prime(x, y, z, &ELLP_A, &ELLP_B);
    }

    #[test]
    fn test_osswu_g2() {
        let c0 =
            Fq::from_repr(FqRepr([0xb1e40u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64])).unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xb9fefffffffbf5ebu64,
            0x1eabfffeb153ffffu64,
            0x6730d2a0f6b0f624u64,
            0x64774b84f38512bfu64,
            0x4b1ba7b6434bacd7u64,
            0x1a0111ea397fe69au64,
        ]))
        .unwrap();
        let xo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x28d6c99ea4383807u64,
            0x59cc5836c91ef30fu64,
            0xa87d216900801408u64,
            0x2610ff4c3c3f9eb1u64,
            0x4f4b3ea32be995fcu64,
            0xdc6721ebe6be37u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x60e0254afc5ba93bu64,
            0x407c6124b57df4cu64,
            0xf8f3c1f44b0f8c7au64,
            0xb96a3df0badd28fau64,
            0x3d04c58bb5e6260u64,
            0x12b21ca35569a3eeu64,
        ]))
        .unwrap();
        let yo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([0xf0u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64])).unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xb9feffffffffa8cbu64,
            0x1eabfffeb153ffffu64,
            0x6730d2a0f6b0f624u64,
            0x64774b84f38512bfu64,
            0x4b1ba7b6434bacd7u64,
            0x1a0111ea397fe69au64,
        ]))
        .unwrap();
        let zo = Fq2 { c0, c1 };
        let p = G2::osswu_map(&Fq2::zero());
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &yo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let c0 =
            Fq::from_repr(FqRepr([0x76980u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64])).unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x3b4c00u64,
            0x0u64,
            0x0u64,
            0x0u64,
            0x0u64,
            0x0u64,
        ]))
        .unwrap();
        let xo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0xe24baa0a898b47e0u64,
            0x92afb1b88e09c84cu64,
            0xf16d677192b7b78au64,
            0xab1dd12189c47c0eu64,
            0xc30f74ce786d38e9u64,
            0xcc49de633f05c98u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x936dda4aedcab1e1u64,
            0x8261a18f1038bdbu64,
            0xc08dea79dde085du64,
            0x9002d76a3ed1ffd2u64,
            0x185ab763985ff885u64,
            0xbab7cc25639665u64,
        ]))
        .unwrap();
        let yo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([0x2d0u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64, 0x0u64])).unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xb9feffffffffa9bbu64,
            0x1eabfffeb153ffffu64,
            0x6730d2a0f6b0f624u64,
            0x64774b84f38512bfu64,
            0x4b1ba7b6434bacd7u64,
            0x1a0111ea397fe69au64,
        ]))
        .unwrap();
        let zo = Fq2 { c0, c1 };
        let p = G2::osswu_map(&Fq2::one());
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &yo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let m1 = {
            let mut tmp = Fq2::one();
            tmp.negate();
            tmp
        };
        let p = G2::osswu_map(&m1);
        let myo = {
            let mut tmp = yo;
            tmp.negate();
            tmp
        };
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &myo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let c0 = Fq::from_repr(FqRepr([
            0xd4e2aa3bbf9a8255u64,
            0xa79f2ece3390978cu64,
            0x48c1a8fdff541ebau64,
            0x2b17303f8af1ec82u64,
            0x86657cd3fc3d08b5u64,
            0x14f05da1ad4eddc8u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x472f6df27fe7c94du64,
            0xea72d4e6f4f06693u64,
            0xd1a89c5e84e6d193u64,
            0xab80a6a3842df525u64,
            0x46e112ac0a450ea4u64,
            0x171441a6d04ca8a9u64,
        ]))
        .unwrap();
        let u = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x19399d7e6e728efau64,
            0x9223ea49b3a6685bu64,
            0xb0535eeb3e0be8eeu64,
            0xccdd7c2ed7a70c2du64,
            0x192ab8f31b9bb432u64,
            0xc0b207783a7fe8au64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xc65c4431a6496c30u64,
            0x8542454973283f10u64,
            0xa7808bb40eebf6b9u64,
            0x683e0aad6e74a5a0u64,
            0x2076b05de214ef02u64,
            0xe039ae7c29d2022u64,
        ]))
        .unwrap();
        let xo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0xcb28446e62179d9eu64,
            0xa280a992df73998eu64,
            0x2d5291422919d305u64,
            0x418c865e205bc0c6u64,
            0xf8d1e5e8c38550acu64,
            0xee2df0d5e07448fu64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xaa7c2684fe2fcc6eu64,
            0x99a983385cb3106fu64,
            0x37ad3280cb8a1519u64,
            0x5a4308b2de7f901du64,
            0xf2f74d4b44fadc7cu64,
            0x6ac1c85e32f4edcu64,
        ]))
        .unwrap();
        let yo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x9e31b14df8456862u64,
            0xb09d54057305d0eau64,
            0x7d4ec28cf63bbd66u64,
            0x1817c2139c736f55u64,
            0x7fd9f027c2ed4347u64,
            0x18d33c46e9efe1f7u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x4da85b1219f0aa69u64,
            0x9eb5f7883c8356b6u64,
            0x9d27373105a8522fu64,
            0x5be18ff40be45f19u64,
            0x9b693bc483f0f59fu64,
            0x922c5bef1fc118cu64,
        ]))
        .unwrap();
        let zo = Fq2 { c0, c1 };
        let p = G2::osswu_map(&u);
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &yo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let c0 = Fq::from_repr(FqRepr([
            0xdfad7422a0bab889u64,
            0x4a70b9f85b2c6f5au64,
            0xc042f72ce88d22f5u64,
            0x5be4f1d4b77bef62u64,
            0x99207c0238d7ab04u64,
            0x6135a609e9aad26u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x34f124763e7deb00u64,
            0xa285e8e52a9cf5f5u64,
            0x3463f5943127700cu64,
            0xeea0ef2a7244c951u64,
            0xeeedf7205412c6a4u64,
            0x3ac7d4da624f424u64,
        ]))
        .unwrap();
        let u = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x470a0eb4c6ea41dau64,
            0x38fc102a7ac96c4bu64,
            0xf12cc75f43f16fau64,
            0x1ae7110401d2bf60u64,
            0xabcdd7ccae9a680au64,
            0x7a6102bf5d97c9cu64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x184b0324bbf4ec25u64,
            0x14e6a614c88543ebu64,
            0x11b6dadcb855c02eu64,
            0x45d1bc1a7b21bf38u64,
            0x6e9811b7292cbe35u64,
            0x20c43c3e504b49du64,
        ]))
        .unwrap();
        let xo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x6c3bf81fbed884beu64,
            0xc9913eda07951808u64,
            0x74fe400d891f0d2fu64,
            0x66459536249908u64,
            0xc6dd9a1dd87e2749u64,
            0x15ab62367cef7a16u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xf0f9b256ffd9ffd0u64,
            0xc481edd39780ca8fu64,
            0x5ea12e0601bcb0adu64,
            0x92ffe49990fd9032u64,
            0xacc33c14b83593a7u64,
            0x5048b4e608e7595u64,
        ]))
        .unwrap();
        let yo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x85e0d5489736e2b4u64,
            0x6c5118e2091d88f0u64,
            0x8b41f404e6916df1u64,
            0xda99a9546f39acf9u64,
            0x57587e3b4ed7340du64,
            0x170ef6f0827380fcu64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xdd61a360bf21c990u64,
            0xe87c9a8fbef8edfeu64,
            0x674f970b3d82e9b8u64,
            0xb3f831e1eabbf03bu64,
            0xcee9367de3ca318u64,
            0x160a61c5ad6a3ff3u64,
        ]))
        .unwrap();
        let zo = Fq2 { c0, c1 };
        let p = G2::osswu_map(&u);
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &yo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let c0 = Fq::from_repr(FqRepr([
            0xaf50b546edfc358au64,
            0x3f1897a2f38a122eu64,
            0xdad7bf8fa9eb51beu64,
            0x34c9f03ed6c4ba66u64,
            0x9ee6db517906e388u64,
            0x1097781715e5c672u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x9c0ae60f939506a8u64,
            0xa4ef9b76946849beu64,
            0x2d7708869060ff0cu64,
            0xbd6d915e7952a21du64,
            0xbfa926b829513c7eu64,
            0x1732337eace2d016u64,
        ]))
        .unwrap();
        let u = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x80330decf209c0f9u64,
            0x9c3c443d2148943cu64,
            0x7b012833fbb8d302u64,
            0xc46b5c5bdffaf903u64,
            0xdc32da48bd881df2u64,
            0xf7a0d745e96ee8cu64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x1f77ac75a53cb01du64,
            0x331ccd087fe7e20u64,
            0xc798a6624c5c2657u64,
            0x318fdef5c6a03aaeu64,
            0x75d649c08a4329b5u64,
            0xd8461734f2b818du64,
        ]))
        .unwrap();
        let xo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x979dcacafe864046u64,
            0x58d5a8feda1b9c68u64,
            0x2dc7fe64d491eb67u64,
            0x1e4eda823cf7dd15u64,
            0x307aa36319482608u64,
            0x2251c003acfa5u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x71eae2c9a83ace48u64,
            0x94e7e90db7f89c6eu64,
            0xeb1f1e2094f14b12u64,
            0x4c44debec0dd26f4u64,
            0x78fd720e9efd3821u64,
            0x145c52e57606ffa5u64,
        ]))
        .unwrap();
        let yo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x9b1eaa292b0b8d6cu64,
            0xf3556f782b80156au64,
            0x7232a60dfcf45578u64,
            0xda283bc794f1c552u64,
            0x72e449993919e49au64,
            0xdd03753cbb62029u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x5e1300be109addd0u64,
            0xf9a438110153ac6fu64,
            0x3f16da21234b7dfeu64,
            0x668a29f291c491ccu64,
            0xb007536e7f23b656u64,
            0x1435472d4037af40u64,
        ]))
        .unwrap();
        let zo = Fq2 { c0, c1 };
        let p = G2::osswu_map(&u);
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &yo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let c0 = Fq::from_repr(FqRepr([
            0xea84b00658419fc4u64,
            0xdc23cabb1c5bedd0u64,
            0x51b2c9560f33a8d5u64,
            0xdce76c736ec4a3d3u64,
            0xaed02316b6641449u64,
            0x17c2c631ba5d8bebu64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xb2577499ede5f632u64,
            0xca3d6ab753b878fu64,
            0x1833b9b48c4d08cdu64,
            0x9df66243f1e33375u64,
            0xeecbfb9b9c09d227u64,
            0x7a4a6b660e99b12u64,
        ]))
        .unwrap();
        let u = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x9b719651c4c746e6u64,
            0xbd438453f89d2adcu64,
            0x22116768f501742eu64,
            0x51174b39ab6bc2cu64,
            0xe1c665b1e5c63de6u64,
            0x1842adaf28baae5u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x6b54949d6f96dbcfu64,
            0xa915298df9efc27au64,
            0x3439428ca0b987e5u64,
            0x61ea03ec041d8965u64,
            0x86c6f8125dc0bbc2u64,
            0xddb31de92a06828u64,
        ]))
        .unwrap();
        let xo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x4b0f0747efbfaa2bu64,
            0xf5501541912d865bu64,
            0x977c499198af07aau64,
            0xd446b9a7fad8f3b9u64,
            0x4badb10ce5e47e33u64,
            0x907aa22e7410129u64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0xdd46de8193ef06f6u64,
            0x4cce40b2f67a7123u64,
            0xd843215fe615c9b4u64,
            0x8d839820983c4b41u64,
            0x16042cc81ac4edddu64,
            0x7eff2aeb396734au64,
        ]))
        .unwrap();
        let yo = Fq2 { c0, c1 };
        let c0 = Fq::from_repr(FqRepr([
            0x23f96d2a1601cb7u64,
            0x6a074b0a3175cbfcu64,
            0x28a4ab30815e16a1u64,
            0x1030979d8436dd2eu64,
            0xb43ad04879add9d4u64,
            0x522b59175626baau64,
        ]))
        .unwrap();
        let c1 = Fq::from_repr(FqRepr([
            0x6992705ff971d0dau64,
            0x295c53f6b1faaa69u64,
            0xe07009934bc1022eu64,
            0x47e2a110d26f261u64,
            0x1721f26639694182u64,
            0x15dba187573a86c3u64,
        ]))
        .unwrap();
        let zo = Fq2 { c0, c1 };
        let p = G2::osswu_map(&u);
        let G2 { x, y, z } = &p;
        assert_eq!(x, &xo);
        assert_eq!(y, &yo);
        assert_eq!(z, &zo);
        check_g2_prime(x, y, z);

        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..32 {
            let input = Fq2::random(&mut rng);
            let p = G2::osswu_map(&input);
            let G2 { x, y, z } = &p;
            check_g2_prime(x, y, z);
        }
    }
}
