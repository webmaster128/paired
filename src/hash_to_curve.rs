//! This module defines a hash_to_curve trait.

use groupy::CurveProjective;

use crate::bls12_381::{ClearH, IsogenyMap, OsswuMap};
use crate::{FromRO, HashToField};

type CoordT<PtT> = <PtT as CurveProjective>::Base;

/// Random oracle and injective maps to curve
pub trait HashToCurve {
    /// Random oracle
    fn hash_to_curve<B: AsRef<[u8]>, C: AsRef<[u8]>>(msg: B, ciphersuite: C) -> Self;

    /// Injective encoding
    fn encode_to_curve<B: AsRef<[u8]>, C: AsRef<[u8]>>(msg: B, ciphersuite: C) -> Self;
}

impl<PtT> HashToCurve for PtT
where
    PtT: ClearH + IsogenyMap + OsswuMap,
    CoordT<PtT>: FromRO,
{
    fn hash_to_curve<B: AsRef<[u8]>, C: AsRef<[u8]>>(msg: B, ciphersuite: C) -> PtT {
        let mut p = {
            let h2f = HashToField::<CoordT<PtT>>::new(msg, Some(ciphersuite.as_ref()));
            let mut tmp = PtT::osswu_map(&h2f.with_ctr(0));
            tmp.add_assign(&PtT::osswu_map(&h2f.with_ctr(1)));
            tmp
        };
        p.isogeny_map();
        p.clear_h();
        p
    }

    fn encode_to_curve<B: AsRef<[u8]>, C: AsRef<[u8]>>(msg: B, ciphersuite: C) -> PtT {
        let mut p = {
            let h2f = HashToField::<CoordT<PtT>>::new(msg, Some(ciphersuite.as_ref()));
            PtT::osswu_map(&h2f.with_ctr(2))
        };
        p.isogeny_map();
        p.clear_h();
        p
    }
}
