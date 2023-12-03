use crypto_bigint::{
    modular::runtime_mod::{DynResidue, DynResidueParams},
    U256,
};

/// Natural numbers represented as cryptographically safe big unsigned
/// integers. Arithmetic operations are checked for overflow at run-time
pub type Nat = U256;

/// Computes `lhs * rhs mod modulus`
pub fn mul_mod(lhs: &Nat, rhs: &Nat, modulus: &Nat) -> Nat {
    let dyn_residue_lhs = DynResidue::new(lhs, DynResidueParams::new(modulus));
    let dyn_residue_rhs = DynResidue::new(rhs, DynResidueParams::new(modulus));
    dyn_residue_lhs.mul(&dyn_residue_rhs).retrieve()
}

pub fn pow_mod(base: &Nat, exponent: &Nat, modulus: &Nat) -> Nat {
    let dyn_residue = DynResidue::new(base, DynResidueParams::new(modulus));
    dyn_residue.pow(exponent).retrieve()
}

#[cfg(test)]
mod test {
    use std::ops::Rem;

    use crate::groups::GroupSpec;

    use super::*;

    #[test]
    fn test_mul_mod() {
        let a = 7_u32;
        let b = 3_u32;
        let c = 5_u32;

        assert_eq!(
            mul_mod(&Nat::from(a), &Nat::from(b), &Nat::from(c)),
            Nat::from((a * b).rem(c))
        );
        assert_eq!(
            mul_mod(&Nat::from(c), &Nat::from(a), &Nat::from(b)),
            Nat::from((c * a).rem(b))
        );
        assert_eq!(
            mul_mod(&Nat::from(b), &Nat::from(c), &Nat::from(a)),
            Nat::from((b * c).rem(a))
        );
    }

    #[test]
    fn test_pow_mod() {
        let a = 2_u32;
        let b = 4_u32;
        let c = 23_u32;

        assert_eq!(
            pow_mod(&Nat::from(a), &Nat::from(b), &Nat::from(c)),
            Nat::from_u32(16)
        );
    }

    #[test]
    fn test_large_pow_mod_for_group() {
        let group = GroupSpec::new();
        let g = group.alpha;
        let q = group.q;
        let p = group.p;

        assert_eq!(pow_mod(&g, &q, &p), Nat::from(1_u32));
    }
}
