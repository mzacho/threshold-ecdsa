use crypto_bigint::{
    modular::runtime_mod::{DynResidue, DynResidueParams},
    NonZero, U64, U256,
};
use lazy_static::lazy_static;

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

// Hard coded modulus for the group
// BigUint cannot be declared as a const due to non-const fun-call,
// the crate lazy_static provides a way to get the same behaviour
// by allocating it at runtime instead.
lazy_static! {
    /// Hard coded prime for the group (Q)
    pub static ref M: NonZero<Nat> = NonZero::new(Nat::from(13506768629334054143_u64)).unwrap();
    /// Hard coded prime for the group (P)
    pub static ref P: NonZero<Nat> = NonZero::new(Nat::from(27013537258668108287_u128)).unwrap();
    /// Hard coded generator for the group (G)
    pub static ref G: Nat = Nat::from(16496305264446614492_u64);

    // pub static ref M: CNat = Checked::new(Nat::from(153_u32));
}

#[cfg(test)]
mod test {
    use std::ops::Rem;

    use crypto_bigint::MulMod;

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
        let a = 7_u32;
        let b = 3_u32;
        let c = 5_u32;

        assert_eq!(
            pow_mod(&Nat::from(a), &Nat::from(b), &Nat::from(c)),
            Nat::from(a.pow(b).rem(c))
        );
        assert_eq!(
            pow_mod(&Nat::from(c), &Nat::from(a), &Nat::from(b)),
            Nat::from(c.pow(a).rem(b))
        );
        assert_eq!(
            pow_mod(&Nat::from(b), &Nat::from(c), &Nat::from(a)),
            Nat::from(b.pow(c).rem(a))
        );
    }

    #[test]
    fn test_large_pow_mod_for_group() {
        let g = G.clone();
        let q = M.clone();
        let p = P.clone();

        assert_eq!(pow_mod(&g, &q, &p), Nat::from(1_u32));
    }
}
