use crypto_bigint::{rand_core::OsRng, NonZero, RandomMod};

use crate::nat::{pow_mod, Nat};
use crypto_primes::generate_safe_prime;

/// A specification of the subgroup from Zp of prime order q,
/// where p is a safe prime with associated Sofie Germain prime q
#[derive(Debug)]
pub struct GroupSpec {
    /// Primes p and q where p = 2q+1
    pub p: NonZero<Nat>,
    pub q: NonZero<Nat>,
    /// Generator of the group, ord(g) = q
    pub alpha: Nat,
}

impl GroupSpec {
    /// Constructs a new GroupSpec with a random 256 bit safe
    /// primes p and q with p = 2q+1 and a random generator of the
    /// subgroup from Zp of prime order q.
    pub fn new() -> GroupSpec {
        let (p, q) = generate_safe_primes();
        let alpha = compute_group_generator(p, q);
        GroupSpec { p, q, alpha }
    }

    /// Returns a random from Zq
    pub fn rand_exp(&self) -> Nat {
        Nat::random_mod(&mut OsRng, &self.q)
    }
}

/// Generate a generator of Zp* using rejection sampling from the
/// lecture notes
fn compute_group_generator(p: NonZero<Nat>, q: NonZero<Nat>) -> Nat {
    let mut x = Nat::random_mod(&mut OsRng, &p);
    // While x^q mod p != 1 try with a new random x
    while pow_mod(&x, &q, &p) != Nat::ONE {
        x = Nat::random_mod(&mut OsRng, &p);
    }
    x
}

/// Generate a safe prime p = 2q + 1, where q is the associated Sophie Germain prime
/// Uses crypto-primes library
fn generate_safe_primes() -> (NonZero<Nat>, NonZero<Nat>) {
    let p: NonZero<Nat> = NonZero::new(generate_safe_prime(Option::None)).unwrap();
    let qinit: Nat = p
        .wrapping_sub(&Nat::ONE)
        .checked_div(&Nat::from(2_u32))
        .unwrap();
    let q = NonZero::new(qinit).unwrap();
    (p, q)
}

impl Default for GroupSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nat::pow_mod;

    #[test]
    fn test_generator_from_safe_prime() {
        let group = GroupSpec::new();
        let alpha = group.alpha;
        // Test for alpha being a generator of Zp*
        let raised = pow_mod(&alpha, &group.q, &group.p);

        assert_eq!(raised, Nat::ONE)
    }
}
