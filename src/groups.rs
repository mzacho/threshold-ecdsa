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
    /// Constructs a new group spec with security parameter k
    /// i.e. k is the bitsize of q = M
    pub fn new() -> GroupSpec {
        // Generate random safe prime p = 2q + 1
        // where q is a safe prime
        let (p, q, alpha) = get_parameters();

        GroupSpec { p, q, alpha }
        // GroupSpec {
        //     p: NonZero::new(Nat::from_u16(23)).unwrap(),
        //     q: NonZero::new(Nat::from_u16(11)).unwrap(),
        //     alpha: Nat::from_u16(2),
        // }
    }

    /// Returns a random from Zq
    pub fn rand_exp(&self) -> Nat {
        Nat::random_mod(&mut OsRng, &self.q)
    }
}

// Generate a safe prime p = 2q + 1, where q is also a safe prime
// and a generator alpha of Zp*
fn get_parameters() -> (
    NonZero<crypto_bigint::Uint<4>>,
    NonZero<crypto_bigint::Uint<4>>,
    crypto_bigint::Uint<4>,
) {
    let (p, q) = generate_safe_primes();
    let alpha = generate_group_generator(p, q);
    (p, q, alpha)
}

// Generate a generator of Zp* using rejection sampling
fn generate_group_generator(
    p: NonZero<crypto_bigint::Uint<4>>,
    q: NonZero<crypto_bigint::Uint<4>>,
) -> crypto_bigint::Uint<4> {
    let mut x = Nat::random_mod(&mut OsRng, &p);
    // While x^q mod p != 1 try with a new random x
    while pow_mod(&x, &q, &p) != Nat::ONE {
        x = Nat::random_mod(&mut OsRng, &p);
    }

    x
}

// Generate a safe prime p = 2q + 1, where q is also a safe prime
fn generate_safe_primes() -> (
    NonZero<crypto_bigint::Uint<4>>,
    NonZero<crypto_bigint::Uint<4>>,
) {
    let p: NonZero<crypto_bigint::Uint<4>> =
        NonZero::new(generate_safe_prime(Option::None)).unwrap();
    let qinit: crypto_bigint::Uint<4> = p
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

// Test for alpha being a generator of Zp*
#[cfg(test)]
mod tests {
    use super::*;
    use crate::nat::pow_mod;

    #[test]
    fn test_generator_from_safe_prime() {
        let group = GroupSpec::new();
        let alpha = group.alpha;
        let raised = pow_mod(&alpha, &group.q, &group.p);

        assert_eq!(raised, Nat::ONE)
    }
}
