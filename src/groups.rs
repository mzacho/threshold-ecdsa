use crypto_bigint::{rand_core::OsRng, NonZero, RandomMod};

use crate::nat::{mul_mod, Nat};
use crypto_primes::generate_safe_prime;

/// A specification of the subgroup from Zp of prime order q,
/// where p is a safe prime with associated Sofie Germain prime q
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

        GroupSpec {
            p: NonZero::new(p).unwrap(),
            q,
            alpha,
        }
    }

    /// Returns a random from Zq
    pub fn rand_exp(&self) -> Nat {
        Nat::random_mod(&mut OsRng, &self.q)
    }
}

// Generate a safe prime p = 2q + 1, where q is also a safe prime
// and a generator alpha of Zp*
fn get_parameters() -> (
    crypto_bigint::Uint<4>,
    NonZero<crypto_bigint::Uint<4>>,
    crypto_bigint::Uint<4>,
) {
    let (p, q) = generate_safe_primes();
    let alpha = generate_group_generator(q, p);
    (p, q, alpha)
}

// Generate a generator of Zp*
fn generate_group_generator(
    q: NonZero<crypto_bigint::Uint<4>>,
    p: crypto_bigint::Uint<4>,
) -> crypto_bigint::Uint<4> {
    let mut x = Nat::random_mod(&mut OsRng, &q);
    while x == Nat::ONE {
        x = Nat::random_mod(&mut OsRng, &q);
    }

    mul_mod(&x, &x, &p)
}

// Generate a safe prime p = 2q + 1, where q is also a safe prime
fn generate_safe_primes() -> (crypto_bigint::Uint<4>, NonZero<crypto_bigint::Uint<4>>) {
    let p: crypto_bigint::Uint<4> = generate_safe_prime(Option::None);
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
