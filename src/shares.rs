use core::ops::{Add, Mul};
use lazy_static::lazy_static;
use crypto_bigint::{U64, Limb, NonZero};

use crate::node::Node;

/// Natural numbers represented as cryptographically safe big unsigned
/// integers. Arithmetic operations are checked for overflow at run-time
pub type Nat = U64;

/// Computes `lhs * rhs mod M` in constant time for the special modulus
/// `M = MAX+1-c` where `c` is small enough to fit in a single [`Limb`],
/// see the documentation for crypto_bigint::mul_mod_special.
pub fn mul_mod(lhs: &Nat, rhs: &Nat) -> Nat {
    let c = 18446744073709428953;
    lhs.mul_mod_special(rhs, Limb(c))
}

// BigUint cannot be declared as a const due to non-const fun-call,
// the crate lazy_static provides a way to get the same behaviour
// by allocating it at runtime instead.
lazy_static! {
    pub static ref M: NonZero<Nat> = NonZero::new(Nat::from(122663_u32)).unwrap();
}

/// An additive share [s] = (x, y) where x + y mod M = s
#[derive(Debug, Clone)]
pub struct Shares {
    pub x: Nat,
    pub y: Nat,
}

impl Shares {
    /// Instantiate a new share with the given `x` and `y` values
    pub fn new(x: Nat, y: Nat) -> Self {
        Shares { x, y }
    }

    /// Reconstruct the secret from the shares
    pub fn open(self) -> Nat {
        self.x.add_mod(&self.y, &M)
    }

    /// Transform Shares to input Node
    pub fn as_in_node(self) -> Node {
        Node::in_(self)
    }
}

impl Add for Shares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Shares::new(self.x.add_mod(&rhs.x, &M),
                    self.y.add_mod(&rhs.y, &M))
    }
}

impl Add<Nat> for Shares {
    type Output = Self;

    fn add(self, rhs: Nat) -> Self::Output {
        Shares::new(self.x.add_mod(&rhs, &M), self.y)
    }
}

impl Mul<Nat> for Shares {
    type Output = Self;

    fn mul(self, rhs: Nat) -> Self::Output {
        Shares::new(mul_mod(&self.x, &rhs), mul_mod(&self.y , &rhs))
    }
}

// impl BitAnd<&Nat> for &Shares {
//     type Output = Shares;

//     fn bitand(self, rhs: &Nat) -> Self::Output {
//         self.mult(rhs)
//     }
// }

impl Default for Shares {
    fn default() -> Self {
        Shares {
            x: Nat::new(Nat::ONE.into()),
            y: Nat::new(Nat::ONE.into()),
        }
    }
}

#[cfg(test)]
mod test {
    use crypto_bigint::{RandomMod, rand_core::OsRng};

    use super::*;

    /// Create a share of a constant `c`
    /// Precondition: 0 <= c < M
    pub fn create_share(c: &Nat) -> Shares {
        assert!(c < &M);

        // Pick random from Zm
        let x: Nat = Nat::random_mod(&mut OsRng, &M);
        // Compute (c - x) mod m, avoiding underflow if c < x
        let y: Nat = if c < &x {
            M.add_mod(c, &M).sub_mod(&x, &M)
        } else {
            c.sub_mod(&x, &M)
        };

        Shares { x, y }
    }

    #[test]
    fn test_shares_create_share() {
        let x = Nat::new(Nat::ONE.into());
        let shares = create_share(&x);

        assert_eq!(shares.open(), x);
    }

    #[test]
    fn test_shares_add() {
        let x = Nat::from(42_u32);
        let s1 = create_share(&x);

        let y = Nat::from(120_u32);
        let s2 = create_share(&y);


        let s3 = s1.clone() + x.clone();
        assert_eq!(s3.open(), x.add_mod(&x, &M));
        let s4 = s1.clone() + y.clone();
        assert_eq!(s4.open(), x.add_mod(&y, &M));
        let s5 = s1 + s2;
        assert_eq!(s5.open(), x.add_mod(&y, &M));
    }

    #[test]
    fn test_shares_mul() {
        let x1 = Nat::from(0b1010u32).add_mod(&Nat::ONE, &M);
        let shares1 = create_share(&x1);
        assert_eq!(shares1.clone().open(), x1);

        let y = Nat::from(0b1111u32).add_mod(&Nat::ONE, &M);

        let mul_share_constant = shares1 * y.clone();
        assert_eq!(mul_share_constant.open(), mul_mod(&y, &x1));
    }
}
