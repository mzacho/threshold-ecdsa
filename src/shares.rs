use core::ops::{Add, Mul};
use crypto_bigint::{ rand_core::OsRng, RandomMod};

use crate::{nat::{Nat, M, mul_mod}, node::Node};

/// An additive share [s] = (x, y) where x + y mod M = s
#[derive(Debug, Clone)]
pub struct Shares {
    pub x: Nat,
    pub y: Nat,
}

impl Shares {
    /// Instantiate a new share with the given `x` and `y` values
    pub fn from(x: Nat, y: Nat) -> Self {
        Shares { x, y }
    }

    /// Create a share of a constant `c`
    /// Precondition: 0 <= c < M
    pub fn new(c: &Nat) -> Shares {
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
        Shares::from(self.x.add_mod(&rhs.x, &M), self.y.add_mod(&rhs.y, &M))
    }
}

impl Add<Nat> for Shares {
    type Output = Self;

    fn add(self, rhs: Nat) -> Self::Output {
        Shares::from(self.x.add_mod(&rhs, &M), self.y)
    }
}

impl Mul<Nat> for Shares {
    type Output = Self;

    fn mul(self, rhs: Nat) -> Self::Output {
        Shares::from(mul_mod(&self.x, &rhs, &M), mul_mod(&self.y, &rhs, &M))
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
    use super::*;
    use crate::nat::mul_mod;

    #[test]
    fn test_shares_new() {
        let x = Nat::new(Nat::ONE.into());
        let shares = Shares::new(&x);

        assert_eq!(shares.open(), x);
    }

    #[test]
    fn test_shares_add() {
        let x = Nat::from(42_u32);
        let s1 = Shares::new(&x);

        let y = Nat::from(120_u32);
        let s2 = Shares::new(&y);

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
        let shares1 = Shares::new(&x1);
        assert_eq!(shares1.clone().open(), x1);

        let y = Nat::from(0b1111u32).add_mod(&Nat::ONE, &M);

        let mul_share_constant = shares1 * y.clone();
        assert_eq!(mul_share_constant.open(), mul_mod(&y, &x1, &M));
    }
}
