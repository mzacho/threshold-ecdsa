use core::ops::{Add, Mul};
use lazy_static::lazy_static;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;

use crate::node::Node;

// BigUint cannot be declared as a const due to non-const fun-call,
// the crate lazy_static provides a way to get the same behaviour
// by allocating it at runtime instead.
lazy_static! {
    pub static ref M: BigUint = BigUint::from(153_u32);
}

#[derive(Debug, Clone)]
pub struct Shares {
    pub x: BigUint,
    pub y: BigUint,
}

impl Shares {
    /// Instantiate a new share with the given `x` and `y` values
    pub fn new(x: BigUint, y: BigUint) -> Self {
        Shares { x, y }
    }

    /// Reconstruct the secret from the shares
    pub fn open(self) -> BigUint {
        (self.x + self.y).mod_floor(&M)
    }

    /// Transform Shares to input Node
    pub fn as_in_node(self) -> Node {
        Node::in_(self)
    }
}

impl Add for Shares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Shares::new(self.x + rhs.x, self.y + rhs.y)
    }
}

impl Add<BigUint> for Shares {
    type Output = Self;

    fn add(self, rhs: BigUint) -> Self::Output {
        Shares::new(self.x + rhs, self.y)
    }
}

impl Mul<BigUint> for Shares {
    type Output = Self;

    fn mul(self, rhs: BigUint) -> Self::Output {
        Shares::new(self.x * &rhs, self.y * rhs)
    }
}

// impl BitAnd<&BigUint> for &Shares {
//     type Output = Shares;

//     fn bitand(self, rhs: &BigUint) -> Self::Output {
//         self.mult(rhs)
//     }
// }

impl Default for Shares {
    fn default() -> Self {
        Shares {
            x: One::one(),
            y: One::one(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use num_bigint::RandBigInt;

    /// Create a share of a constant `c`
    /// Precondition: 0 <= c < M
    pub fn create_share(c: &BigUint) -> Shares {
        assert!(c < &M);
        let mut rng = rand::thread_rng();

        // Pick random from Zm
        let x: BigUint = rng.gen_biguint(M.bits()).mod_floor(&M);
        // Compute (c - x) mod m, avoiding underflow if c < x
        let y: BigUint = if c < &x {
            &M.clone() + c - x.clone()
        } else {
            c - x.clone()
        };

        Shares { x, y }
    }

    #[test]
    fn test_shares_create_share() {
        let x = One::one();
        let shares = create_share(&x);

        assert_eq!(shares.open(), x);
    }

    #[test]
    fn test_shares_add() {
        let x = BigUint::from(42_u32);
        let s1 = create_share(&x);

        let y = BigUint::from(120_u32);
        let s2 = create_share(&y);

        let s3 = s1.clone() + x.clone();
        assert_eq!(s3.open(), (x.clone() + x.clone()).mod_floor(&M));
        let s4 = s1.clone() + y.clone();
        assert_eq!(s4.open(), (x.clone() + y.clone()).mod_floor(&M));
        let s5 = s1 + s2;
        assert_eq!(s5.open(), (x + y).mod_floor(&M));
    }

    #[test]
    fn test_shares_mul() {
        let x1 = BigUint::from(0b1010u32).mod_floor(&M);
        let shares1 = create_share(&x1);
        assert_eq!(shares1.clone().open(), (x1.clone()).mod_floor(&M));

        let y = BigUint::from(0b1111u32).mod_floor(&M);

        let mul_share_constant = shares1 * y.clone();
        assert_eq!(mul_share_constant.open(), (x1 * y).mod_floor(&M));
    }
}
