use core::ops::{Add, Mul};
use crypto_bigint::{rand_core::OsRng, NonZero, RandomMod};
use elliptic_curve::ops::MulByGenerator;
use elliptic_curve::scalar::FromUintUnchecked;

use crate::{
    curve::{Point, Scalar},
    nat::{mul_mod, Nat},
    node::Node,
};

/// An additive share [s] = (x, y) where x + y mod M = s
#[derive(Debug, Clone)]
pub struct Shares {
    pub x: Nat,
    pub y: Nat,
    pub m: NonZero<Nat>,
}

impl Shares {
    /// Instantiate a new share with the given `x` and `y` values
    pub fn from(x: Nat, y: Nat, m: NonZero<Nat>) -> Self {
        Shares { x, y, m }
    }

    /// Create a share of a constant `c`
    /// Precondition: 0 <= c < m
    pub fn new(c: &Nat, m: NonZero<Nat>) -> Shares {
        assert!(c < &m);

        // Pick random from Zm
        let x: Nat = Nat::random_mod(&mut OsRng, &m);
        // Compute (c - x) mod m, avoiding underflow if c < x
        let y: Nat = if c < &x {
            m.add_mod(c, &m).sub_mod(&x, &m)
        } else {
            c.sub_mod(&x, &m)
        };

        Shares { x, y, m }
    }

    /// Reconstruct the secret from the shares
    pub fn open(self) -> Nat {
        self.x.add_mod(&self.y, &self.m)
    }

    /// Transform Shares to input Node
    pub fn as_in_node(self) -> Node {
        Node::in_(self)
    }
}

impl Add for Shares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert!(self.m == rhs.m);
        Shares::from(
            self.x.add_mod(&rhs.x, &self.m),
            self.y.add_mod(&rhs.y, &self.m),
            self.m,
        )
    }
}

impl Add<Nat> for Shares {
    type Output = Self;

    fn add(self, rhs: Nat) -> Self::Output {
        Shares::from(self.x.add_mod(&rhs, &self.m), self.y, self.m)
    }
}

impl Mul<Nat> for Shares {
    type Output = Self;

    fn mul(self, rhs: Nat) -> Self::Output {
        Shares::from(
            mul_mod(&self.x, &rhs, &self.m),
            mul_mod(&self.y, &rhs, &self.m),
            self.m,
        )
    }
}

#[derive(Debug, PartialEq)]
pub struct CurveShares {
    pub x: Point,
    pub y: Point,
}

impl CurveShares {
    /// Convert shares of a value "a" to a share of the
    /// representation of the point on the curve for the
    /// value "a"
    fn from(s: Shares) -> Self {
        let x = Scalar::from_uint_unchecked(s.x);
        let y = Scalar::from_uint_unchecked(s.y);

        let xi = Point::mul_by_generator(&x);
        let yi = Point::mul_by_generator(&y);

        CurveShares { x: xi, y: yi }
    }
}

impl Add for CurveShares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        CurveShares {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl Add<Scalar> for CurveShares {
    type Output = Self;

    fn add(self, rhs: Scalar) -> Self::Output {
        todo!() // don't know if we need this?
    }
}

impl Mul<Scalar> for CurveShares {
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        CurveShares {
            x: self.x * rhs,
            y: self.y * rhs,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::nat::mul_mod;

    #[test]
    fn test_shares_new() {
        let m = NonZero::new(Nat::from(1337_u128)).unwrap();
        let x = Nat::new(Nat::ONE.into());
        let shares = Shares::new(&x, m);

        assert_eq!(shares.open(), x);
    }

    #[test]
    fn test_shares_add() {
        let m = NonZero::new(Nat::from(150_u128)).unwrap();
        let x = Nat::from(42_u32);
        let s1 = Shares::new(&x, m.clone());

        let y = Nat::from(120_u32);
        let s2 = Shares::new(&y, m.clone());

        let s3 = s1.clone() + x.clone();
        assert_eq!(s3.open(), x.add_mod(&x, &m));
        let s4 = s1.clone() + y.clone();
        assert_eq!(s4.open(), x.add_mod(&y, &m));
        let s5 = s1 + s2;
        assert_eq!(s5.open(), x.add_mod(&y, &m));
    }

    #[test]
    fn test_shares_mul() {
        let m = NonZero::new(Nat::from_u32(51)).unwrap();
        let x = Nat::from_u32(43);
        let shares = Shares::new(&x, m.clone());
        assert_eq!(shares.clone().open(), x);

        let y = Nat::from_u32(13);

        let mul_share_constant = shares * y.clone();
        assert_eq!(mul_share_constant.open(), mul_mod(&y, &x, &m));
    }

    /// Test that Convert([a] + [b])
    ///         = Convert([a]) + Convert([b])
    #[test]
    fn test_add_shares_is_homomorphic_wrt_convert_to_curve() {
        let m = NonZero::new(Nat::from(522_u128)).unwrap();
        let x = Nat::from(42_u32);
        let s1 = Shares::new(&x, m.clone());

        let y = Nat::from(120_u32);
        let s2 = Shares::new(&y, m.clone());

        let s1c = CurveShares::from(s1.clone());
        let s2c = CurveShares::from(s2.clone());

        assert_eq!(s1c + s2c, CurveShares::from(s1 + s2));
    }
}
