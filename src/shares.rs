use core::ops::{Add, Mul};
use crypto_bigint::{rand_core::OsRng, NonZero, RandomMod};
use elliptic_curve::ops::MulByGenerator;
use elliptic_curve::scalar::FromUintUnchecked;

use crate::{
    curve::{Point, Scalar},
    nat::{mul_mod, Nat},
    node::{ConstLiteral, Node},
};

#[derive(Debug, Clone)]
pub enum Shares {
    Nat(NatShares),
    Point(PointShares),
}

impl Shares {
    pub fn nat(self) -> NatShares {
        if let Self::Nat(s) = self {
            s
        } else {
            panic!("not a nat")
        }
    }

    // pub fn point(self) -> CurveShares {
    //     if let Self::Curve(s) = self {
    //         s
    //     } else {
    //         panic!("not a point")
    //     }
    // }

    /// Reconstruct the secret from the shares
    pub fn open(self) -> ConstLiteral {
        match self {
            Shares::Nat(self_) => ConstLiteral::Nat(self_.x.add_mod(&self_.y, &self_.m)),
            Shares::Point(self_) => ConstLiteral::Point(self_.x + &self_.y),
        }
    }
}

/// An additive share [s] = (x, y) where x + y mod M = s
#[derive(Debug, Clone)]
pub struct NatShares {
    pub x: Nat,
    pub y: Nat,
    pub m: NonZero<Nat>,
}

impl NatShares {
    /// Instantiate a new share with the given `x` and `y` values
    pub fn from(x: Nat, y: Nat, m: NonZero<Nat>) -> Self {
        NatShares { x, y, m }
    }

    /// Create a share of a constant `c`
    /// Precondition: 0 <= c < m
    pub fn new(c: &Nat, m: NonZero<Nat>) -> NatShares {
        assert!(c < &m);

        // Pick random from Zm
        let x: Nat = Nat::random_mod(&mut OsRng, &m);
        // Compute (c - x) mod m, avoiding underflow if c < x
        let y: Nat = if c < &x {
            m.add_mod(c, &m).sub_mod(&x, &m)
        } else {
            c.sub_mod(&x, &m)
        };

        NatShares { x, y, m }
    }

    /// Transform Shares to input Node
    pub fn as_in_node(self) -> Node {
        Node::in_nat(self)
    }

    /// Reconstruct the secret from the shares
    pub fn open(self) -> Nat {
        self.x.add_mod(&self.y, &self.m)
    }
}

impl Add for Shares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Shares::Nat(self_), Shares::Nat(rhs)) => Shares::Nat(self_ + rhs),
            (Shares::Point(self_), Shares::Point(rhs)) => Shares::Point(self_ + rhs),
            _ => panic!("cannot add shares of differet types"),
        }
    }
}

impl Add for NatShares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert!(self.m == rhs.m);
        NatShares::from(
            self.x.add_mod(&rhs.x, &self.m),
            self.y.add_mod(&rhs.y, &self.m),
            self.m,
        )
    }
}

impl Add<Nat> for NatShares {
    type Output = Self;

    fn add(self, rhs: Nat) -> Self::Output {
        NatShares::from(self.x.add_mod(&rhs, &self.m), self.y, self.m)
    }
}

impl Mul<Nat> for NatShares {
    type Output = Self;

    fn mul(self, rhs: Nat) -> Self::Output {
        NatShares::from(
            mul_mod(&self.x, &rhs, &self.m),
            mul_mod(&self.y, &rhs, &self.m),
            self.m,
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct PointShares {
    pub x: Point,
    pub y: Point,
}

impl PointShares {
    /// Convert shares of a value "a" to a share of the
    /// representation of the point on the curve for the
    /// value "a"
    pub fn from(s: NatShares) -> Self {
        let x = Scalar::from_uint_unchecked(s.x);
        let y = Scalar::from_uint_unchecked(s.y);

        let xi = Point::mul_by_generator(&x);
        let yi = Point::mul_by_generator(&y);

        PointShares { x: xi, y: yi }
    }
}

impl Add for PointShares {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        PointShares {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

impl Add<Scalar> for PointShares {
    type Output = Self;

    fn add(self, _: Scalar) -> Self::Output {
        todo!() // don't know if we need this?
    }
}

impl Mul<Scalar> for PointShares {
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self::Output {
        PointShares {
            x: self.x * rhs,
            y: self.y * rhs,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{curve::ORDER, nat::mul_mod};

    #[test]
    fn test_shares_new() {
        let m = NonZero::new(Nat::from(1337_u128)).unwrap();
        let x = Nat::new(Nat::ONE.into());
        let shares = NatShares::new(&x, m);

        assert_eq!(shares.open(), x);
    }

    #[test]
    fn test_shares_add() {
        let m = NonZero::new(Nat::from(150_u128)).unwrap();
        let x = Nat::from(42_u32);
        let s1 = NatShares::new(&x, m.clone());

        let y = Nat::from(120_u32);
        let s2 = NatShares::new(&y, m.clone());

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
        let shares = NatShares::new(&x, m.clone());
        assert_eq!(shares.clone().open(), x);

        let y = Nat::from_u32(13);

        let mul_share_constant = shares * y.clone();
        assert_eq!(mul_share_constant.open(), mul_mod(&y, &x, &m));
    }

    /// Test that Convert([a] + [b])
    ///         = Convert([a]) + Convert([b])
    ///
    /// test with a small modulus, the sum is not reduced
    #[test]
    fn test_add_shares_is_homomorphic_wrt_convert_to_curve1() {
        let m = NonZero::new(Nat::from(522_u128)).unwrap();
        let s1 = NatShares {
            x: Nat::from(426_u32),
            y: Nat::from(42_u32),
            m,
        };

        let s2 = NatShares {
            x: Nat::from(12_u32),
            y: Nat::from(266_u32),
            m,
        };

        let s1c = PointShares::from(s1.clone());
        let s2c = PointShares::from(s2.clone());

        assert_eq!(s1c + s2c, PointShares::from(s1 + s2));
    }

    /// test where the modulus is the actual order of the curve
    /// and the shares are generated at random
    #[test]
    fn test_add_shares_is_homomorphic_wrt_convert_to_curve2() {
        let m = NonZero::new(ORDER).unwrap();
        let s1 = NatShares::new(&Nat::from_u8(13_u8), m);
        let s2 = NatShares::new(&Nat::from_u8(42_u8), m);

        let s1c = PointShares::from(s1.clone());
        let s2c = PointShares::from(s2.clone());

        assert_eq!(s1c + s2c, PointShares::from(s1 + s2));
    }
}
