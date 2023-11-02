use num_bigint::BigUint;
use num_traits::One;
use rand::Rng;
use std::ops::{BitAnd, BitXor};

use crate::node::Node;

#[derive(Debug, Clone)]
pub struct Shares {
    pub x: BigUint,
    pub y: BigUint,
}

impl Shares {
    /// Instantiate a new share with the given `x` and `y` values
    pub fn new(x: &BigUint, y: &BigUint) -> Self {
        Shares {
            x: x.clone(),
            y: y.clone(),
        }
    }

    /// Create a share of a constant `c`
    pub fn create_share(c: &BigUint) -> Self {
        let mut rng = rand::thread_rng();

        let x: BigUint = BigUint::from(rng.gen_bool(0.5));
        let y: BigUint = c ^ &x;

        Shares { x, y }
    }

    pub fn xor(&self, c: &BigUint) -> Shares {
        return Shares::new(&(&self.x ^ c), &self.y);
    }

    pub fn and(&self, c: &BigUint) -> Shares {
        return Shares::new(&(&self.x & c), &(&self.y & c));
    }

    // Reconstruct the secret from the shares
    pub fn reconstruct(&self) -> BigUint {
        self.x.clone() ^ self.y.clone()
    }

    pub fn as_in_node(self) -> Node {
        Node::in_(self)
    }
}

impl BitXor<&Shares> for &Shares {
    type Output = Shares;

    fn bitxor(self, rhs: &Shares) -> Self::Output {
        Shares::new(&(&self.x ^ &rhs.x), &(&self.y ^ &rhs.y))
    }
}

impl BitXor<&BigUint> for &Shares {
    type Output = Shares;

    fn bitxor(self, rhs: &BigUint) -> Self::Output {
        self.xor(&rhs)
    }
}

impl BitAnd<&BigUint> for &Shares {
    type Output = Shares;

    fn bitand(self, rhs: &BigUint) -> Self::Output {
        self.and(&rhs)
    }
}

impl Default for Shares {
    fn default() -> Self {
        Shares {
            x: One::one(),
            y: One::one(),
        }
    }
}

// TODO: Implement Mul and BitAnd for Shares here?

#[cfg(test)]
mod test {
    use num_traits::Zero;

    use super::*;

    #[test]
    fn test_shares_create_share() {
        let x = One::one();
        let shares = Shares::create_share(&x);

        assert_eq!(shares.reconstruct(), x);
    }

    #[test]
    fn test_shares_xor() {
        let one = One::one();
        let shares1 = Shares::create_share(&one);

        let zero = Zero::zero();
        let shares2 = Shares::create_share(&zero);

        let xor_share_constant_1 = &shares1 ^ &one;
        assert_eq!(xor_share_constant_1.reconstruct(), &one ^ &one);

        let xor_share_constant_0 = &shares1 ^ &zero;
        assert_eq!(xor_share_constant_0.reconstruct(), &one ^ &zero);

        let xor_share = &shares1 ^ &shares2;
        assert_eq!(xor_share.reconstruct(), &one ^ zero);
    }

    #[test]
    fn test_shares_and() {
        let x1 = BigUint::from(0b1010u32);
        let shares1 = Shares::create_share(&x1);

        let y = BigUint::from(0b1111u32);

        let and_share_constant = &shares1 & &y;
        assert_eq!(and_share_constant.reconstruct(), &x1 & &y);
    }
}
