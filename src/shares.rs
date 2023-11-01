use num_bigint::BigUint;
use num_traits::One;
use std::ops::{BitAnd, BitXor};

use crate::node::Node;

#[derive(Debug, Clone)]
pub struct Shares {
    pub x: BigUint,
    pub y: BigUint,
}

impl Shares {
    pub fn xor(&self, c: BigUint) -> Shares {
        Shares {
            x: self.x ^ c,
            y: self.y,
        }
    }

    pub fn and(&self, c: BigUint) -> Shares {
        Shares {
            x: self.x & c,
            y: self.y & c,
        }
    }

    // Reconstruct the secret from the shares
    pub fn val(&self) -> BigUint {
        self.x ^ self.y
    }

    pub fn as_in_node(self) -> Node {
        Node::in_(self)
    }
}

impl BitAnd for Shares {
    type Output = Shares;

    fn bitand(self, rhs: Self) -> Self::Output {
        Shares {
            x: self.x & rhs.x,
            y: self.y & rhs.y,
        }
    }
}

impl BitXor for Shares {
    type Output = Shares;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Shares {
            x: self.x ^ rhs.x,
            y: self.y ^ rhs.y,
        }
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
