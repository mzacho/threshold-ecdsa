use crate::node::Node;
use std::ops::{BitAnd, BitXor};


#[derive(Debug, Clone, Copy)]
pub struct Shares {
    pub x: bool, // todo: Nat
    pub y: bool, // todo: Nat
}

impl Shares {
    pub fn xor(&self, c: bool) -> Shares {
        Shares {
            x: self.x ^ c,
            y: self.y,
        }
    }

    pub fn and(&self, c: bool) -> Shares {
        Shares {
            x: self.x & c,
            y: self.y & c,
        }
    }

    // Reconstruct the secret from the shares
    pub fn val(&self) -> bool {
        self.x ^ self.y
    }

    pub fn as_in_node(&self) -> Node {
        Node::in_(*self)
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
        Shares { x: true, y: true }
    }
}
