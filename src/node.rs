use getrandom::getrandom;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::cell::RefCell;

use crate::shares::Shares;

#[derive(Debug, Clone)]
pub enum Gate {
    IN,
    XORUnary(Const),
    ANDUnary(Const),
    AND,
    XOR,
    OPEN,
}

#[derive(Debug, Clone)]
pub enum Const {
    Literal(BigUint),
    Var(usize),
    AND(usize, usize),
}

pub type NodeId = usize;

#[derive(Debug, Clone)]
pub struct Node {
    pub in_1: Option<NodeId>,
    pub in_2: Option<NodeId>,
    pub op: Gate,
    pub value: RefCell<Option<Shares>>,
}

impl Default for Node {
    fn default() -> Self {
        Node {
            in_1: None,
            in_2: None,
            op: Gate::IN,
            value: RefCell::new(None),
        }
    }
}

impl Node {
    pub fn and(pid1: usize, pid2: usize) -> Self {
        Node {
            in_1: Some(pid1),
            in_2: Some(pid2),
            op: Gate::AND,
            ..Default::default()
        }
    }

    pub fn xor(pid1: usize, pid2: usize) -> Self {
        Node {
            in_1: Some(pid1),
            in_2: Some(pid2),
            op: Gate::XOR,
            ..Default::default()
        }
    }

    pub fn xor_unary(pid1: usize, c: Const) -> Self {
        Node {
            in_1: Some(pid1),
            in_2: None,
            op: Gate::XORUnary(c),
            ..Default::default()
        }
    }

    pub fn and_unary(pid: usize, c: Const) -> Self {
        Node {
            in_1: Some(pid),
            op: Gate::ANDUnary(c),
            ..Default::default()
        }
    }

    pub fn open(pid: usize) -> Self {
        Node {
            in_1: Some(pid),
            op: Gate::OPEN,
            ..Default::default()
        }
    }

    pub fn in_(s: Shares) -> Self {
        Node {
            value: RefCell::new(Some(s)),
            ..Node::default()
        }
    }
}

// Converts an array of boolean values, representing the
// input of Alice or Bob, into input nodes, to be used in
// the boolean circuit.
pub fn as_nodes(arr: [BigUint; 3]) -> [Node; 3] {
    // Sample random bits
    let mut buf = [0];
    if let Err(e) = getrandom(&mut buf) {
        panic!("{e}");
    }

    let nodes = [Node::default(), Node::default(), Node::default()];

    for (i, b) in arr.iter().enumerate() {
        // Make new secret share of b
        //
        // First sample a random bit

        let r: BigUint = if (buf[0] >> i) % 2 != 0 {
            One::one()
        } else {
            Zero::zero()
        };

        // Then assign Alices share to r XOR b
        // and Bobs share to r

        let s = Shares::new(r.clone() ^ b, r);

        *nodes[i].value.borrow_mut() = Some(s);
    }
    nodes
}
