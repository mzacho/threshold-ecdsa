use getrandom::getrandom;
use std::cell::RefCell;

use crate::shares::{Shares, Nat};

#[derive(Debug, Clone)]
pub enum Gate {
    In,
    AddUnary(Const),
    MulUnary(Const),
    Mul,
    Add,
    Open,
}

#[derive(Debug, Clone)]
pub enum Const {
    Literal(Nat),
    Var(usize),
    MUL(usize, usize),
}

pub type NodeId = usize;

/// `Node` represents a node in the BeDOZa circuit.
///
/// Its function is determined by the value of the `op` operation.
/// It contains a `value`, which can be `None` or `Some` of `Shares`.
/// During evaluation.
///
/// Input nodes whose `op` is `In` are created with a `value` of `Some`.
/// `Mul`, `Add`, `AddUnary(Const)` and `MulUnary(Const)` are created with
/// a `value` of `None`, which changes to `Some` during evaluation.
/// `Open` nodes always have a `value` of `None`, even after evaluation.
/// Their value is inserted into the environment of the `Circuit` during
/// evaluation.
#[derive(Debug, Clone)]
pub struct Node {
    pub in_1: Option<NodeId>,
    pub in_2: Option<NodeId>,
    pub op: Gate,
    pub value: RefCell<Option<Shares>>,
}

/// Default nodes are inputs
impl Default for Node {
    fn default() -> Self {
        Node {
            in_1: None,
            in_2: None,
            op: Gate::In,
            value: RefCell::new(None),
        }
    }
}

impl Node {
    pub fn mul(pid1: usize, pid2: usize) -> Self {
        Node {
            in_1: Some(pid1),
            in_2: Some(pid2),
            op: Gate::Mul,
            ..Default::default()
        }
    }

    pub fn add(pid1: usize, pid2: usize) -> Self {
        Node {
            in_1: Some(pid1),
            in_2: Some(pid2),
            op: Gate::Add,
            ..Default::default()
        }
    }

    pub fn add_unary(pid1: usize, c: Const) -> Self {
        Node {
            in_1: Some(pid1),
            in_2: None,
            op: Gate::AddUnary(c),
            ..Default::default()
        }
    }

    pub fn mul_unary(pid: usize, c: Const) -> Self {
        Node {
            in_1: Some(pid),
            op: Gate::MulUnary(c),
            ..Default::default()
        }
    }

    pub fn open(pid: usize) -> Self {
        Node {
            in_1: Some(pid),
            op: Gate::Open,
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

/// Converts an array of boolean values, representing the
/// input of Alice or Bob, into input nodes, to be used in
/// the boolean circuit.
pub fn as_nodes(arr: [Nat; 3]) -> [Node; 3] {
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

        let r: Nat = if (buf[0] >> i) % 2 != 0 {
            Nat::ONE
        } else {
            Nat::ZERO
        };

        // Then assign Alices share to r XOR b
        // and Bobs share to r

        let s = Shares::from(r.clone() ^ b, r);

        *nodes[i].value.borrow_mut() = Some(s);
    }
    nodes
}
