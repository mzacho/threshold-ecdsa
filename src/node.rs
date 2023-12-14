use crypto_bigint::NonZero;
use getrandom::getrandom;
use std::cell::RefCell;

use crate::{
    curve::Point,
    nat::Nat,
    shares::{NatShares, Shares},
};

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
    Literal(ConstLiteral),
    Var(usize),
    MUL(usize, usize),
}

#[derive(Debug, Clone)]
pub enum ConstLiteral {
    Nat(Nat),
    Point(Point),
}

impl ConstLiteral {
    pub fn nat(self) -> Nat {
        if let Self::Nat(n) = self {
            n
        } else {
            panic!("not a nat")
        }
    }

    pub fn point(self) -> Point {
        if let Self::Point(p) = self {
            p
        } else {
            panic!("not a point")
        }
    }
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

    pub fn in_nat(s: NatShares) -> Self {
        Node {
            value: RefCell::new(Some(Shares::Nat(s))),
            ..Node::default()
        }
    }

    // pub fn in_point(s: PointShares) -> Self {
    //     Node {
    //         value: RefCell::new(Some(Shares::Point(s))),
    //         ..Node::default()
    //     }
    // }
}

/// Converts an array of boolean values, representing the
/// input of Alice or Bob, into input nodes, to be used in
/// the boolean circuit.
#[allow(dead_code)]
pub fn as_nodes(arr: [Nat; 3], modulus: NonZero<Nat>) -> [Node; 3] {
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

        let s = NatShares::from(r.clone().add_mod(b, &modulus), r, modulus);

        *nodes[i].value.borrow_mut() = Some(Shares::Nat(s));
    }
    nodes
}

/// --------------- tests ----------------

#[cfg(test)]
mod tests {

    use crypto_bigint::NonZero;

    use crate::{
        circuit::{deal_rands, push_node, Circuit, Rands},
        nat::{mul_mod, Nat},
        node::{Const, Node},
        shares::NatShares,
    };

    use super::ConstLiteral;

    fn single_mul_gate(x: Node, y: Node) -> Circuit {
        let modulus = x.value.borrow().as_ref().unwrap().clone().nat().m;
        let mut g: Circuit = Circuit {
            nodes: vec![],
            modulus,
        };

        let xa_id = push_node(&mut g, x);
        let ya_id = push_node(&mut g, y);

        let and = Node::mul(xa_id, ya_id);
        let _ = push_node(&mut g, and);
        g
    }

    fn and_xor_unary_one(x: Node, y: Node) -> Circuit {
        let modulus = x.value.borrow().as_ref().unwrap().clone().nat().m;
        let mut g: Circuit = Circuit {
            nodes: vec![],
            modulus,
        };

        let xa_id = push_node(&mut g, x);
        let ya_id = push_node(&mut g, y);

        let and = Node::mul(xa_id, ya_id);
        let and_id = push_node(&mut g, and);

        let xor = Node::add_unary(and_id, Const::Literal(ConstLiteral::Nat(Nat::from(1u32))));
        push_node(&mut g, xor);
        g
    }

    fn and_and(x: Node, y: Node) -> Circuit {
        let modulus = x.value.borrow().as_ref().unwrap().clone().nat().m;
        let mut g: Circuit = Circuit {
            nodes: vec![],
            modulus,
        };

        let xa_id = push_node(&mut g, x);
        let ya_id = push_node(&mut g, y);

        let and = Node::mul(xa_id, ya_id);
        let and_id = push_node(&mut g, and);

        let and = Node::mul(and_id, ya_id);
        let _ = push_node(&mut g, and);
        g
    }

    fn x_plus_y_times_x_plus_1(x: Node, y: Node) -> Circuit {
        let modulus = x.value.borrow().as_ref().unwrap().clone().nat().m;
        let mut g: Circuit = Circuit {
            nodes: vec![],
            modulus,
        };

        let xa_id = push_node(&mut g, x);
        let ya_id = push_node(&mut g, y);

        let xor = Node::add(xa_id, ya_id);
        let xor_id = push_node(&mut g, xor);

        let and = Node::mul(xa_id, xor_id);
        let and_id = push_node(&mut g, and);

        let xor = Node::add_unary(and_id, Const::Literal(ConstLiteral::Nat(Nat::from(1u32))));
        push_node(&mut g, xor);
        g
    }

    #[test]
    fn test_transform_and_gates1() {
        // input gates

        for _ in 0..100 {
            [Nat::ONE, Nat::ZERO].into_iter().for_each(|b1: Nat| {
                [Nat::ONE, Nat::ZERO].into_iter().for_each(|b2: Nat| {
                    [Nat::ONE, Nat::ZERO].into_iter().for_each(|b3: Nat| {
                        for b4 in [Nat::ONE, Nat::ZERO] {
                            let m = NonZero::new(Nat::from(3_u32)).unwrap();
                            let x: NatShares = NatShares::from(b1.clone(), b2.clone(), m.clone());
                            let y: NatShares = NatShares::from(b3.clone(), b4, m.clone());

                            let mut g: Circuit =
                                single_mul_gate(Node::in_nat(x.clone()), Node::in_nat(y.clone()));
                            g.transform_mul_gates();
                            let res = g.eval();
                            assert_eq!(res.open().nat(), mul_mod(&x.open(), &y.open(), &m));
                        }
                    });
                });
            });
        }
    }

    #[test]
    fn test_transform_and_gates2() {
        // input gates

        for _ in 0..100 {
            [Nat::ONE, Nat::ZERO].into_iter().for_each(|b1: Nat| {
                [Nat::ONE, Nat::ZERO].into_iter().for_each(|b2: Nat| {
                    [Nat::ONE, Nat::ZERO].into_iter().for_each(|b3: Nat| {
                        for b4 in [Nat::ONE, Nat::ZERO] {
                            let m = NonZero::new(Nat::from(3_u32)).unwrap();
                            let x: NatShares = NatShares::from(b1.clone(), b2.clone(), m.clone());
                            let y: NatShares = NatShares::from(b3.clone(), b4, m.clone());

                            let mut g =
                                and_xor_unary_one(Node::in_nat(x.clone()), Node::in_nat(y.clone()));
                            g.transform_mul_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open().nat(),
                                mul_mod(&x.open(), &y.open(), &m).add_mod(&Nat::from(1u32), &m)
                            );
                        }
                    });
                });
            });
        }
    }

    #[test]
    fn test_transform_and_gates3() {
        // input gates

        for _ in 0..100 {
            [Nat::ONE, Nat::ZERO].into_iter().for_each(|b1: Nat| {
                [Nat::ONE, Nat::ZERO].into_iter().for_each(|b2: Nat| {
                    [Nat::ONE, Nat::ZERO].into_iter().for_each(|b3: Nat| {
                        for b4 in [Nat::ONE, Nat::ZERO] {
                            let m = NonZero::new(Nat::from(3_u32)).unwrap();
                            let x: NatShares = NatShares::from(b1.clone(), b2.clone(), m.clone());
                            let y: NatShares = NatShares::from(b3.clone(), b4, m.clone());

                            let mut g = x_plus_y_times_x_plus_1(
                                Node::in_nat(x.clone()),
                                Node::in_nat(y.clone()),
                            );
                            g.transform_mul_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open().nat(),
                                (mul_mod(&x.clone().open().add_mod(&y.open(), &m), &x.open(), &m))
                                    .add_mod(&Nat::from(1_u32), &m)
                            );
                        }
                    });
                });
            });
        }
    }

    #[test]
    fn test_transform_and_gates4() {
        // input gates

        for _ in 0..100 {
            [Nat::ONE, Nat::ZERO].into_iter().for_each(|b1: Nat| {
                [Nat::ONE, Nat::ZERO].into_iter().for_each(|b2: Nat| {
                    [Nat::ONE, Nat::ZERO].into_iter().for_each(|b3: Nat| {
                        for b4 in [Nat::ONE, Nat::ZERO] {
                            let m = NonZero::new(Nat::from(3_u32)).unwrap();
                            let x: NatShares = NatShares::from(b1.clone(), b2.clone(), m.clone());
                            let y: NatShares = NatShares::from(b3.clone(), b4, m.clone());

                            let mut g = x_plus_y_times_x_plus_1(
                                Node::in_nat(x.clone()),
                                Node::in_nat(y.clone()),
                            );
                            g.transform_mul_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open().nat(),
                                (mul_mod(&x.clone().open().add_mod(&y.open(), &m), &x.open(), &m)
                                    .add_mod(&Nat::from(1u32), &m))
                            );
                        }
                    });
                });
            });
        }
    }

    #[test]
    fn test_transform_and_gates5() {
        // input gates

        for _ in 0..100 {
            [Nat::ONE, Nat::ZERO].into_iter().for_each(|b1: Nat| {
                [Nat::ONE, Nat::ZERO].into_iter().for_each(|b2: Nat| {
                    [Nat::ONE, Nat::ZERO].into_iter().for_each(|b3: Nat| {
                        for b4 in [Nat::ONE, Nat::ZERO] {
                            let m = NonZero::new(Nat::from(3_u32)).unwrap();
                            let x: NatShares = NatShares::from(b1.clone(), b2.clone(), m.clone());
                            let y: NatShares = NatShares::from(b3.clone(), b4, m.clone());

                            let mut g = and_and(Node::in_nat(x.clone()), Node::in_nat(y.clone()));
                            g.transform_mul_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open().nat(),
                                (mul_mod(
                                    &mul_mod(&x.open(), &y.clone().open(), &m),
                                    &y.open(),
                                    &m
                                ))
                            );
                        }
                    });
                });
            });
        }
    }

    #[test]
    fn test_deal_rands() {
        for _ in 0..100 {
            // deal_rands is indeterministic, so run it a lot of times ...
            let modulus = NonZero::new(Nat::from_u32(1337)).unwrap();
            let Rands { u, v, w } = deal_rands(&modulus);
            assert_eq!(mul_mod(&u.open(), &v.open(), &modulus), w.open());
        }
    }
}
