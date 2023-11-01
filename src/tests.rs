use crate::circuit::{Rands, deal_rands};

// --------------- tests ----------------
use super::*;

fn single_and_gate(x: Node, y: Node) -> Circuit {
    let mut g: Circuit = Circuit { nodes: vec![] };

    let xa_id = push_node(&mut g, x);
    let ya_id = push_node(&mut g, y);

    let and = Node::and(xa_id, ya_id);
    let _ = push_node(&mut g, and);
    g
}

fn and_xor_unary_one(x: Node, y: Node) -> Circuit {
    let mut g: Circuit = Circuit { nodes: vec![] };

    let xa_id = push_node(&mut g, x);
    let ya_id = push_node(&mut g, y);

    let and = Node::and(xa_id, ya_id);
    let and_id = push_node(&mut g, and);

    let xor = Node::xor_unary(and_id, Const::Literal(true));
    push_node(&mut g, xor);
    g
}

fn and_and(x: Node, y: Node) -> Circuit {
    let mut g: Circuit = Circuit { nodes: vec![] };

    let xa_id = push_node(&mut g, x);
    let ya_id = push_node(&mut g, y);

    let and = Node::and(xa_id, ya_id);
    let and_id = push_node(&mut g, and);

    let and = Node::and(and_id, ya_id);
    let _ = push_node(&mut g, and);

    //let xor = Node::xor_unary(and_id, Const::Literal(true));
    //push_node(&mut g, xor);
    g
}

fn xor_and_xor(x: Node, y: Node) -> Circuit {
    let mut g: Circuit = Circuit { nodes: vec![] };

    let xa_id = push_node(&mut g, x);
    let ya_id = push_node(&mut g, y);

    let xor = Node::xor(xa_id, ya_id);
    let xor_id = push_node(&mut g, xor);

    let and = Node::and(xa_id, xor_id);
    let and_id = push_node(&mut g, and);

    let xor = Node::xor_unary(and_id, Const::Literal(true));
    push_node(&mut g, xor);
    g
}

#[test]
fn test_transform_and_gates1() {
    // input gates

    for _ in 0..100 {
        for b1 in [true, false] {
            for b2 in [true, false] {
                for b3 in [true, false] {
                    for b4 in [true, false] {
                        let x = Shares { x: b1, y: b2 };
                        let y = Shares { x: b3, y: b4 };

                        let mut g: Circuit = single_and_gate(Node::in_(x), Node::in_(y));
                        g.transform_and_gates();
                        let res = g.eval();
                        assert_eq!(res.val(), x.val() & y.val());
                    }
                }
            }
        }
    }
}

#[test]
fn test_transform_and_gates2() {
    // input gates

    for _ in 0..100 {
        for b1 in [true, false] {
            for b2 in [true, false] {
                for b3 in [true, false] {
                    for b4 in [true, false] {
                        let x = Shares { x: b1, y: b2 };
                        let y = Shares { x: b3, y: b4 };

                        let mut g = and_xor_unary_one(Node::in_(x), Node::in_(y));
                        g.transform_and_gates();
                        let res = g.eval();
                        assert_eq!(res.val(), (x.val() & y.val()) ^ true);
                    }
                }
            }
        }
    }
}

#[test]
fn test_transform_and_gates3() {
    // input gates

    for _ in 0..100 {
        for b1 in [true, false] {
            for b2 in [true, false] {
                for b3 in [true, false] {
                    for b4 in [true, false] {
                        let x = Shares { x: b1, y: b2 };
                        let y = Shares { x: b3, y: b4 };

                        let mut g = xor_and_xor(Node::in_(x), Node::in_(y));
                        g.transform_and_gates();
                        let res = g.eval();
                        assert_eq!(res.val(), ((x.val() ^ y.val()) & x.val()) ^ true);
                    }
                }
            }
        }
    }
}

#[test]
fn test_transform_and_gates4() {
    // input gates

    for _ in 0..100 {
        for b1 in [true, false] {
            for b2 in [true, false] {
                for b3 in [true, false] {
                    for b4 in [true, false] {
                        let x = Shares { x: b1, y: b2 };
                        let y = Shares { x: b3, y: b4 };

                        let mut g = xor_and_xor(Node::in_(x), Node::in_(y));
                        g.transform_and_gates();
                        let res = g.eval();
                        assert_eq!(res.val(), ((x.val() ^ y.val()) & x.val()) ^ true);
                    }
                }
            }
        }
    }
}

#[test]
fn test_transform_and_gates5() {
    // input gates

    for _ in 0..100 {
        for b1 in [true, false] {
            for b2 in [true, false] {
                for b3 in [true, false] {
                    for b4 in [true, false] {
                        let x = Shares { x: b1, y: b2 };
                        let y = Shares { x: b3, y: b4 };

                        let mut g = and_and(Node::in_(x), Node::in_(y));
                        g.transform_and_gates();
                        let res = g.eval();
                        assert_eq!(res.val(), ((x.val() & y.val()) & y.val()));
                    }
                }
            }
        }
    }
}

fn test_bedoza_helper(x: &str, y: &str, expectation: bool) {
    let (in_alice, in_bob) = str_to_nodes(x, y);
    let mut g: Circuit = init_circuit(in_alice, in_bob);
    g.transform_and_gates();
    let res = g.eval();
    assert_eq!(res.val(), expectation);
}

#[test]
fn test_bedoza() {
    let minus = ["AB-", "A-", "B-", "o-"];
    let plus = ["AB+", "A+", "B+", "o+"];

    for x in [minus, plus].concat() {
        test_bedoza_helper(x, x, true);
    }

    for i in 0..4 {
        test_bedoza_helper(plus[i], minus[i], true);
        test_bedoza_helper(minus[i], plus[i], false);
    }

    for i in 1..4 {
        test_bedoza_helper(plus[0], plus[i], true);
        test_bedoza_helper(minus[0], minus[i], true);
        test_bedoza_helper(plus[0], minus[i], true);
    }

    for i in 0..4 {
        for j in (i + 1)..4 {
            test_bedoza_helper(plus[j], plus[i], false);
            test_bedoza_helper(minus[j], plus[i], false);
            test_bedoza_helper(minus[j], minus[i], false);
            test_bedoza_helper(plus[j], minus[i], false);
        }
    }

    for i in 1..3 {
        test_bedoza_helper(plus[3], plus[i], false);
        test_bedoza_helper(minus[3], minus[i], false);
        test_bedoza_helper(plus[3], minus[i], false);
    }
}

#[test]
fn test_deal_rands() {
    for _ in 0..100 {
        // deal_rands is indeterministic, so run it a lot of times ...
        let Rands { u, v, w } = deal_rands();
        assert_eq!(u.val() & v.val(), w.val());
    }
}

