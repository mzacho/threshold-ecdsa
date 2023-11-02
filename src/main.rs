use circuit::push_node;
use node::{as_nodes, Const, Node};
use num_bigint::BigUint;
use num_traits::FromPrimitive;
use std::env;

use crate::circuit::Circuit;
use crate::shares::Shares;

mod circuit;
mod node;
mod shares;

// type Nat = BigUint; // represent natural numbers as BigUint

fn main() {
    // Inputs
    let (x, y) = read_args(env::args());
    print!("Running BeDOZa on inputs: x={x} y={y}\n");

    // Parse inputs
    let (in_alice, in_bob) = str_to_nodes(&x, &y);

    // Initialize circuit
    let mut g: Circuit = init_circuit(in_alice, in_bob);
    g.transform_and_gates();

    // Evaluate circuit
    let Shares { x, y } = g.eval();

    print!("---------------------------------------------------\n");
    print!("Result of evaluation:\n");
    println!("Alices share: {:?}", x);
    println!("Bobs share: {:?}", y);
    println!("Reconstruction (XOR): {:?}", x ^ y);
    print!("---------------------------------------------------\n");
}

fn init_circuit(alice_in: [Node; 3], bob_in: [Node; 3]) -> Circuit {
    let mut g: Circuit = Circuit { nodes: vec![] };

    // input gates

    let [xa, xb, xr] = alice_in;
    let [ya, yb, yr] = bob_in;

    let xa_id = push_node(&mut g, xa);
    let xb_id = push_node(&mut g, xb);
    let xr_id = push_node(&mut g, xr);

    let ya_id = push_node(&mut g, ya);
    let yb_id = push_node(&mut g, yb);
    let yr_id = push_node(&mut g, yr);

    // first layer

    let xor_xa = Node::xor_unary(xa_id, Const::Literal(BigUint::from_i8(1).unwrap()));
    let xor_xa_id = push_node(&mut g, xor_xa);

    let xor_xb = Node::xor_unary(xb_id, Const::Literal(BigUint::from_i8(1).unwrap()));
    let xor_xb_id = push_node(&mut g, xor_xb);

    let xor_xr = Node::xor_unary(xr_id, Const::Literal(BigUint::from_i8(1).unwrap()));
    let xor_xr_id = push_node(&mut g, xor_xr);

    // second layer

    let and_ya = Node::and(xor_xa_id, ya_id);
    let and_ya_id = push_node(&mut g, and_ya);

    let and_yb = Node::and(xor_xb_id, yb_id);
    let and_yb_id = push_node(&mut g, and_yb);

    let and_yr = Node::and(xor_xr_id, yr_id);
    let and_yr_id = push_node(&mut g, and_yr);

    // third layer

    let xor_and_ya = Node::xor_unary(and_ya_id, Const::Literal(BigUint::from_i8(1).unwrap()));
    let xor_and_ya_id = push_node(&mut g, xor_and_ya);

    let xor_and_yb = Node::xor_unary(and_yb_id, Const::Literal(BigUint::from_i8(1).unwrap()));
    let xor_and_yb_id = push_node(&mut g, xor_and_yb);

    let xor_and_yr = Node::xor_unary(and_yr_id, Const::Literal(BigUint::from_i8(1).unwrap()));
    let xor_and_yr_id = push_node(&mut g, xor_and_yr);

    // fourth layer

    let and_xor1 = Node::and(xor_and_ya_id, xor_and_yb_id);
    let and_xor1_id = push_node(&mut g, and_xor1);

    let and_xor2 = Node::and(xor_and_yr_id, and_xor1_id);
    let _ = push_node(&mut g, and_xor2);
    g
}

// -------------- parsing inputs

fn read_args(args: env::Args) -> (String, String) {
    let args: Vec<String> = args.collect();
    let x = args.get(1).unwrap().to_string();
    let y = args.get(2).unwrap().to_string();
    (x, y)
}

fn parse_blood_type(s: &str) -> u8 {
    let mut state = 0;
    let mut i = 0;
    for (idx, c) in s.chars().enumerate() {
        if state == 0 {
            if c == 'A' {
                // i += 2;
                i += 4;
                state = 1;
            } else if c == 'B' {
                // i += 1;
                i += 2;
                state = 2;
            } else if c == 'o' {
                // nop
                state = 2;
            }
        } else if state == 1 {
            if c == 'B' {
                i += 2;
                state = 2;
            } else if c == '-' {
                // nop
                break;
            } else if c == '+' {
                i += 1;
                break;
            }
        } else if state == 2 {
            if c == '-' {
                // nop
                break;
            } else if c == '+' {
                i += 1;
                break;
            } else {
                panic!("could not parse {s} at index {idx}");
            }
        } else {
            panic!("could not parse {s}");
        }
    }
    i
}

fn as_bool_arr(n: u8) -> [BigUint; 3] {
    let mut res = [
        BigUint::from_i64(0).unwrap(),
        BigUint::from_i64(0).unwrap(),
        BigUint::from_i64(0).unwrap(),
    ];
    for i in 0..3 {
        res[2 - i] = BigUint::from_u8(((n >> i) % 2 != 0) as u8).unwrap();
    }
    res
}

fn str_to_nodes(x: &str, y: &str) -> ([Node; 3], [Node; 3]) {
    let bt_alice = as_bool_arr(parse_blood_type(x));
    let bt_bob = as_bool_arr(parse_blood_type(y));
    let in_alice = as_nodes(bt_alice);
    let in_bob = as_nodes(bt_bob);
    (in_alice, in_bob)
}

// --------------- tests ----------------

#[cfg(test)]
mod tests {
    use num_traits::{One, Zero};

    use crate::circuit::{deal_rands, Rands};

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

        let xor = Node::xor_unary(and_id, Const::Literal(One::one()));
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

        //let xor = Node::xor_unary(and_id, Const::Literal(One::one()));
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

        let xor = Node::xor_unary(and_id, Const::Literal(One::one()));
        push_node(&mut g, xor);
        g
    }

    #[test]
    fn test_transform_and_gates1() {
        // input gates

        for _ in 0..100 {
            for b1 in [&One::one(), &Zero::zero()] {
                for b2 in [&One::one(), &Zero::zero()] {
                    for b3 in [&One::one(), &Zero::zero()] {
                        for b4 in [&One::one(), &Zero::zero()] {
                            let x: Shares = Shares::new(b1, b2);
                            let y: Shares = Shares::new(b3, b4);

                            let mut g: Circuit =
                                single_and_gate(Node::in_(x.clone()), Node::in_(y.clone()));
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
            for b1 in [&One::one(), &Zero::zero()] {
                for b2 in [&One::one(), &Zero::zero()] {
                    for b3 in [&One::one(), &Zero::zero()] {
                        for b4 in [&One::one(), &Zero::zero()] {
                            let x: Shares = Shares::new(b1, b2);
                            let y: Shares = Shares::new(b3, b4);

                            let mut g =
                                and_xor_unary_one(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(res.val(), (x.val() & y.val()) ^ &One::one());
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
            for b1 in [&One::one(), &Zero::zero()] {
                for b2 in [&One::one(), &Zero::zero()] {
                    for b3 in [&One::one(), &Zero::zero()] {
                        for b4 in [&One::one(), &Zero::zero()] {
                            let x: Shares = Shares::new(b1, b2);
                            let y: Shares = Shares::new(b3, b4);

                            let mut g = xor_and_xor(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(res.val(), ((x.val() ^ y.val()) & x.val()) ^ &One::one());
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
            for b1 in [&One::one(), &Zero::zero()] {
                for b2 in [&One::one(), &Zero::zero()] {
                    for b3 in [&One::one(), &Zero::zero()] {
                        for b4 in [&One::one(), &Zero::zero()] {
                            let x: Shares = Shares::new(b1, b2);
                            let y: Shares = Shares::new(b3, b4);

                            let mut g = xor_and_xor(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(res.val(), ((x.val() ^ y.val()) & x.val()) ^ &One::one());
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
            for b1 in [&One::one(), &Zero::zero()] {
                for b2 in [&One::one(), &Zero::zero()] {
                    for b3 in [&One::one(), &Zero::zero()] {
                        for b4 in [&One::one(), &Zero::zero()] {
                            let x: Shares = Shares::new(b1, b2);
                            let y: Shares = Shares::new(b3, b4);

                            let mut g = and_and(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(res.val(), ((x.val() & y.val()) & y.val()));
                        }
                    }
                }
            }
        }
    }

    fn test_bedoza_helper(x: &str, y: &str, expectation: BigUint) {
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
            test_bedoza_helper(x, x, One::one());
        }

        for i in 0..4 {
            test_bedoza_helper(plus[i], minus[i], One::one());
            test_bedoza_helper(minus[i], plus[i], Zero::zero());
        }

        for i in 1..4 {
            test_bedoza_helper(plus[0], plus[i], One::one());
            test_bedoza_helper(minus[0], minus[i], One::one());
            test_bedoza_helper(plus[0], minus[i], One::one());
        }

        for i in 0..4 {
            for j in (i + 1)..4 {
                test_bedoza_helper(plus[j], plus[i], Zero::zero());
                test_bedoza_helper(minus[j], plus[i], Zero::zero());
                test_bedoza_helper(minus[j], minus[i], Zero::zero());
                test_bedoza_helper(plus[j], minus[i], Zero::zero());
            }
        }

        for i in 1..3 {
            test_bedoza_helper(plus[3], plus[i], Zero::zero());
            test_bedoza_helper(minus[3], minus[i], Zero::zero());
            test_bedoza_helper(plus[3], minus[i], Zero::zero());
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
}
