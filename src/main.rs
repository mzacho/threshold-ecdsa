use std::env;
mod circuit;
mod groups;
mod nat;
mod node;
mod schnorr;
mod shares;

fn main() {
    // Inputs
    let (x, y) = read_args(env::args());
    print!("Running BeDOZa on inputs: x={x} y={y}\n");

    // Parse inputs
    //let (in_alice, in_bob) = str_to_nodes(&x, &y);

    // Initialize circuit
    // let mut g: Circuit = schnorr_circuit(in_alice, in_bob);
    // g.transform_and_gates();

    // Evaluate circuit
    // let Shares { x, y } = g.eval();

    print!("---------------------------------------------------\n");
    print!("Result of evaluation:\n");
    println!("Alices share: {:?}", x);
    println!("Bobs share: {:?}", y);
    // println!("Reconstruction (XOR): {:?}", x ^ y);
    print!("---------------------------------------------------\n");
}

// -------------- parsing inputs

fn read_args(args: env::Args) -> (String, String) {
    let args: Vec<String> = args.collect();
    let x = args.get(1).unwrap().to_string();
    let y = args.get(2).unwrap().to_string();
    (x, y)
}

// --------------- tests ----------------

#[cfg(test)]
mod tests {

    use crypto_bigint::NonZero;

    use crate::{
        circuit::{deal_rands, push_node, Circuit, Rands},
        groups::GroupSpec,
        nat::{mul_mod, Nat},
        node::{Const, Node},
        shares::Shares,
    };

    fn single_mul_gate(x: Node, y: Node) -> Circuit {
        let modulus = x.value.borrow().as_ref().unwrap().m.clone();
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
        let modulus = x.value.borrow().as_ref().unwrap().m.clone();
        let mut g: Circuit = Circuit {
            nodes: vec![],
            modulus,
        };

        let xa_id = push_node(&mut g, x);
        let ya_id = push_node(&mut g, y);

        let and = Node::mul(xa_id, ya_id);
        let and_id = push_node(&mut g, and);

        let xor = Node::add_unary(and_id, Const::Literal(Nat::from(1u32)));
        push_node(&mut g, xor);
        g
    }

    fn and_and(x: Node, y: Node) -> Circuit {
        let modulus = x.value.borrow().as_ref().unwrap().m.clone();
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
        let modulus = x.value.borrow().as_ref().unwrap().m.clone();
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

        let xor = Node::add_unary(and_id, Const::Literal(Nat::from(1u32)));
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
                            let x: Shares = Shares::from(b1.clone(), b2.clone(), m.clone());
                            let y: Shares = Shares::from(b3.clone(), b4, m.clone());

                            let mut g: Circuit =
                                single_mul_gate(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(res.open(), mul_mod(&x.open(), &y.open(), &m));
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
                            let x: Shares = Shares::from(b1.clone(), b2.clone(), m.clone());
                            let y: Shares = Shares::from(b3.clone(), b4, m.clone());

                            let mut g =
                                and_xor_unary_one(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open(),
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
                            let x: Shares = Shares::from(b1.clone(), b2.clone(), m.clone());
                            let y: Shares = Shares::from(b3.clone(), b4, m.clone());

                            let mut g =
                                x_plus_y_times_x_plus_1(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open(),
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
                            let x: Shares = Shares::from(b1.clone(), b2.clone(), m.clone());
                            let y: Shares = Shares::from(b3.clone(), b4, m.clone());

                            let mut g =
                                x_plus_y_times_x_plus_1(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open(),
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
                            let x: Shares = Shares::from(b1.clone(), b2.clone(), m.clone());
                            let y: Shares = Shares::from(b3.clone(), b4, m.clone());

                            let mut g = and_and(Node::in_(x.clone()), Node::in_(y.clone()));
                            g.transform_and_gates();
                            let res = g.eval();
                            assert_eq!(
                                res.open(),
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

    #[test]
    fn test_schnorr_circuit() {
        let group_spec = GroupSpec::new();
        // Construct a new secret key
        let sk = group_spec.rand_exp();
        let ss_sk = Shares::new(&sk, group_spec.q);
        // Have Alice choose a random r1 from Zq, and compute g^r1
        let r1 = group_spec.rand_exp();
        // let c1 = group_spec.g.pow();
        // Have Bob choose a random r2 from Zq, and compute g^r2
        let r2 = group_spec.rand_exp();
        // todo
        let _ = ss_sk;
        let _ = r1;
        let _ = r2;
    }
}
