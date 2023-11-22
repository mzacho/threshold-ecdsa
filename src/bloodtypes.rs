use std::env;

use crate::{
    circuit::{push_node, Circuit},
    nat::{Nat, TWO},
    node::{as_nodes, Const, Node},
    shares::Shares,
};

pub fn run_blood_type(x: String, y: String, debug: bool) -> Nat {
    // Inputs
    print!("Running BeDOZa on inputs: x={x} y={y}\n");

    // Parse inputs
    let (in_alice, in_bob) = str_to_nodes(&x, &y);

    // Initialize circuit
    let mut g: Circuit = blood_type_compatability_circuit(in_alice, in_bob);
    g.transform_and_gates();

    // Evaluate circuit
    let Shares { x, y, modulus: _ } = g.eval();

    let result = x.add_mod(&y, &TWO);

    if debug {
        print!("---------------------------------------------------\n");
        print!("Result of evaluation:\n");
        println!("Alices share: {:?}", x);
        println!("Bobs share: {:?}", y);
        println!("Reconstruction (XOR): {:?}", x ^ y);
        print!("---------------------------------------------------\n");
    }

    result
}

pub fn blood_type_compatability_circuit(alice_in: [Node; 3], bob_in: [Node; 3]) -> Circuit {
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

    let xor_xa = Node::add_unary(xa_id, Const::Literal(Nat::from_u8(1)));
    let xor_xa_id = push_node(&mut g, xor_xa);

    let xor_xb = Node::add_unary(xb_id, Const::Literal(Nat::from_u8(1)));
    let xor_xb_id = push_node(&mut g, xor_xb);

    let xor_xr = Node::add_unary(xr_id, Const::Literal(Nat::from_u8(1)));
    let xor_xr_id = push_node(&mut g, xor_xr);

    // second layer

    let and_ya = Node::mul(xor_xa_id, ya_id);
    let and_ya_id = push_node(&mut g, and_ya);

    let and_yb = Node::mul(xor_xb_id, yb_id);
    let and_yb_id = push_node(&mut g, and_yb);

    let and_yr = Node::mul(xor_xr_id, yr_id);
    let and_yr_id = push_node(&mut g, and_yr);

    // third layer

    let xor_and_ya = Node::add_unary(and_ya_id, Const::Literal(Nat::from_u8(1)));
    let xor_and_ya_id = push_node(&mut g, xor_and_ya);

    let xor_and_yb = Node::add_unary(and_yb_id, Const::Literal(Nat::from_u8(1)));
    let xor_and_yb_id = push_node(&mut g, xor_and_yb);

    let xor_and_yr = Node::add_unary(and_yr_id, Const::Literal(Nat::from_u8(1)));
    let xor_and_yr_id = push_node(&mut g, xor_and_yr);

    // fourth layer

    let and_xor1 = Node::mul(xor_and_ya_id, xor_and_yb_id);
    let and_xor1_id = push_node(&mut g, and_xor1);

    let and_xor2 = Node::mul(xor_and_yr_id, and_xor1_id);
    let _ = push_node(&mut g, and_xor2);
    g
}

// -------------- parsing inputs

pub fn read_args_bloodtypes(args: env::Args) -> (String, String) {
    let args: Vec<String> = args.collect();
    let x = args.get(2).unwrap().to_string();
    let y = args.get(3).unwrap().to_string();
    (x, y)
}

pub fn parse_blood_type(s: &str) -> u8 {
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

fn as_bool_arr(n: u8) -> [Nat; 3] {
    let mut res = [Nat::from_u64(0), Nat::from_u64(0), Nat::from_u64(0)];
    for i in 0..3 {
        res[2 - i] = Nat::from_u8(((n >> i) % 2 != 0) as u8);
    }
    res
}

pub fn str_to_nodes(x: &str, y: &str) -> ([Node; 3], [Node; 3]) {
    let bt_alice = as_bool_arr(parse_blood_type(x));
    let bt_bob = as_bool_arr(parse_blood_type(y));
    let in_alice = as_nodes(bt_alice, *TWO);
    let in_bob = as_nodes(bt_bob, *TWO);
    (in_alice, in_bob)
}

// --------------- tests ----------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_bloodtypes() {
        let tt: [[u8; 8]; 8] = [
            [1, 0, 0, 0, 0, 0, 0, 0],
            [1, 1, 0, 0, 0, 0, 0, 0],
            [1, 0, 1, 0, 0, 0, 0, 0],
            [1, 1, 1, 1, 0, 0, 0, 0],
            [1, 0, 0, 0, 1, 0, 0, 0],
            [1, 1, 0, 0, 1, 1, 0, 0],
            [1, 0, 1, 0, 1, 0, 1, 0],
            [1, 1, 1, 1, 1, 1, 1, 1],
        ];

        let bloodtypes = ["A+", "A-", "B+", "B-", "AB+", "AB-", "o+", "o-"];

        for (i, alice_bt) in bloodtypes.iter().enumerate() {
            for (j, bob_bt) in bloodtypes.iter().enumerate() {
                let res = run_blood_type(alice_bt.to_string(), bob_bt.to_string(), false);
                let expected = tt[i][j];
                assert_eq!(res, Nat::from(expected))
            }
        }
    }
}
