use getrandom::getrandom;
use std::cell::RefCell;
use std::env;
mod share;
mod node;
mod circuit;
use crate::share::Shares;
use crate::node::{Node, Const, NodeId};
use crate::circuit::Circuit;
// use num_bigint::BigUint;
// use num_integer::Integer;
// use num_traits::{FromPrimitive, Zero};

// type Nat = BigUint; // represent natural numbers as BigUint

fn main() {
    let (x, y) = read_args(env::args());
    print!("Running BeDOZa on inputs: x={x} y={y}\n");
    let (in_alice, in_bob) = str_to_nodes(&x, &y);
    let mut g: Circuit = init_circuit(in_alice, in_bob);
    g.transform_and_gates();
    let share::Shares { x, y } = g.eval();
    print!("---------------------------------------------------\n");
    print!("Result of evaluation:\n");
    print!(
        "Alices share: {x}\nBobs share: {y}\nReconstruction (XOR): {}\n",
        x ^ y
    );
    print!("---------------------------------------------------\n");
}

// Converts an array of boolean values, representing the
// input of Alice or Bob, into input nodes, to be used in
// the boolean circuit.
fn as_nodes(arr: [bool; 3]) -> [Node; 3] {
    // Sample random bits
    let mut buf = [0];
    if let Err(e) = getrandom(&mut buf) {
        panic!("{e}");
    }

    let mut nodes = [Node::default(), Node::default(), Node::default()];

    for (i, b) in arr.iter().enumerate() {
        // Make new secret share of b
        //
        // First sample a random bit

        let r = (buf[0] >> i) % 2 != 0;

        // Then assign Alices share to r XOR b
        // and Bobs share to r

        let s = Shares { x: r ^ b, y: r };

        nodes[i].value = RefCell::new(Some(s));
    }
    nodes
}

fn push_node(c: &mut Circuit, n: Node) -> NodeId {
    c.nodes.push(n);
    c.nodes.len() - 1
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

    let xor_xa = Node::xor_unary(xa_id, Const::Literal(true));
    let xor_xa_id = push_node(&mut g, xor_xa);

    let xor_xb = Node::xor_unary(xb_id, Const::Literal(true));
    let xor_xb_id = push_node(&mut g, xor_xb);

    let xor_xr = Node::xor_unary(xr_id, Const::Literal(true));
    let xor_xr_id = push_node(&mut g, xor_xr);

    // second layer

    let and_ya = Node::and(xor_xa_id, ya_id);
    let and_ya_id = push_node(&mut g, and_ya);

    let and_yb = Node::and(xor_xb_id, yb_id);
    let and_yb_id = push_node(&mut g, and_yb);

    let and_yr = Node::and(xor_xr_id, yr_id);
    let and_yr_id = push_node(&mut g, and_yr);

    // third layer

    let xor_and_ya = Node::xor_unary(and_ya_id, Const::Literal(true));
    let xor_and_ya_id = push_node(&mut g, xor_and_ya);

    let xor_and_yb = Node::xor_unary(and_yb_id, Const::Literal(true));
    let xor_and_yb_id = push_node(&mut g, xor_and_yb);

    let xor_and_yr = Node::xor_unary(and_yr_id, Const::Literal(true));
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

fn as_bool_arr(n: u8) -> [bool; 3] {
    let mut res = [false, false, false];
    for i in 0..3 {
        res[2 - i] = (n >> i) % 2 != 0;
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

#[cfg(test)]
mod tests;