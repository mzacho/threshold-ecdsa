use getrandom::getrandom;
use num_bigint::BigUint;
use num_traits::FromPrimitive;
use std::collections::HashMap;

use crate::node::{Const, Gate, Node, NodeId};
use crate::shares::Shares;

#[derive(Debug)]
pub struct Circuit {
    pub nodes: Vec<Node>,
}

pub type Env = HashMap<NodeId, BigUint>;

impl Circuit {
    // Evaluates the circuit and returns the shares of the last node
    //
    // It does so by iterating over all nodes, and propagating values from
    // parents to children with respect to the operation of the current node.

    pub fn eval(self) -> Shares {
        // Env is a mapping from node ids to openings of the secret
        // flowing out of that node. Its used to lookup variables
        // referred to by constant gates (in contrast to literals
        // hard-coded into the constant gates).

        let mut env: Env = HashMap::new();

        let len = self.nodes.len();
        for id in 0..len {
            let node = &self.nodes[id];
            if node.value.borrow().is_some() {
                continue;
            }
            match &node.op {
                Gate::XORUnary(c) => {
                    if let Some(p1_id) = node.in_1 {
                        let p1 = &self.nodes[p1_id].value.borrow();
                        if p1.is_some() {
                            let p1_val = p1.as_ref().unwrap();
                            let node = &self.nodes[id];
                            let b = Self::lookup_const(&env, c);
                            *node.value.borrow_mut() = Some(p1_val ^ &b);
                        } else {
                            // In this case a node's parent has no value yet
                            // Since we assume the circuit only has forward
                            // gates, then this shouldn't be possible
                            panic!("expected value on XOR gate parent")
                        }
                    } else {
                        panic!("expected parent id on XOR gate")
                    }
                }
                Gate::AND => panic!("circuit not normalized"),
                Gate::XOR => match (node.in_1, node.in_2) {
                    (Some(p1_id), Some(p2_id)) => {
                        let p1 = &self.nodes[p1_id].value.borrow();
                        let p2 = &self.nodes[p2_id].value.borrow();
                        if p1.is_some() && p2.is_some() {
                            let v1 = p1.as_ref().unwrap();
                            let v2 = p2.as_ref().unwrap();
                            let node = &self.nodes[id];
                            *node.value.borrow_mut() = Some(v1 ^ v2);
                        } else {
                            panic!("no values on parents of AND")
                        }
                    }
                    (_, _) => panic!("no parent ids on AND gate"),
                },
                Gate::IN => continue,
                Gate::OPEN => {
                    match node.in_1 {
                        Some(pid) => {
                            let p = &self.nodes[pid].value.borrow();
                            if p.is_some() {
                                let s = p.as_ref().unwrap();
                                // Update the environment with the opened
                                // value of the node
                                env.insert(id, s.reconstruct());
                            } else {
                                panic!("no value to open");
                            }
                        }
                        None => panic!("no parent on open gate"),
                    }
                }
                Gate::ANDUnary(c) => {
                    if let Some(p1_id) = node.in_1 {
                        let p1 = &self.nodes[p1_id].value.borrow();
                        if p1.is_some() {
                            let p1_val = p1.as_ref().unwrap();
                            let node = &self.nodes[id];
                            let b = Self::lookup_const(&env, c);
                            *node.value.borrow_mut() = Some(p1_val & &b);
                        } else {
                            // In this case a node's parent has no value yet
                            // Since we assume the circuit only has forward
                            // gates, then this shouldn't be possible
                            panic!("expected value on XOR gate parent")
                        }
                    } else {
                        panic!("expected parent id on XOR gate")
                    }
                }
            }
        }
        self.nodes[len - 1].value.borrow().as_ref().unwrap().clone()
    }

    pub fn lookup_const(e: &Env, c: &Const) -> BigUint {
        match c {
            Const::Literal(b) => b.clone(),
            Const::Var(id) => {
                if let Some(b) = e.get(&id) {
                    b.clone()
                } else {
                    panic!("could not look up const var");
                }
            }
            Const::AND(id1, id2) => match (e.get(&id1), e.get(&id2)) {
                (Some(b1), Some(b2)) => b1.clone() & b2.clone(),
                (_, _) => panic!("could nok look up const vars for and"),
            },
        }
    }

    // Transforms all AND gates in a circuit. Any gates in the
    // circuit such as
    //
    // [x] AND [y]
    //
    // are removed and replaced by the gates correponding to
    // the protocol for AND of Two Wires from the lecture notes.
    //
    // The protocol makes use a dealer, whose output is added
    // as inputs gates in the circuit.
    //
    // OPEN gates are trivial, in that they only refer to the
    // id of the gate containing the value being opened.
    // The actual reconstruction of secrets is being
    // handled in the evaluation of the circuit.

    pub fn transform_and_gates(&mut self) -> () {
        let mut i = 0;
        while i < self.nodes.len() {
            let node = &self.nodes[i];
            match node.op {
                Gate::AND => {
                    let Rands { u, v, w } = deal_rands();
                    let pid1 = node.in_1.unwrap();
                    let pid2 = node.in_2.unwrap();

                    // Remove the gate and replace it with an input gate for u
                    //
                    // Note: This doesn't update parent pointers
                    self.nodes.remove(i);
                    self.nodes.insert(i, u.as_in_node());
                    let uid = i;

                    // Insert XOR gate with inputs pid1 and u
                    let did = i + 1;
                    self.insert_node(did, Node::xor(pid1, uid));

                    // Insert input gate for v
                    let vid = i + 2;
                    self.insert_node(vid, v.as_in_node());

                    // Insert XOR gate with inputs pid2 and v
                    let eid = i + 3;
                    self.insert_node(eid, Node::xor(pid2, vid));

                    // Insert OPEN gates for d and e
                    let odid = i + 4;
                    let oeid = i + 5;
                    self.insert_node(odid, Node::open(did));

                    self.insert_node(oeid, Node::open(eid));

                    // Insert unary AND gates for [x] and e
                    let and_xe_id = i + 6;
                    let c = Const::Var(oeid);
                    self.insert_node(and_xe_id, Node::and_unary(pid1, c));

                    // Insert unary XOR gates for [y] and d
                    let and_yd_id = i + 7;
                    let c = Const::Var(odid);
                    self.insert_node(and_yd_id, Node::and_unary(pid2, c));

                    // Insert input gate for w
                    let wid = i + 8;
                    self.insert_node(wid, w.as_in_node());

                    // Insert XOR gate with inputs w and xor_xe
                    let xor_wxe_id = i + 9;
                    self.insert_node(xor_wxe_id, Node::xor(wid, and_xe_id));

                    // Insert XOR gate with inputs and_yd and e*d
                    let xor_and_yd_ed_id = i + 10;
                    self.insert_node(
                        xor_and_yd_ed_id,
                        Node::xor_unary(and_yd_id, Const::AND(oeid, odid)),
                    );

                    // Insert XOR gate with inputs xor_wxe and xor_and_yd_ed
                    let xor_xor_wxe_xor_and_yd_ed_id = i + 11;
                    self.insert_node(
                        xor_xor_wxe_xor_and_yd_ed_id,
                        Node::xor(xor_wxe_id, xor_and_yd_ed_id),
                    );
                    i += 11;
                }
                _ => (),
            }
            i += 1;
        }
    }

    pub fn insert_node(&mut self, index: usize, n: Node) -> () {
        self.nodes.insert(index, n);

        // Increment parent pointers, if they point to an element
        // after index.
        //
        // Since we only have forward edges in the circuit, then nodes
        // can only point to previous element in the vector. We can
        // therefore skip elements [0; index].

        let len = self.nodes.len();
        for i in index + 1..len {
            if let Some(pid) = self.nodes[i].in_1 {
                if pid >= index - 1 {
                    self.nodes[i].in_1 = Some(pid + 1);
                }
            }
            if let Some(pid) = self.nodes[i].in_2 {
                if pid >= index - 1 {
                    self.nodes[i].in_2 = Some(pid + 1);
                }
            }
        }
    }
}

// The random shares distributed by the dealer to alice and bob.
// Invariant:
//   u.x & v.x = w.x
//   u.y & v.y = w.y

pub struct Rands {
    pub u: Shares,
    pub v: Shares,
    pub w: Shares,
}

pub fn deal_rands() -> Rands {
    // Sample random bits
    let mut buf = [0];
    if let Err(e) = getrandom(&mut buf) {
        panic!("{e}");
    }
    let ux: BigUint = BigUint::from_u8(buf[0]).unwrap();
    let uy: BigUint = BigUint::from_u8(buf[0]).unwrap();
    let vx: BigUint = BigUint::from_u8(buf[0]).unwrap();
    let vy: BigUint = BigUint::from_u8(buf[0]).unwrap();
    let wx: BigUint = BigUint::from_u8(buf[0]).unwrap();

    let u: Shares = Shares::new(ux.clone(), uy.clone());
    let v: Shares = Shares::new(vx.clone(), vy.clone());

    Rands {
        u,
        v,
        w: Shares::new(
            wx.clone(),
            wx ^ (ux.clone() & vx.clone()) ^ (ux & vy.clone()) ^ (uy.clone() & vx) ^ (uy & vy),
        ),
    }
}

pub fn push_node(c: &mut Circuit, n: Node) -> NodeId {
    c.nodes.push(n);
    c.nodes.len() - 1
}
