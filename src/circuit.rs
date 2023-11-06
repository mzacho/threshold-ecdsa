use num_bigint::{BigUint, RandBigInt};
use num_integer::Integer;
use std::collections::HashMap;

use crate::node::{Const, Gate, Node, NodeId};
use crate::shares::{Shares, M};

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
                Gate::AddUnary(c) => {
                    if let Some(p1_id) = node.in_1 {
                        let p1 = &self.nodes[p1_id].value.borrow();
                        if p1.is_some() {
                            let p1_val = p1.as_ref().unwrap().clone();
                            let node = &self.nodes[id];
                            let b = Self::lookup_const(&env, c);
                            *node.value.borrow_mut() = Some(p1_val + b);
                        } else {
                            // In this case a node's parent has no value yet
                            // Since we assume the circuit only has forward
                            // gates, then this shouldn't be possible
                            panic!("expected value on AddUnary gate parent")
                        }
                    } else {
                        panic!("expected parent id on AddUnary gate")
                    }
                }
                Gate::Mul => panic!("circuit not normalized"),
                Gate::Add => match (node.in_1, node.in_2) {
                    (Some(p1_id), Some(p2_id)) => {
                        let p1 = &self.nodes[p1_id].value.borrow();
                        let p2 = &self.nodes[p2_id].value.borrow();
                        if p1.is_some() && p2.is_some() {
                            let v1 = p1.as_ref().unwrap().clone();
                            let v2 = p2.as_ref().unwrap().clone();
                            let node = &self.nodes[id];
                            *node.value.borrow_mut() = Some(v1 + v2);
                        } else {
                            panic!("no values on parents of AND")
                        }
                    }
                    (_, _) => panic!("no parent ids on AND gate"),
                },
                Gate::In => continue,
                Gate::Open => {
                    match node.in_1 {
                        Some(pid) => {
                            let p = &self.nodes[pid].value.borrow();
                            if p.is_some() {
                                let s = p.as_ref().unwrap().clone();
                                // Update the environment with the opened
                                // value of the node
                                env.insert(id, s.open());
                            } else {
                                panic!("no value to open");
                            }
                        }
                        None => panic!("no parent on open gate"),
                    }
                }
                Gate::MulUnary(c) => {
                    if let Some(p1_id) = node.in_1 {
                        let p1 = &self.nodes[p1_id].value.borrow();
                        if p1.is_some() {
                            let p1_val = p1.as_ref().unwrap().clone();
                            let node = &self.nodes[id];
                            let b = Self::lookup_const(&env, c);
                            *node.value.borrow_mut() = Some(p1_val * b);
                        } else {
                            // In this case a node's parent has no value yet
                            // Since we assume the circuit only has forward
                            // gates, then this shouldn't be possible
                            panic!("expected value on MulUnary gate parent")
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
                (Some(b1), Some(b2)) => {
                    // Compute -b1*b2 mod m, i.e. m - ((b1 * b2) mod m)
                    &M.clone() - (b1.clone() * b2.clone()).mod_floor(&M)
            },
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
                Gate::Mul => {
                    let Rands { u, v, w } = deal_rands();
                    let pid1 = node.in_1.unwrap();
                    let pid2 = node.in_2.unwrap();

                    // Remove the gate and replace it with an input gate for u
                    //
                    // Note: This doesn't update parent pointers
                    self.nodes.remove(i);
                    self.nodes.insert(i, u.as_in_node());
                    let uid = i;

                    // Insert ADD gate with inputs pid1 and u
                    let did = i + 1;
                    self.insert_node(did, Node::add(pid1, uid));

                    // Insert input gate for v
                    let vid = i + 2;
                    self.insert_node(vid, v.as_in_node());

                    // Insert ADD gate with inputs pid2 and v
                    let eid = i + 3;
                    self.insert_node(eid, Node::add(pid2, vid));

                    // Insert OPEN gates for d and e
                    let odid = i + 4;
                    let oeid = i + 5;
                    self.insert_node(odid, Node::open(did));

                    self.insert_node(oeid, Node::open(eid));

                    // Insert unary MUL gates for [x] and e
                    let and_xe_id = i + 6;
                    let c = Const::Var(oeid);
                    self.insert_node(and_xe_id, Node::mul_unary(pid1, c));

                    // Insert unary MUL gates for [y] and d
                    let and_yd_id = i + 7;
                    let c = Const::Var(odid);
                    self.insert_node(and_yd_id, Node::mul_unary(pid2, c));

                    // Insert input gate for w
                    let wid = i + 8;
                    self.insert_node(wid, w.as_in_node());

                    // Insert ADD gate with inputs w and xor_xe
                    let xor_wxe_id = i + 9;
                    self.insert_node(xor_wxe_id, Node::add(wid, and_xe_id));

                    // Insert ADD gate with inputs and_yd and -e*d
                    let xor_and_yd_ed_id = i + 10;
                    self.insert_node(
                        xor_and_yd_ed_id,
                        Node::add_unary(and_yd_id, Const::AND(oeid, odid)),
                    );

                    // Insert XOR gate with inputs xor_wxe and xor_and_yd_ed
                    let xor_xor_wxe_xor_and_yd_ed_id = i + 11;
                    self.insert_node(
                        xor_xor_wxe_xor_and_yd_ed_id,
                        Node::add(xor_wxe_id, xor_and_yd_ed_id),
                    );
                    i += 11;
                }
                _ => (),
            }
            i += 1;
        }
    }

    /// Insert `Node` in `self.nodes` and increment parent pointers of all
    /// nodes whose parent(s) have an `id` > `index` (similar to how one
    /// would insert an element at the front of a linked list).
    ///
    /// Since we only have forward edges in the circuit, then nodes
    /// can only point to previous element in the vector. We can
    /// therefore skip elements [0; index].
    pub fn insert_node(&mut self, index: usize, n: Node) -> () {
        self.nodes.insert(index, n);

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

/// The random shares distributed by the dealer to alice and bob.
/// Invariant:
///   (u.open() * v.open()).mod_floor(&M) = w.open()
pub struct Rands {
    pub u: Shares,
    pub v: Shares,
    pub w: Shares,
}

/// Constructs new secret shares of u, v, w such that u * v = w.
///
/// Is does so by choosing random values in Zm for ux, uy, vx, vy and wx,
/// and computes wy as (((ux + uy) * (vx + vy)) mod m - wx) mod m
pub fn deal_rands() -> Rands {
    let mut rng = rand::thread_rng();

    // Pick random elements from from Zm
    let ux: BigUint = rng.gen_biguint(M.bits()).mod_floor(&M);
    let uy: BigUint = rng.gen_biguint(M.bits()).mod_floor(&M);
    let vx: BigUint = rng.gen_biguint(M.bits()).mod_floor(&M);
    let vy: BigUint = rng.gen_biguint(M.bits()).mod_floor(&M);
    let wx: BigUint = rng.gen_biguint(M.bits()).mod_floor(&M);

    let u: Shares = Shares::new(ux.clone(), uy.clone());
    let v: Shares = Shares::new(vx.clone(), vy.clone());

    // Compute u * v mod m
    let k1 = ux.clone() * vx.clone();
    let k2 = ux * vy.clone();
    let k3 = uy.clone() * vx;
    let k4 = uy * vy;
    let uv = (k1 + k2 + k3 + k4).mod_floor(&M);

    // Compute (u * v) mod m - wx, avoiding underflow if uv < wx
    let wy = if uv < wx.clone() {
        &M.clone() + uv - wx.clone()
    } else {
        uv - wx.clone()
    };

    let w = Shares::new(wx, wy);
    Rands { u, v, w }
}

pub fn push_node(c: &mut Circuit, n: Node) -> NodeId {
    c.nodes.push(n);
    c.nodes.len() - 1
}
