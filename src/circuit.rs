use std::collections::HashMap;

use crypto_bigint::rand_core::OsRng;
use crypto_bigint::{NonZero, RandomMod};

use crate::node::{Const, Gate, Node, NodeId};
use crate::shares::{Shares, M, Nat, mul_mod};

/// `Circuit` represents the circuit used in the BeDOZa protocol for
/// passively secure two-party computation.
///
/// A circuit consists of a vector of Nodes, i.e. Add, Mul, Open etc.,
/// whose IDs are implicit from their index into the Vec.
#[derive(Debug)]
pub struct Circuit {
    pub nodes: Vec<Node>,
}

/// Env is a mapping from node ids to openings of the secret
/// flowing out of that node. Its used to lookup variables
/// referred to by constant gates (in contrast to literals
/// hard-coded into the constant gates).
pub type Env = HashMap<NodeId, Nat>;

impl Circuit {

    /// Evaluates the circuit and returns the shares of the last node
    ///
    /// It does so by iterating over all nodes, and propagating values from
    /// parents to children with respect to the operation of the current node.
    pub fn eval(self) -> Shares {

        let mut env: Env = HashMap::new();

        let len = self.nodes.len();
        for id in 0..len {
            let node = &self.nodes[id];
            if node.value.borrow().is_some() {
                continue;
            }
            let p1_id = node.in_1;
            if p1_id.is_some() {
                let p1 = &self.nodes[p1_id.unwrap()].value.borrow();
                if !p1.is_some() {
                    // In this case a node's parent has no value yet
                    // Since we assume the circuit only has forward
                    // gates, then this shouldn't be possible
                    panic!("expected value on gate parent")
                }
                match &node.op {
                    Gate::AddUnary(c) => {
                                let p1_val = p1.as_ref().unwrap().clone();
                                let node = &self.nodes[id];
                                let const_value = Self::lookup_const(&env, c);
                                *node.value.borrow_mut() = Some(p1_val + const_value);
                    }
                    Gate::Mul => panic!("circuit not normalized"),
                    Gate::Add => {
                            if let Some(p2_id) = node.in_2 {
                                let p2 = &self.nodes[p2_id].value.borrow();
                                if p1.is_some() && p2.is_some() {
                                    let v1 = p1.as_ref().unwrap().clone();
                                    let v2 = p2.as_ref().unwrap().clone();
                                    let node = &self.nodes[id];
                                    *node.value.borrow_mut() = Some(v1 + v2);
                                } else {
                                    panic!("no values on parents of ADD")
                                }
                            } else {
                                panic!("expected parent id on Add gate")
                            }
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
                                let p1_val = p1.as_ref().unwrap().clone();
                                let node = &self.nodes[id];
                                let b = Self::lookup_const(&env, c);
                                *node.value.borrow_mut() = Some(p1_val * b);
                    }
                }
            } else {
                panic!("expected parent id on AddUnary gate")
            }

        }
        self.nodes[len - 1].value.borrow().as_ref().unwrap().clone()
    }

    /// Returns the constant represented by `c`, by possibly performing
    /// a lookup into the environment `e`.
    ///
    /// Constants are either literal, variables or the product of two
    /// constants.
    ///
    /// If `c` is a literal, its literal value is directly returned.
    ///
    /// If `c` is a variable it contains the id of a node, whose value
    /// should have been opened and inserted into the environment during
    /// evaluation of the circuit. Its value is returned.
    ///
    /// If `c` is the product of two constants, it contains the ids of
    /// two nodes, whose values should been opened and inserted into the
    /// environment during evaluation of the circuit. Their product is
    /// returned.
    pub fn lookup_const(e: &Env, c: &Const) -> Nat {
        match c {
            Const::Literal(b) => b.clone(),
            Const::Var(id) => {
                if let Some(const_value) = e.get(&id) {
                    const_value.clone()
                } else {
                    panic!("could not look up const var");
                }
            }
            Const::MUL(id1, id2) => match (e.get(&id1), e.get(&id2)) {
                (Some(const_value_1), Some(const_value_2)) => {
                    // Compute m - (e * d) mod m
                    M.sub_mod(&mul_mod(const_value_1, const_value_2), &M)
            },
                (_, _) => panic!("could nok look up const vars for and"),
            },
        }
    }

    /// Transforms all MUL gates in a circuit. Any gates in the
    /// circuit such as
    ///
    /// [x] MUL [y]
    ///
    /// are removed and replaced by the gates correponding to
    /// the protocol for MUL of Two Wires from the lecture notes.
    ///
    /// The protocol makes use a dealer, whose output is added
    /// as inputs gates in the circuit.
    ///
    /// OPEN gates are trivial, in that they only refer to the
    /// id of the gate containing the value being opened.
    /// The actual reconstruction of secrets is being
    /// handled in the evaluation of the circuit.
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
                    let mul_xe_id = i + 6;
                    let c = Const::Var(oeid);
                    self.insert_node(mul_xe_id, Node::mul_unary(pid1, c));

                    // Insert unary MUL gates for [y] and d
                    let mul_yd_id = i + 7;
                    let c = Const::Var(odid);
                    self.insert_node(mul_yd_id, Node::mul_unary(pid2, c));

                    // Insert input gate for w
                    let wid = i + 8;
                    self.insert_node(wid, w.as_in_node());

                    // Insert ADD gate with inputs w and add_xe
                    let add_wxe_id = i + 9;
                    self.insert_node(add_wxe_id, Node::add(wid, mul_xe_id));

                    // Insert ADD gate with inputs and_yd and -e*d
                    let sub_mull_yd_ed_id = i + 10;
                    self.insert_node(
                        sub_mull_yd_ed_id,
                        Node::add_unary(mul_yd_id, Const::MUL(oeid, odid)),
                    );

                    // Insert ADD gate with inputs add_wxe and sub_mul_yd_ed
                    let add_add_wxe_sub_mul_yd_ed_id = i + 11;
                    self.insert_node(
                        add_add_wxe_sub_mul_yd_ed_id,
                        Node::add(add_wxe_id, sub_mull_yd_ed_id),
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

    // Pick random elements from from Zm
    let ux: Nat = Nat::random_mod(&mut OsRng, &M);
    let uy: Nat = Nat::random_mod(&mut OsRng, &M);
    let vx: Nat = Nat::random_mod(&mut OsRng, &M);
    let vy: Nat = Nat::random_mod(&mut OsRng, &M);
    let wx: Nat = Nat::random_mod(&mut OsRng, &M);

    let u: Shares = Shares::new(ux.clone(), uy.clone());
    let v: Shares = Shares::new(vx.clone(), vy.clone());

    // Compute u * v mod m
    let k1 = mul_mod(&vx, &ux);
    let k2 = mul_mod(&ux, &vy);
    let k3 = mul_mod(&uy, &vx);
    let k4 = mul_mod(&uy, &vy);
    let uv = k1.add_mod(&k2.add_mod(&k3.add_mod(&k4, &M), &M), &M);

    // Compute (u * v) mod m - wx, avoiding underflow if uv < wx
    let wy = if uv < wx.clone() {
        M.clone().add_mod(&uv.sub_mod(&wx, &M), &M)
    } else {
        uv.sub_mod(&wx, &M)
    };

    let w = Shares::new(wx, wy);
    Rands { u, v, w }
}

pub fn push_node(c: &mut Circuit, n: Node) -> NodeId {
    c.nodes.push(n);
    c.nodes.len() - 1
}
