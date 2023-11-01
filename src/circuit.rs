use std::{collections::HashMap, cell::RefCell};
use getrandom::getrandom;

use crate::{share::Shares, node::{Gate, Const, Node}};


#[derive(Debug)]
pub struct Circuit {
    pub nodes: Vec<Node>,
}

// Env is a mapping from node ids to openings of the secret
// flowing out of that node. Its used to lookup variables
// referred to by constant gates (in contrast to literals
// hard-coded into the constant gates).
pub type Env = HashMap<usize, bool>;


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
    let ux = buf[0] % 2 != 0;
    let uy = (buf[0] >> 1) % 2 != 0;
    let vx = (buf[0] >> 2) % 2 != 0;
    let vy = (buf[0] >> 3) % 2 != 0;
    let wx = (buf[0] >> 4) % 2 != 0;
    Rands {
        u: Shares { x: ux, y: uy },
        v: Shares { x: vx, y: vy },
        w: Shares {
            x: wx,
            y: wx ^ (ux & vx) ^ (ux & vy) ^ (uy & vx) ^ (uy & vy),
        },
    }
}

impl Circuit {
    // Evaluates the circuit and returns the shares of the last node
    //
    // It does so by iterating over all nodes, and propagating values from
    // parents to children with respect to the operation of the current node.

    pub fn eval(&self) -> Shares {
        let mut env: Env = HashMap::new();

        for (id, node) in self.nodes.iter().enumerate() {
            if node.value.borrow().is_some() {
                // Node has been evaluated to a value
                continue;
            }
            // Resulting value
            let v = RefCell::new(None);

            match node.op {
                Gate::XORUnary(c) => {
                    let b = Self::lookup_const(&env, c);
                    if node.in_1.is_none() {
                        panic!("expected parent id on XOR gate")
                    }
                    let parent = node.in_1.unwrap();
                    if parent.value.borrow().is_none() {
                        // In this case a node's parent has no value yet
                        // Since we assume the circuit only has forward
                        // gates, then this shouldn't be possible
                        panic!("expected value on XOR gate parent")
                    } else {
                        let p1_val = parent.value.borrow().unwrap();
                        *v.borrow_mut() = Some(p1_val.xor(b));
                    }
                }
                Gate::AND => { // TODO: Should we remove this?
                    if node.in_1.is_none() || node.in_2.is_none() {
                        panic!("no p_ids on AND");
                    }
                    let p1 = node.in_1.unwrap();
                    let p2 = node.in_2.unwrap();
                    if p1.value.borrow().is_none() || p2.value.borrow().is_none() {
                        panic!("no values on parents of AND")
                    }
                    let v1 = p1.value.borrow().unwrap();
                    let v2 = p2.value.borrow().unwrap();
                    *v.borrow_mut() = Some(v1 & v2);
                }
                Gate::XOR => {
                    if node.in_1.is_none() || node.in_2.is_none() {
                        panic!("no p_ids on AND");
                    }
                    let p1 = node.in_1.unwrap();
                    let p2 = node.in_2.unwrap();
                    if p1.value.borrow().is_none() || p2.value.borrow().is_none() {
                        panic!("no values on parents of AND")
                    }
                    let v1 = p1.value.borrow().unwrap();
                    let v2 = p2.value.borrow().unwrap();
                    *v.borrow_mut() = Some(v1 ^ v2);
                }
                Gate::IN => continue,
                Gate::OPEN => {
                    if node.in_1.is_none() {
                        panic!("no parent on open gate");
                    }
                    let p = node.in_1.unwrap();
                    if p.value.borrow().is_none() {
                        panic!("no value to open");
                    } else {
                        // Update the environment
                        env.insert(id, p.value.borrow().unwrap().val());
                    }
                }
                Gate::ANDUnary(c) => {
                    let b = Self::lookup_const(&env, c);
                    if node.in_1.is_none() {
                        panic!("expected parent id on XOR gate")
                    }
                    let parent = node.in_1.unwrap();
                    if parent.value.borrow().is_none() {
                        // In this case a node's parent has no value yet
                        // Since we assume the circuit only has forward
                        // gates, then this shouldn't be possible
                        panic!("expected value on XOR gate parent")
                    } else {
                        let p1_val = parent.value.borrow().unwrap();
                        *v.borrow_mut() = Some(p1_val.and(b));
                    }
                }
            }
        }
        self.nodes.last().unwrap().value.borrow().unwrap()
    }

    pub fn lookup_const(e: &Env, c: Const) -> bool {
        match c {
            Const::Literal(b) => b,
            Const::Var(id) => {
                if let Some(b) = e.get(&id) {
                    *b
                } else {
                    panic!("could not look up const var");
                }
            }
            Const::AND(id1, id2) => match (e.get(&id1), e.get(&id2)) {
                (Some(b1), Some(b2)) => *b1 & *b2,
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

    pub fn transform_and_gates(&mut self) -> () { // TODO: Should we do it directly on the circuit instead of breaking it into subProtocols
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
                    self.insert_node(did, Node::xor(&pid1, &pid1));
                    // self.insert_node(did, Node::xor(pid1, uid));

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
            if self.nodes[i].in_1.is_some() {
                let p = self.nodes[i].in_1.unwrap();
                if p.id >= index - 1 {
                    self.nodes[i].in_1 = Some(p.id + 1);
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
