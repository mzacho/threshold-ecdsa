use getrandom::getrandom;
use std::cell::RefCell;
use std::collections::HashMap;
use std::env;
use std::ops::{BitAnd, BitXor};
use std::rc::Rc;
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
    let Shares { x, y } = g.eval();
    print!("---------------------------------------------------\n");
    print!("Result of evaluation:\n");
    print!(
        "Alices share: {x}\nBobs share: {y}\nReconstruction (XOR): {}\n",
        x ^ y
    );
    print!("---------------------------------------------------\n");
}

#[derive(Debug, Clone)]
enum Gate {
    IN,
    XORUnary(Const),
    ANDUnary(Const),
    AND,
    XOR,
    OPEN,
}

#[derive(Debug, Clone, Copy)]
enum Const {
    Literal(bool),
    Var(usize),
    AND(usize, usize),
}

type NodeId = usize;

#[derive(Debug, Clone)]
struct Node {
    id: usize,
    in_1: Rc<Option<Node>>, // left parent
    in_2: Rc<Option<Node>>, // right parent
    op: Gate,
    value: RefCell<Option<Shares>>,
}

#[derive(Debug, Clone, Copy)]
struct Shares {
    x: bool, // todo: Nat
    y: bool, // todo: Nat
}

impl Shares {
    fn xor(&self, c: bool) -> Shares {
        Shares {
            x: self.x ^ c,
            y: self.y,
        }
    }

    fn and(&self, c: bool) -> Shares {
        Shares {
            x: self.x & c,
            y: self.y & c,
        }
    }

    // Reconstruct the secret from the shares
    fn val(&self) -> bool {
        self.x ^ self.y
    }

    fn as_in_node(&self) -> Node {
        Node::in_(*self)
    }
}

impl BitAnd for Shares {
    type Output = Shares;

    fn bitand(self, rhs: Self) -> Self::Output {
        Shares {
            x: self.x & rhs.x,
            y: self.y & rhs.y,
        }
    }
}

impl BitXor for Shares {
    type Output = Shares;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Shares {
            x: self.x ^ rhs.x,
            y: self.y ^ rhs.y,
        }
    }
}

impl Default for Shares {
    fn default() -> Self {
        Shares { x: true, y: true }
    }
}

impl Default for Node {
    fn default() -> Self {
        Node {
            id: 0,
            in_1: Rc::new(None),
            in_2: Rc::new(None),
            op: Gate::IN,
            value: RefCell::new(None),
        }
    }
}

impl Node {
    fn and(p1: &Rc<Option<Node>>, p2: &Rc<Option<Node>>) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p1),
            in_2: Rc::clone(p2),
            op: Gate::AND,
            ..Default::default()
        }
    }

    fn xor(p1: &Node, p2: &Node) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p1),
            in_2: Rc::clone(p2),
            op: Gate::XOR,
            ..Default::default()
        }
    }

    fn xor_unary(p: &Rc<Option<Node>>, c: Const) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p),
            in_2: Rc::new(None),
            op: Gate::XORUnary(c),
            ..Default::default()
        }
    }

    fn and_unary(p: &Rc<Option<Node>>, c: Const) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p),
            op: Gate::ANDUnary(c),
            ..Default::default()
        }
    }

    fn open(p: &Rc<Option<Node>>) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p),
            op: Gate::OPEN,
            ..Default::default()
        }
    }

    fn in_(s: Shares) -> Self {
        Node {
            id: 0,
            value: RefCell::new(Some(s)),
            ..Node::default()
        }
    }
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

#[derive(Debug)]
struct Circuit {
    nodes: Vec<Node>,
}

// Env is a mapping from node ids to openings of the secret
// flowing out of that node. Its used to lookup variables
// referred to by constant gates (in contrast to literals
// hard-coded into the constant gates).
type Env = HashMap<usize, bool>;

impl Circuit {
    // Evaluates the circuit and returns the shares of the last node
    //
    // It does so by iterating over all nodes, and propagating values from
    // parents to children with respect to the operation of the current node.

    fn eval(&self) -> Shares {
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
                Gate::AND => {
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

    fn lookup_const(e: &Env, c: Const) -> bool {
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

    fn transform_and_gates(&mut self) -> () {
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
                    self.insert_node(did, Node::xor(pid1, &pid1));
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

    fn insert_node(&mut self, index: usize, n: Node) -> () {
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

struct Rands {
    u: Shares,
    v: Shares,
    w: Shares,
}

fn deal_rands() -> Rands {
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

// --------------- tests ----------------

#[cfg(test)]
mod tests {
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
}
