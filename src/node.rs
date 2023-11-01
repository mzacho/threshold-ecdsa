use std::{rc::Rc, cell::RefCell};
use crate::share::Shares;

#[derive(Debug, Clone, Copy)]
pub enum Const {
    Literal(bool),
    Var(usize),
    AND(usize, usize),
}

#[derive(Debug, Clone)]
pub enum Gate {
    IN,
    XORUnary(Const),
    ANDUnary(Const),
    AND,
    XOR,
    OPEN,
}

pub type NodeId = usize;

#[derive(Debug, Clone)]
pub struct Node {
    pub id: usize,
    pub in_1: Rc<Option<Node>>, // left parent
    pub in_2: Rc<Option<Node>>, // right parent
    pub op: Gate,
    pub value: RefCell<Option<Shares>>,
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
    pub fn and(p1: &Rc<Option<Node>>, p2: &Rc<Option<Node>>) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p1),
            in_2: Rc::clone(p2),
            op: Gate::AND,
            ..Default::default()
        }
    }

    pub fn xor(p1:  &Rc<Option<Node>>, p2:  &Rc<Option<Node>>) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p1),
            in_2: Rc::clone(p2),
            op: Gate::XOR,
            ..Default::default()
        }
    }

    pub fn xor_unary(p: &Rc<Option<Node>>, c: Const) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p),
            in_2: Rc::new(None),
            op: Gate::XORUnary(c),
            ..Default::default()
        }
    }

    pub fn and_unary(p: &Rc<Option<Node>>, c: Const) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p),
            op: Gate::ANDUnary(c),
            ..Default::default()
        }
    }

    pub fn open(p: &Rc<Option<Node>>) -> Self {
        Node {
            id: 0,
            in_1: Rc::clone(p),
            op: Gate::OPEN,
            ..Default::default()
        }
    }

    pub fn in_(s: Shares) -> Self {
        Node {
            id: 0,
            value: RefCell::new(Some(s)),
            ..Node::default()
        }
    }
}

