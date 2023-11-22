use crypto_bigint::Encoding;
use sha256_rs::sha256;

use crate::{
    circuit::{push_node, Circuit},
    groups::GroupSpec,
    nat::{pow_mod, Nat},
    node::{Const, Node},
    shares::Shares,
};

pub fn schnorr_circuit(r: Shares, sk: Shares, e: Nat) -> Circuit {
    assert!(r.m == sk.m);
    let mut g: Circuit = Circuit { nodes: vec![], modulus: r.m };

    let in_sk = Node::in_(sk);
    let in_sk_id = push_node(&mut g, in_sk);

    let in_r = Node::in_(r);
    let in_r_id = push_node(&mut g, in_r);

    let mul_e = Node::mul_unary(in_sk_id, Const::Literal(e));
    let mul_e_id = push_node(&mut g, mul_e);

    let z = Node::add(in_r_id, mul_e_id);
    let _ = push_node(&mut g, z);
    g
}

pub fn compute_e(message: Nat, group: GroupSpec) -> Nat {

    let r1 = group.rand_exp();
    let r2 = group.rand_exp();

    let c = pow_mod(&group.alpha, &r1.add_mod(&r2, &group.q), &group.q);

    let c_bytes = c.to_be_bytes();
    let c_m_bytes = [c_bytes, message.to_be_bytes()].concat();

    let e = Nat::from_be_bytes(sha256(&c_m_bytes));

    e
}
