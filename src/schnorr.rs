use crate::{
    circuit::{push_node, Circuit},
    groups::GroupSpec,
    nat::Nat,
    node::{Const, Node},
    shares::Shares,
};

pub fn schnorr_circuit(r: Shares, sk: Shares, e: Nat) -> Circuit {
    let mut g: Circuit = Circuit { nodes: vec![] };

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

pub fn generate_e_from_message(message: Nat, q: Nat) {
    let group = GroupSpec::new();

    let r1 = group.rand_exp();
    let r2 = group.rand_exp();

    todo!("Finish this")
}
