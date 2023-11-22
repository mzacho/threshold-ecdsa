use std::env;

use crypto_bigint::Encoding;
use sha256_rs::sha256;

use crate::{
    circuit::{push_node, Circuit},
    groups::GroupSpec,
    nat::{pow_mod, Nat},
    node::{Const, Node},
    shares::Shares,
};

pub fn run_schnorr(m: Nat) {
    todo!()
}

pub fn read_args_message(args: env::Args) -> Nat {
    let args: Vec<String> = args.collect();
    let m = Nat::from(args.get(2).unwrap().parse::<u32>().unwrap());
    m
}

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

pub fn compute_e(message: Nat, group: GroupSpec) -> Nat {

    let r1 = group.rand_exp();
    let r2 = group.rand_exp();

    let c = pow_mod(&group.alpha, &r1.add_mod(&r2, &group.q), &group.q);

    let c_bytes = c.to_be_bytes();
    let c_m_bytes = [c_bytes, message.to_be_bytes()].concat();

    let e = Nat::from_be_bytes(sha256(&c_m_bytes));

    e
}

#[cfg(test)]
mod tests {

    use crate::{groups::GroupSpec, nat::M, shares::Shares};

    #[test]
    fn test_schnorr_circuit() {
        let group_spec = GroupSpec::new();
        // Construct a new secret key
        let sk = group_spec.rand_exp();
        let ss_sk = Shares::new(&sk, *M);
        // Have Alice choose a random r1 from Zq, and compute g^r1
        let r1 = group_spec.rand_exp();
        // let c1 = group_spec.g.pow();
        // Have Bob choose a random r2 from Zq, and compute g^r2
        let r2 = group_spec.rand_exp();
        // A
    }
}
