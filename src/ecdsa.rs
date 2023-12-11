// pub fn run_ecdsa() {
//     todo!()
// }

use crypto_bigint::NonZero;

use crate::{
    circuit::{deal_rands, push_node, Circuit, Rands},
    nat::Nat,
    node::Node,
    shares::{NatShares, PointShares},
};

pub fn run_ecdsa(m: Nat, sk: Nat, modulus: NonZero<Nat>) {
    let preprocessed_tuple = user_independent_preprocessing(&modulus);

    let sk_shared = NatShares::new(&sk, modulus);
}

/// Generate tuple (<k>, [k_inv])
///
/// <k> is a shared point on the elliptic curve
/// [k_inv] is a shared scalar
pub fn user_independent_preprocessing(modulus: &NonZero<Nat>) -> (PointShares, NatShares) {
    // Servers run ([a], [b], [c]) <- RandMul()
    let Rands { u, v, w } = deal_rands(modulus);

    // Run c <- Open([c])
    let c = w.open();

    // [k_inv] = [a]
    let k_inv = u;
    let (c_inv, c_inv_exists) = c.inv_mod(modulus);

    // Define <k> <- Convert([b] * c_inv)
    if !bool::from(c_inv_exists) {
        panic!("c inverse does not exist")
    }

    let product = v * c_inv;

    let k_point_share = PointShares::from(product);

    return (k_point_share, k_inv);
}

pub fn ecdsa_circuit(sk_shared: NatShares, preprocessed_tuple: (PointShares, NatShares)) {
    // Create circuit
    let mut circuit: Circuit = Circuit {
        nodes: vec![],
        modulus: sk_shared.m,
    };

    // User dependent preprocessing

    // # Input nodes
    
    // <k>

    // [k_inv]
    let in_k_inv = Node::in_(preprocessed_tuple.1);
    let in_k_inv_id = push_node(&mut circuit, in_k_inv);

    // [sk]
    let in_sk = Node::in_(sk_shared);
    let in_sk_id = push_node(&mut circuit, in_sk);


    // Compute [sk'] = [sk] * [k_inv]
    let sk_prime = Node::mul(in_sk_id, in_k_inv_id);

    // Open <k>

    let 


}

#[cfg(test)]
mod tests {
    use crypto_bigint::rand_core::OsRng;
    use k256::ecdsa::{
        signature::Signer, signature::Verifier, Signature, SigningKey, VerifyingKey,
    };

    #[test]
    fn test_sign() {
        let sk = SigningKey::random(&mut OsRng);
        let message = b"hello ecdsa";
        let _: Signature = sk.sign(message);
    }

    #[test]
    fn test_verify() {
        let sk = SigningKey::random(&mut OsRng);
        let message = b"hello ecdsa";
        let signature: Signature = sk.sign(message);
        let pk = VerifyingKey::from(&sk);
        assert!(pk.verify(message, &signature).is_ok());
    }
}
