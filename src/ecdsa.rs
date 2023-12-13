use crypto_bigint::{Encoding, NonZero};
use elliptic_curve::{point::AffineCoordinates, FieldBytesEncoding};
use k256::AffinePoint;
use sha2::{Digest, Sha256};

// use crypto_bigint::Encoding;

use crate::{
    circuit::{deal_rands, push_node, Circuit, Rands},
    nat::Nat,
    node::{Const, ConstLiteral, Node},
    shares::{NatShares, PointShares, Shares},
};

/// Run a ECDSA protocol
/// 
/// Uses the protocol from Securing DNSSEC Keys via Threshold ECDSA From Generic MPC
/// 
/// Steps:
/// 1. User independent preprocessing
/// 2. Generate circuit
/// 3. Evaluate circuit
/// 4. Verify signature from evaluated circuit
/// 5. PROFIT!
pub fn run_ecdsa(m: Nat, sk: Nat, modulus: NonZero<Nat>) -> (Nat, Nat) {
    // User independent preprocessing
    let preprocessed_tuple = user_independent_preprocessing(&modulus);

    // Share key
    let sk_shared = NatShares::new(&sk, modulus);

    // Generate circuit
    let (circuit, r_x) = ecdsa_circuit(m, sk_shared, preprocessed_tuple);

    // Evaluate circuit, return shared `s`
    let s_shared = circuit.eval();

    let s = s_shared.open().nat();

    // Output (r_x, s)
    let output = (r_x, s);

    // Verify signature
    todo!();
}

/// Generate tuple (<k>, [k_inv])
///
/// <k> is a shared point on the elliptic curve
/// [k_inv] is a shared scalar
fn user_independent_preprocessing(modulus: &NonZero<Nat>) -> (PointShares, NatShares) {
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

/// Generate circuit for ECDSA (Securing DNSSEC Keys via Threshold ECDSA From Generic MPC, page 11)
/// Does not include the user independent preprocessing
fn ecdsa_circuit(
    m: Nat,
    sk_shared: NatShares,
    preprocessed_tuple: (PointShares, NatShares),
) -> (Circuit, Nat) {
    // Create circuit
    let mut circuit: Circuit = Circuit {
        nodes: vec![],
        modulus: sk_shared.m,
    };

    let (k_point, k_inv) = preprocessed_tuple;

    // User dependent preprocessing

    // # Input nodes

    // [k_inv]
    let in_k_inv = Node::in_nat(k_inv);
    let in_k_inv_id = push_node(&mut circuit, in_k_inv);

    // [sk]
    let in_sk = Node::in_nat(sk_shared);
    let in_sk_id = push_node(&mut circuit, in_sk);

    // Compute [sk'] = [sk] * [k_inv]
    let sk_prime = Node::mul(in_sk_id, in_k_inv_id);
    let sk_prime_id = push_node(&mut circuit, sk_prime);

    // Open <k> to get R = (r_x, r_y). We only need r_x
    let r = AffinePoint::from(Shares::Point(k_point).open().point());
    let r_x: Nat = FieldBytesEncoding::decode_field_bytes(&r.x());

    // Compute H(m)
    let hashed_m = hash_message(m);

    // H(m) * [k_inv]
    let mul_message_k_inv =
        Node::mul_unary(in_k_inv_id, Const::Literal(ConstLiteral::Nat(hashed_m)));
    let mul_message_k_inv_id = push_node(&mut circuit, mul_message_k_inv);

    // r_x * [sk']
    let mul_r_x_sk_prime = Node::mul_unary(sk_prime_id, Const::Literal(ConstLiteral::Nat(r_x)));
    let mul_r_x_sk_prime_id = push_node(&mut circuit, mul_r_x_sk_prime);

    // Compute e = H(m) * [k_inv] + r_x * [sk']
    let s = Node::add(mul_message_k_inv_id, mul_r_x_sk_prime_id);
    push_node(&mut circuit, s);

    return (circuit, r_x);
}

/// Compute H(m) = sha256(m)
fn hash_message(m: Nat) -> Nat {
    let m_bytes = m.to_be_bytes();

    let mut hasher = Sha256::new();

    hasher.update(&m_bytes);
    let result = hasher.finalize();

    return Nat::from_le_slice(&result[..]);
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
