use crypto_bigint::rand_core::OsRng;
use crypto_bigint::{Encoding, NonZero};

use elliptic_curve::scalar::FromUintUnchecked;
use elliptic_curve::{ops::Mul, ops::MulByGenerator, point::AffineCoordinates, FieldBytesEncoding};
use k256::AffinePoint;

use k256::ecdsa::{signature::Verifier, VerifyingKey};
use k256::ecdsa::{Signature, SigningKey};
use k256::schnorr::signature::Signer;
use sha2::{Digest, Sha256};

use crate::{
    circuit::{deal_rands, push_node, Circuit, Rands},
    curve::{self, Point},
    nat::{mul_mod, Nat},
    node::{Const, ConstLiteral, Node},
    shares::{NatShares, PointShares, Shares},
};

/// Signs message using threshold ECDSA and asserts that the signature
/// is valid for the message.
///
/// Uses the protocol from Securing DNSSEC Keys via Threshold ECDSA From Generic MPC
pub fn run_threshold_ecdsa(message: Nat) {
    // Generate a keys
    let (_, sk_shared, pk) = keygen();

    // Sign message
    let signature = threshold_sign_message(message, sk_shared);

    println!("Signature: {:?}", signature);

    // Verify signature
    assert!(verify_signature(message, signature, pk));

    println!("Signature verified");
}

/// Signs message using plain ECDSA and asserts the signature is valid.
///
/// Used for benchmarking
/// Uses the protocol from https://cryptobook.nakov.com/digital-signatures/ecdsa-sign-verify-messages
#[allow(dead_code)]
pub fn run_ecdsa(message: Nat) {
    // Generate a keys
    let (sk, _, pk) = keygen();

    // Sign message
    let signature = sign_message(message, sk);

    // Verify signature
    assert!(verify_signature(message, signature, pk));
}

/// Use the ECDSA protocol package for benchmarking
/// Use https://github.com/RustCrypto/elliptic-curves/tree/master/k256
#[allow(dead_code)]
pub fn run_ecdsa_benchmarking(message: Nat) {
    // Generate a keys

    // Signing
    let signing_key = SigningKey::random(&mut OsRng);

    let signature: Signature = signing_key.sign(message.to_string().as_bytes());

    // Verification
    let verifying_key = VerifyingKey::from(&signing_key);
    assert!(verifying_key
        .verify(message.to_string().as_bytes(), &signature)
        .is_ok());
}

/// Sign a message with BeDOZa
///
/// Using ABB+ protocol from Securing DNSSEC Keys via Threshold ECDSA From Generic MPC
///
/// Steps:
/// 1. User independent preprocessing to compute k^-1
/// 2. Generate circuit
/// 3. Evaluate circuit
/// 3. Return signature: (r, s)
fn threshold_sign_message(m: Nat, sk_shared: NatShares) -> (Nat, Nat) {
    // User independent preprocessing
    let preprocessed_tuple = user_independent_preprocessing(&curve::nonzero_order());

    // Generate circuit
    let (mut circuit, r_x) = ecdsa_circuit(m, sk_shared.clone(), preprocessed_tuple);

    // Convert mul gates
    circuit.transform_mul_gates();

    // Evaluate circuit, return shared `s`
    let s_shared = circuit.eval();

    let s = s_shared.open().nat();

    return (r_x, s);
}

/// Verify a signature
///
/// Based on https://cryptobook.nakov.com/digital-signatures/ecdsa-sign-verify-messages
///
/// Arguments:
/// - `m`: message
/// - `signature`: (r, s)
/// - `pk`: public key - Open(Convert(\[sk\]))
fn verify_signature(m: Nat, signature: (Nat, Nat), pk: Point) -> bool {
    let (r, s) = signature;

    // Calculate the hash of the message
    let h = hash_message(m);

    // Calculate the modular inverse of the signature proof s
    let (s_inv, s_inv_exists) = s.inv_mod(&curve::nonzero_order());
    if !bool::from(s_inv_exists) {
        panic!("s inverse does not exist")
    }

    // Recover Random point used during the signing R' = (h * s_inv) * G + (r * s_inv) * pk
    let h_mul_s_inv =
        curve::Scalar::from_uint_unchecked(mul_mod(&s_inv, &h, &curve::nonzero_order()));
    let r_mul_s_inv =
        curve::Scalar::from_uint_unchecked(mul_mod(&s_inv, &r, &curve::nonzero_order()));

    let r_prime = AffinePoint::from(Point::mul_by_generator(&h_mul_s_inv) + pk.mul(r_mul_s_inv));

    // Take from R' it's x coordinate r' = R'.x
    let r_prime_x: Nat = FieldBytesEncoding::decode_field_bytes(&r_prime.x());

    return r_prime_x == r;
}

/// Generate public key
///
/// Returns a point on the curve
/// `pk = Open(Convert([sk]))` or `pk = sk * G`
fn generate_public_key(sk_shared: NatShares) -> Point {
    let sk_convert = PointShares::convert(sk_shared);
    let pk = Shares::Point(sk_convert).open().point();
    return pk;
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

    (k_point_share, k_inv)
}

/// Generate circuit for ECDSA (Securing DNSSEC Keys via Threshold ECDSA From Generic MPC, page 11)
/// Does not include the user independent preprocessing
fn ecdsa_circuit(
    message: Nat,
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
    let hashed_m = hash_message(message);

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

    (circuit, r_x)
}

/// Generate ECDSA keypair where sk is secret shared
fn keygen() -> (Nat, NatShares, Point) {
    let sk = curve::rand_mod_order();
    let sk_shared = NatShares::new(&sk, curve::nonzero_order());
    let pk = generate_public_key(sk_shared.clone());
    (sk, sk_shared, pk)
}

/// Compute H(m) = sha256(m)
fn hash_message(m: Nat) -> Nat {
    let m_bytes = m.to_be_bytes();

    let mut hasher = Sha256::new();

    hasher.update(&m_bytes);
    let result = hasher.finalize();

    return Nat::from_be_slice(&result[..]);
}

/// Sign a message with plain ECDSA (no BeDOZa)
///
/// Based on https://cryptobook.nakov.com/digital-signatures/ecdsa-sign-verify-messages
#[allow(dead_code)]
fn sign_message(message: Nat, sk: Nat) -> (Nat, Nat) {
    // Calculate the hash of the message
    let h = hash_message(message);

    // Generate a random number k
    let k = curve::rand_mod_order();

    // Calculate random point R = k * G and take its x coordinate r_x = R.x
    let r_x = FieldBytesEncoding::decode_field_bytes(
        &AffinePoint::from(Point::mul_by_generator(
            &curve::Scalar::from_uint_unchecked(k),
        ))
        .x(),
    );

    // Calculate the modular inverse of k
    let (k_inv, k_inv_exists) = k.inv_mod(&curve::nonzero_order());
    if !bool::from(k_inv_exists) {
        panic!("k inverse does not exist")
    }

    // Calculate the signature proof s = (h + r_x * sk) * k_inv
    let h_plus_r_x_sk =
        mul_mod(&r_x, &sk, &curve::nonzero_order()).add_mod(&h, &curve::nonzero_order());
    let s = mul_mod(&h_plus_r_x_sk, &k_inv, &curve::nonzero_order());

    (r_x, s)
}

#[cfg(test)]
mod tests_threshold {
    use super::*;

    #[test]
    fn test_run_ecdsa() {
        run_threshold_ecdsa(Nat::from_u16(1337));
    }

    #[test]
    fn test_threshold_ecdsa_bedoza_positive() {
        // Test that sign/verify of 100 random messages
        let mut i = 0;
        while i < 100 {
            let message = curve::rand_mod_order();

            let (_, sk_shared, pk) = keygen();
            let s = threshold_sign_message(message, sk_shared);
            assert!(verify_signature(message, s, pk));
            i = i + 1;
        }
        run_threshold_ecdsa(Nat::from_u16(1337));
    }

    #[test]
    fn test_threshold_ecdsa_bedoza_negative() {
        // Test that sign/verify of 100 random messages
        // m1 and m2 where m1 != m2
        let mut i = 0;
        while i < 100 {
            let m1 = curve::rand_mod_order();
            let m2 = curve::rand_mod_order();
            if m1 == m2 {
                continue;
            }

            let (_, sk_shared, pk) = keygen();
            let s = threshold_sign_message(m1, sk_shared);
            assert!(!verify_signature(m2, s, pk));
            i = i + 1;
        }
    }
}

#[cfg(test)]
mod tests_plain {
    use super::*;
    use k256::ecdsa::{signature::Verifier, Signature, SigningKey, VerifyingKey};

    // Convert ECDSA signature (r, s) from nats to ecdsa::Signature
    fn sig_from_nats(r: Nat, s: Nat) -> Signature {
        let r_bytes = r.to_be_bytes();
        let s_bytes = s.to_be_bytes();
        let sig = Signature::from_scalars(r_bytes, s_bytes).unwrap();
        sig.normalize_s().unwrap_or(sig)
    }

    #[test]
    fn test_threshold_sign_verifies_with_rustcrypto() {
        // Serialize a new message
        let m = Nat::from_u8(42);
        let message = &m.to_be_bytes();
        // Generate keypair
        let (sk, sks, _) = keygen();
        let sk = SigningKey::from_slice(&sk.to_be_bytes()).unwrap();
        // Threshold sign message
        let (r, s) = threshold_sign_message(m, sks);
        let sig = sig_from_nats(r, s);
        // let _: Signature = sk.sign(message);
        // Verify with RustCrypto
        let pk = VerifyingKey::from(sk);
        assert!(pk.verify(message, &sig).is_ok());
    }

    #[test]
    fn test_run_ecdsa() {
        run_ecdsa(Nat::from_u16(1337));
    }

    #[test]
    fn test_threshold_ecdsa_plain_positive() {
        // Test that sign/verify of 100 random messages
        let mut i = 0;
        while i < 100 {
            let message = curve::rand_mod_order();

            let (sk, _, pk) = keygen();
            let s = sign_message(message, sk);
            assert!(verify_signature(message, s, pk));
            i = i + 1;
        }
        run_ecdsa(Nat::from_u16(1337));
    }

    #[test]
    fn test_threshold_ecdsa_plain_negative() {
        // Test that sign/verify of 100 random messages
        // m1 and m2 where m1 != m2
        let mut i = 0;
        while i < 100 {
            let m1 = curve::rand_mod_order();
            let m2 = curve::rand_mod_order();
            if m1 == m2 {
                continue;
            }

            let (sk, _, pk) = keygen();
            let s = sign_message(m1, sk);
            assert!(!verify_signature(m2, s, pk));
            i = i + 1;
        }
    }
}
