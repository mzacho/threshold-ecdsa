use std::env;

use crypto_bigint::{Encoding, NonZero};

use elliptic_curve::scalar::FromUintUnchecked;
use elliptic_curve::{ops::Mul, ops::MulByGenerator, point::AffineCoordinates, FieldBytesEncoding};
use k256::AffinePoint;

use sha2::{Digest, Sha256};

use crate::{
    circuit::{deal_rands, push_node, Circuit, Rands},
    curve::{self, Point},
    nat::{mul_mod, Nat},
    node::{Const, ConstLiteral, Node},
    shares::{NatShares, PointShares, Shares},
};

/// Run a ECDSA protocol
///
/// Uses the protocol from Securing DNSSEC Keys via Threshold ECDSA From Generic MPC
///
/// 1. Sign message
/// 2. Verify signature
/// 3. PROFIT!
pub fn run_ecdsa(message: Nat) {
    // Generate a keys
    let (sk_shared, pk) = keygen();

    // Sign message
    let signature = sign_message(message, sk_shared);

    // Verify signature
    assert!(verify_signature(message, signature, pk));
}

/// Sign a message
///
/// Using ABB+ protocol from Securing DNSSEC Keys via Threshold ECDSA From Generic MPC
///
/// Steps:
/// 1. User independent preprocessing to compute k^-1
/// 2. Generate circuit
/// 3. Evaluate circuit
/// 3. Return signature: (r, s)
fn sign_message(m: Nat, sk_shared: NatShares) -> (Nat, Nat) {
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

    // Calculate the signature validation result by comparing wether r' = r
    println!("r_prime_x: \t{}", r_prime_x);
    println!("r_x: \t\t{}", r);
    println!("r_prime_x == r: {}", r_prime_x == r);

    return r_prime_x == r;
}

/// Generate public key
///
/// Returns a point on the curve
/// pk = Open(Convert(\[sk\]))
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
fn keygen() -> (NatShares, Point) {
    let sk = curve::rand_mod_order();
    let sk_shared = NatShares::new(&sk, curve::nonzero_order());
    let pk = generate_public_key(sk_shared.clone());
    (sk_shared, pk)
}

/// Compute H(m) = sha256(m)
fn hash_message(m: Nat) -> Nat {
    let m_bytes = m.to_be_bytes();

    let mut hasher = Sha256::new();

    hasher.update(&m_bytes);
    let result = hasher.finalize();

    return Nat::from_le_slice(&result[..]);
}

pub fn read_args_message(args: env::Args) -> Nat {
    let args: Vec<String> = args.collect();
    let m = Nat::from(args.get(2).unwrap().parse::<u128>().unwrap());
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_ecdsa() {
        run_ecdsa(Nat::from_u16(1337));
    }

    #[test]
    fn test_threshold_ecdsa_positive() {
        // Test that sign/verify of 100 random messages
        let mut i = 0;
        while i < 100 {
            let message = curve::rand_mod_order();

            let (sk_shared, pk) = keygen();
            let s = sign_message(message, sk_shared);
            assert!(verify_signature(message, s, pk));
            i = i + 1;
        }
        run_ecdsa(Nat::from_u16(1337));
    }

    #[test]
    fn test_threshold_ecdsa_negative() {
        // Test that sign/verify of 100 random messages
        // m1 and m2 where m1 != m2
        let mut i = 0;
        while i < 100 {
            let m1 = curve::rand_mod_order();
            let m2 = curve::rand_mod_order();
            if m1 == m2 {
                continue;
            }

            let (sk_shared, pk) = keygen();
            let s = sign_message(m1, sk_shared);
            assert!(!verify_signature(m2, s, pk));
            i = i + 1;
        }
    }
}
