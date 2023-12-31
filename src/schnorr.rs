use crypto_bigint::Encoding;
use sha2::{Digest, Sha256};

use crate::{
    circuit::{push_node, Circuit},
    groups::GroupSpec,
    nat::{mul_mod, pow_mod, Nat},
    node::{Const, ConstLiteral, Node},
    shares::NatShares,
};

/// Sign m using threshold Schnorr and assert that the signature is valid for the message
///
/// Step 1: Generate a signature on m using schnorr where the secret key has been shared between 2 parties
/// Step 2: Verify the signature
pub fn run_treshold_schnorr(
    m: Nat,
    verbose: bool,
    g_r1: Nat,
    g_r2: Nat,
    r1: Nat,
    r2: Nat,
    group: GroupSpec,
) {
    // Generate a secret key
    let sk = group.rand_exp();
    // Compute the beta of the public key
    let beta = pow_mod(&group.alpha, &sk, &group.p);

    // They both compute g^r1 * g^r2 mod p = g^(r1 + r2) mod p = g^r mod p = c
    let c = mul_mod(&g_r1, &g_r2, &group.p);

    // They both compute e = H(c, m)
    let e = compute_e(c, m);

    // Create the share for the random value r
    let r_shares = NatShares {
        x: r1,
        y: r2,
        m: group.q,
    };

    // Create the share for the secret key
    let sk_share = NatShares::new(&sk, group.q);

    // Construct net schnorr circuit
    let circuit = schnorr_circuit(r_shares, sk_share, e);

    // Evaluate the circuit
    let result = circuit.eval();

    // Open the result to get the second component z of the signature
    let s = result.open().nat();

    println!("Signature: ({:?}, {:?})", e, s);

    // Compute beta inverted in mod p
    let (beta_inv, choice) = beta.inv_mod(&group.p);

    // Chekck that beta is invertible in mod p
    if !bool::from(choice) {
        panic!("e is not invertible in mod p");
    }

    // Compute c_verify = g^z * beta^-e mod p
    let c_verify = mul_mod(
        &pow_mod(&group.alpha, &s, &group.p),
        &pow_mod(&beta_inv, &e, &group.p),
        &group.p,
    );

    // Compute e_verify = Sha256(c_verify, m)
    let e_verify = compute_e(c_verify, m);

    if verbose {
        println!("group: {:?}", group);
        println!("r1: {:?}", r1);
        println!("r2: {:?}", r2);
        println!("g: {:?}", group.alpha);
        println!("g^r1: {:?}", g_r1);
        println!("g^r2: {:?}", g_r2);
        println!("c: {:?}", c);
        println!("e: {:?}", e);
        println!("sk: {:?}", sk);
        println!("z: {:?}", s);
        println!("beta: {:?}", beta);
        println!("e_inv: {:?}", beta_inv);
        println!("c_verify: {:?}", c_verify);
        println!("e_verify: {:?}", e_verify);
    }

    // Check that e_verify = e
    if e_verify != e {
        panic!("Signature is not valid");
    }

    println!("Signature verified");
}

/// Preprocess the modulus of the group
pub fn preprocess_mod(group: &GroupSpec) -> (Nat, Nat, Nat, Nat) {
    // Step 1: Agreeing on a secret random value r from Zq
    // Alice chooses a random r1 from Zq
    let r1 = group.rand_exp();
    // Bob chooses a random r2 from Zq
    let r2 = group.rand_exp();

    // Alice computes g^r1 mod p and sends it to Bob
    let g_r1 = pow_mod(&group.alpha, &r1, &group.p);
    // Bob computes g^r2 mod p and sends it to Alice
    let g_r2 = pow_mod(&group.alpha, &r2, &group.p);
    (g_r1, g_r2, r1, r2)
}

/// Schnorr circuit consists of four nodes:
///
/// 1. An input node for the secret key
/// 2. An input node for the random
/// 3. A mul node for computing e * [sk]
/// 4. An add node for computing [r] + [e * sk]
pub fn schnorr_circuit(r: NatShares, sk: NatShares, e: Nat) -> Circuit {
    // Check that the modulus of the shares are the same
    assert!(r.m == sk.m);
    let mut g: Circuit = Circuit {
        nodes: vec![],
        modulus: r.m,
    };

    // Add the input nodes
    let in_sk = Node::in_nat(sk);
    let in_sk_id = push_node(&mut g, in_sk);

    let in_r = Node::in_nat(r);
    let in_r_id = push_node(&mut g, in_r);

    // Compute z = r + e * sk
    let mul_e = Node::mul_unary(in_sk_id, Const::Literal(ConstLiteral::Nat(e)));
    let mul_e_id = push_node(&mut g, mul_e);

    // Add r and e * sk
    let z = Node::add(in_r_id, mul_e_id);
    let _ = push_node(&mut g, z);
    g
}

// Compute e = sha256(c, m)
pub fn compute_e(c: Nat, m: Nat) -> Nat {
    let c_bytes = c.to_be_bytes();
    let c_m_bytes = [c_bytes, m.to_be_bytes()].concat();

    let mut hasher = Sha256::new();

    hasher.update(&c_m_bytes);
    let result = hasher.finalize();
    Nat::from_le_slice(&result[..])
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_schnorr_circuit() {
        // Run through the schnorr protocol
        let group = GroupSpec::new();
        let (g_r1, g_r2, r1, r2) = preprocess_mod(&group);
        run_treshold_schnorr(Nat::from_u16(1337), true, g_r1, g_r2, r1, r2, group);
    }
}
