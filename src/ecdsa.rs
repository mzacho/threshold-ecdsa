// pub fn run_ecdsa() {
//     todo!()
// }

use crypto_bigint::NonZero;

use crate::{
    circuit::{deal_rands, Rands},
    nat::Nat,
    shares::{PointShares, NatShares},
};

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

pub fn user_dependent_preprocessing() {
    todo!()
}

// pub fn circuit_ecdsa() {
//     todo!()
// }

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
