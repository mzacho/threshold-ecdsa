use elliptic_curve::ops::MulByGenerator;
use elliptic_curve::scalar::FromUintUnchecked;

use crate::curve::{Point, Scalar};
use crate::shares::{CurveShares, Shares};

// pub fn run_ecdsa() {
//     todo!()
// }

// pub fn circuit_ecdsa() {
//     todo!()
// }

#[cfg(test)]
mod tests {
    use crypto_bigint::{rand_core::OsRng};
    use p224::ecdsa::{
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
