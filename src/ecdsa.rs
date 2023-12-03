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

/// Convert shares of a value "a" to a share of the representation of the point on the curve for the value "a"
pub fn convert(shares: Shares) -> CurveShares {
    let x = Scalar::from_uint_unchecked(shares.x);
    let y = Scalar::from_uint_unchecked(shares.y);

    let xi = Point::mul_by_generator(&x);
    let yi = Point::mul_by_generator(&y);

    CurveShares { x: xi, y: yi }
}

#[cfg(test)]
mod tests {
    use crypto_bigint::{rand_core::OsRng, NonZero};
    use p224::ecdsa::{
        signature::Signer, signature::Verifier, Signature, SigningKey, VerifyingKey,
    };

    use crate::nat::Nat;

    use super::*;

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

    #[test]
    fn test_convert() {
        let m = NonZero::new(Nat::from(1337_u128)).unwrap();
        let x = Nat::new(Nat::from(42_u128).into());
        let _ = convert(Shares::new(&x, m));
    }
}
