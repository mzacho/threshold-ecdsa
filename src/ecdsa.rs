// https://docs.rs/fiat-crypto/0.2.5/fiat_crypto/index.html
// https://docs.rs/k256/latest/k256/

// https://docs.rs/elliptic-curve/latest/elliptic_curve/
use ecdsa::Signature;
use elliptic_curve::{group::prime::PrimeCurveAffine, point::*};

use crate::shares::Shares;

pub fn run_ecdsa() {
    todo!()
}

pub fn circuit_ecdsa() {
    todo!()
}

/// Convert shares of a value "a" to a share of the representation of the point on the curve for the value "a"
pub fn convert<Curve: PrimeCurveAffine>(
    shares: Shares,
    curve: Curve,
) {
  let g = Curve::generator().mul(shares.x);

  let group_shares = Shares {
    x: shares.x.mul(&g),
    y: g,
    m: shares.m,
  };
}
