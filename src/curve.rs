use crate::nat::Nat;
use elliptic_curve::{ProjectivePoint, Curve as EC_CURVE};

/// The curve with parameters used by bitcoins pke
pub type Curve = k256::Secp256k1;

/// Order of the curve.
pub const ORDER: Nat = Curve::ORDER;

/// A point on the curve
pub type Point = ProjectivePoint<Curve>;

/// A scalar in the underlying field of the curve
/// The ECDSA sk is such a scalar
pub type Scalar = k256::Scalar;

#[cfg(test)]
mod test {
    use super::*;
    use crate::nat::Nat;
    use elliptic_curve::ops::MulByGenerator;
    use elliptic_curve::scalar::FromUintUnchecked;

    #[test]
    fn test_compare_scalars() {
        let x = Nat::from_u32(1337_u32);
        let y = Scalar::from_uint_unchecked(x);
        let z = Scalar::from_uint_unchecked(x);
        assert_eq!(y, z)
    }

    #[test]
    fn test_compare_points1() {
        let x = Nat::from_u32(1337_u32);
        let x_scalar = Scalar::from_uint_unchecked(x);
        let x_point = Point::mul_by_generator(&x_scalar);

        let y = Nat::from_u32(1337_u32);
        let y_scalar = Scalar::from_uint_unchecked(y);
        let y_point = Point::mul_by_generator(&y_scalar);

        assert_eq!(x_point, y_point);

        let z = Nat::from_u32(42_u32);
        let z_scalar = Scalar::from_uint_unchecked(z);
        let z_point = Point::mul_by_generator(&z_scalar);

        assert_ne!(x_point, z_point);
    }

    /// Test that for scalar a: a*G = G+G+G+...+G
    /// where G is the generator of the curve
    #[test]
    fn test_mul_by_generator() {
        let four = Nat::from_u32(4_u32);
        let a = Scalar::from_uint_unchecked(four);
        let x = Point::mul_by_generator(&a);

        let y = Point::mul_by_generator(&Scalar::ONE)
            + Point::mul_by_generator(&Scalar::ONE)
            + Point::mul_by_generator(&Scalar::ONE)
            + Point::mul_by_generator(&Scalar::ONE);

        assert_eq!(x, y);

        let eleven = Nat::from_u32(11_u32);
        let a = Scalar::from_uint_unchecked(eleven);
        let x = Point::mul_by_generator(&a);

        // 4 + 4 + 3 = 11
        let y = y
            + y
            + Point::mul_by_generator(&Scalar::ONE)
            + Point::mul_by_generator(&Scalar::ONE)
            + Point::mul_by_generator(&Scalar::ONE);

        assert_eq!(x, y);
    }
}
