use elliptic_curve::ProjectivePoint;

pub type Curve = k256::Secp256k1;

pub type Point = ProjectivePoint<Curve>;

pub type Scalar = k256::Scalar;

#[cfg(test)]
mod test {
    use super::*;
    use crate::nat::Nat;
    use elliptic_curve::scalar::FromUintUnchecked;
    use elliptic_curve::ops::MulByGenerator;

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
}
