use elliptic_curve::ProjectivePoint;

pub type Curve = p224::NistP224;

pub type Point = ProjectivePoint<Curve>;

pub type Scalar = p224::Scalar;
