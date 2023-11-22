use crate::shares::Nat;

/// A specification of the subgroup from Zp of prime order q,
/// where p is a safe prime with associated Sofie Germain prime q
pub struct GroupSpec {
    /// Primes p and q where p = 2q+1
    p: Nat,
    q: Nat,
    /// Generator of the group, ord(g) = q
    g: Nat,
}

// impl GroupSpec {
//     /// Constructs a new group spec with security parameter k
//     /// i.e. k is the size of q
//     fn new(_: Nat) -> GroupSpec {

//         // GroupSpec { p: (), q: (), g: () }
//         todo!()
//     }
// }
