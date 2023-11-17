use crate::shares::Nat;

/// A specification of the subgroup from Zp of prime order q
struct SafePrimeGroupSpec {
    /// Primes p and q where p = 2q+1
    p: Nat,
    q: Nat,
    /// Generator of the group, ord(g) = q
    g: Nat,
}

impl SafePrimeGroupSpec {
    /// Constructs a new group spec with security parameter k
    /// i.e. k is the size of q
    fn new(k: Nat) -> SafePrimeGroupSpec {

    }
}
