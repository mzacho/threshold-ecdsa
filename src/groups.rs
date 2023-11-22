use crypto_bigint::{rand_core::OsRng, RandomMod, NonZero};
use crate::shares::Nat;

/// A specification of the subgroup from Zp of prime order q,
/// where p is a safe prime with associated Sofie Germain prime q
pub struct GroupSpec {
    /// Primes p and q where p = 2q+1
    pub p: NonZero<Nat>,
    pub q: NonZero<Nat>,
    /// Generator of the group, ord(g) = q
    pub g: Nat,
}

impl GroupSpec {
    /// Constructs a new group spec with security parameter k
    /// i.e. k is the bitsize of q = M
    pub fn new() -> GroupSpec {

        // GroupSpec { p: (), q: (), g: () }
        todo!()
    }

    /// Returns a random from Zq
    pub fn rand_exp(&self) -> Nat {
        Nat::random_mod(&mut OsRng, &self.q)
    }
}

///// Sample random generator of Zp* assuming p = self is a safe prime
/////
///// We use the fact that alpha is a generator for Zp* iff
///// alpha ^ ((p-1)/q) != 1 for every q divisor in p - 1 (Lemma
///// 9.8 from the notes on cryptography by Ivan Damgaard)
/////
///// Since p is a safe prime, the only divisors of p - 1 are q
///// and 2.
///// fn generator_from_safe_prime(p: Nat) -> Nat {
//     // Sample random x in Zp*
//     // Since Zp* = {1, 2, ..., p-1} we do this by picking x at
//     // random from Z(p-1) = {0, 1, ..., p-2} and adding one.

//     let mut x = Nat::random_mod(&mut OsRng, &p);
//     let mut x = p.minus_one().rand_modulo().plus_one();

//     // q is the sophie germain prime associated with p
//     let q = p.minus_one().div_two();

//     let mut divisors = vec![2, q];
//     // Loop while we still have divisors to check

//     loop {
//         match divisors.pop() {
//             Some(mut i) => {
//                 // Compose x with itself i times and check that
//                 // none of the compositions yield the neutral
//                 // element, i.e. if x_clone == 1 at any time then
//                 // x is not a generator of Zp* since ord(x) < p-1.
//                 let mut x_clone = x;
//                 while i != 1 && x_clone != 1 {
//                     // Zp* is a multiplicative group
//                     x_clone *= x;
//                     // Reduce mod p to get back into the group
//                     x_clone %= p;
//                     i = i - 1;
//                 }
//                 // Assert that x ^ i != 1
//                 if x_clone == 1 {
//                     // x is not a generator, pick a new candidate
//                     x = p.minus_one().rand_modulo().plus_one();
//                     divisors = vec![2, q];
//                 }
//             }
//             None => {
//                 // In this case x ^ 2 % p != 1 and x ^ q % p != 1
//                 // so x is a generator of Zp*. Break and return x.
//                 break;
//             }
//         }
//     }
//     x
// }
