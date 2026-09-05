import FormalConjectures.OEIS.«51903»

/-! Reusable factor-list and local-order bridges for the A051903 witness. -/

namespace D14.Bridges

/-- A sorted prime factor list determines the upstream maximum exponent. -/
theorem maximumExponent_from_primeList {n : ℕ} {l : List ℕ}
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, Nat.Prime p)
    (hsorted : l.Pairwise (· ≤ ·)) :
    OeisA51903.a n = (l.map (fun p => l.count p)).foldr max 0 := by
  have h : n.primeFactorsList = l :=
    ((Nat.primeFactorsList_unique hprod hprime).eq_of_pairwise'
      hsorted (Nat.primeFactorsList_sorted n).pairwise).symm
  simp only [OeisA51903.a, h]

/-- Specialize `m` to a prime power for the local multiplicative-order condition. -/
theorem order_dvd_iff_modEq (b m k : ℕ) :
    orderOf (b : ZMod m) ∣ k ↔ b ^ k ≡ 1 [MOD m] := by
  rw [orderOf_dvd_iff_pow_eq_one]
  simpa only [Nat.cast_pow, Nat.cast_one] using
    (ZMod.natCast_eq_natCast_iff (b ^ k) 1 m)

end D14.Bridges

#print axioms D14.Bridges.maximumExponent_from_primeList
#print axioms D14.Bridges.order_dvd_iff_modEq
