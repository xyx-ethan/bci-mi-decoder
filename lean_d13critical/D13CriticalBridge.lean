import D13CriticalFermat

/-!
# D13 Round 25: bridge the two critical residual certificates to the upstream encoding

The preceding round proves that `q1 3` and `q2 0` are not prime.  This module
connects those certificates back to the actual `OeisA67599.a` definition.  It
excludes the corresponding two-prime fixed-point strata with decimal lengths
733 and 666, without using the research-open conjecture.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

namespace D13Round25

open OeisA67599

/-- Recover the ordered prime-factor list from an explicit sorted prime list. -/
theorem factors_from_sorted (n : ℕ) (l : List ℕ)
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, Nat.Prime p)
    (hsort : l.Pairwise (· ≤ ·)) : n.primeFactorsList = l := by
  exact ((Nat.primeFactorsList_unique hprod hprime).eq_of_pairwise'
    hsort (Nat.primeFactorsList_sorted n).pairwise).symm

/-- The exact ordered factor list for `7^4 * q` when `q` is a larger prime. -/
theorem factors7 (q : ℕ) (hq : q.Prime) (h7 : 7 < q) :
    ((7 : ℕ) ^ 4 * q).primeFactorsList = [7, 7, 7, 7, q] := by
  apply factors_from_sorted
  · norm_num
    ring
  · have hp : Nat.Prime 7 := by norm_num
    simp_all
  · simp [List.pairwise_cons, le_of_lt h7]

/-- The exact ordered factor list for `3^7 * q` when `q` is a larger prime. -/
theorem factors3 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    ((3 : ℕ) ^ 7 * q).primeFactorsList = [3, 3, 3, 3, 3, 3, 3, q] := by
  apply factors_from_sorted
  · norm_num
    ring
  · have hp : Nat.Prime 3 := by norm_num
    simp_all
  · simp [List.pairwise_cons, le_of_lt h3]

/-- Evaluate the real upstream encoding on the `7^4 * q` branch. -/
theorem encoding7 (q : ℕ) (hq : q.Prime) (h7 : 7 < q) :
    OeisA67599.a ((7 : ℕ) ^ 4 * q) =
      740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1 := by
  have hn : ¬ (7 : ℕ) ^ 4 * q < 2 := by
    norm_num
    omega
  have hne : q ≠ 7 := ne_of_gt h7
  have hne' : 7 ≠ q := ne_of_lt h7
  unfold OeisA67599.a
  rw [if_neg hn, factors7 q hq h7]
  norm_num [OeisA67599.concatenateNats, List.dedup, List.pwFilter, hne, hne']
  ring

/-- Evaluate the real upstream encoding on the `3^7 * q` branch. -/
theorem encoding3 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    OeisA67599.a ((3 : ℕ) ^ 7 * q) =
      370 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1 := by
  have hn : ¬ (3 : ℕ) ^ 7 * q < 2 := by
    norm_num
    omega
  have hne : q ≠ 3 := ne_of_gt h3
  have hne' : 3 ≠ q := ne_of_lt h3
  unfold OeisA67599.a
  rw [if_neg hn, factors3 q hq h3]
  norm_num [OeisA67599.concatenateNats, List.dedup, List.pwFilter, hne, hne']
  ring

/-- A fixed point in the `7^4*q` branch with a 733-digit prime factor would
force that factor to equal the Round-24 critical residual. -/
theorem fixed7_digit733_forces_critical (q : ℕ)
    (hq : q.Prime) (h7 : 7 < q)
    (hdigits : (Nat.digits 10 q).length = 733)
    (hfix : OeisA67599.a ((7 : ℕ) ^ 4 * q) = (7 : ℕ) ^ 4 * q) :
    q = D13Round24.q1Critical := by
  rw [encoding7 q hq h7, hdigits] at hfix
  norm_num only [show (7 : ℕ) ^ 4 = 2401 by decide] at hfix
  have heq : 2391 * q = 740 * 10 ^ 733 + 1 := by omega
  have hq_q1 : q = D13Round24.q1 3 := by
    unfold D13Round24.q1 D13Round24.Q
    change q = (740 * 10 ^ 733 + 1) / 2391
    rw [← heq]
    exact (Nat.mul_div_cancel_left q (by decide : 0 < 2391)).symm
  exact hq_q1.trans D13Round24.q1_formula

/-- A fixed point in the `3^7*q` branch with a 666-digit prime factor would
force that factor to equal the Round-24 critical residual. -/
theorem fixed3_digit666_forces_critical (q : ℕ)
    (hq : q.Prime) (h3 : 3 < q)
    (hdigits : (Nat.digits 10 q).length = 666)
    (hfix : OeisA67599.a ((3 : ℕ) ^ 7 * q) = (3 : ℕ) ^ 7 * q) :
    q = D13Round24.q2Critical := by
  rw [encoding3 q hq h3, hdigits] at hfix
  norm_num only [show (3 : ℕ) ^ 7 = 2187 by decide] at hfix
  have heq : 2177 * q = 370 * 10 ^ 666 + 1 := by omega
  have hq_q2 : q = D13Round24.q2 0 := by
    unfold D13Round24.q2 D13Round24.Q
    change q = (370 * 10 ^ 666 + 1) / 2177
    rw [← heq]
    exact (Nat.mul_div_cancel_left q (by decide : 0 < 2177)).symm
  exact hq_q2.trans D13Round24.q2_formula

/-- No 733-digit prime can complete the `7^4*q` critical fixed-point stratum. -/
theorem no_fixed7_digit733 :
    ¬ ∃ q : ℕ, q.Prime ∧ 7 < q ∧
      (Nat.digits 10 q).length = 733 ∧
      OeisA67599.a ((7 : ℕ) ^ 4 * q) = (7 : ℕ) ^ 4 * q := by
  rintro ⟨q, hq, h7, hdigits, hfix⟩
  have hqeq := fixed7_digit733_forces_critical q hq h7 hdigits hfix
  apply D13Round24.q1Critical_not_prime
  rw [← hqeq]
  exact hq

/-- No 666-digit prime can complete the `3^7*q` critical fixed-point stratum. -/
theorem no_fixed3_digit666 :
    ¬ ∃ q : ℕ, q.Prime ∧ 3 < q ∧
      (Nat.digits 10 q).length = 666 ∧
      OeisA67599.a ((3 : ℕ) ^ 7 * q) = (3 : ℕ) ^ 7 * q := by
  rintro ⟨q, hq, h3, hdigits, hfix⟩
  have hqeq := fixed3_digit666_forces_critical q hq h3 hdigits hfix
  apply D13Round24.q2Critical_not_prime
  rw [← hqeq]
  exact hq

/-- The two formerly persistent critical fixed-point strata are both empty. -/
theorem no_critical_fixed_point_strata :
    (¬ ∃ q : ℕ, q.Prime ∧ 7 < q ∧
      (Nat.digits 10 q).length = 733 ∧
      OeisA67599.a ((7 : ℕ) ^ 4 * q) = (7 : ℕ) ^ 4 * q) ∧
    (¬ ∃ q : ℕ, q.Prime ∧ 3 < q ∧
      (Nat.digits 10 q).length = 666 ∧
      OeisA67599.a ((3 : ℕ) ^ 7 * q) = (3 : ℕ) ^ 7 * q) :=
  ⟨no_fixed7_digit733, no_fixed3_digit666⟩

-- Kernel-level semantic and ordering controls for the upstream concatenation.
example : OeisA67599.a 0 = 0 := by decide
example : OeisA67599.a 1 = 0 := by decide
example : OeisA67599.concatenateNats 31 51 = 3151 := by
  norm_num [OeisA67599.concatenateNats]
example : OeisA67599.concatenateNats 31 51 ≠ 3511 := by
  norm_num [OeisA67599.concatenateNats]

end D13Round25
