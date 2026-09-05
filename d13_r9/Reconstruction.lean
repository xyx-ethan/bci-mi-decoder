import D13R9Numbers
import FormalConjectures.OEIS.«67599»

namespace D13.R9

/-- Recover the ordered prime factor list, not just a product identity. -/
theorem factors_from_sorted (n : ℕ) (l : List ℕ)
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, Nat.Prime p)
    (hsort : l.Pairwise (· ≤ ·)) : n.primeFactorsList = l := by
  exact ((Nat.primeFactorsList_unique hprod hprime).eq_of_pairwise'
    hsort (Nat.primeFactorsList_sorted n).pairwise).symm

theorem factors7 (q : ℕ) (hq : q.Prime) (h7 : 7 < q) :
    ((7 : ℕ)^4 * q).primeFactorsList = [7,7,7,7,q] := by
  apply factors_from_sorted
  · norm_num <;> ring
  · have hp : Nat.Prime 7 := by norm_num
    simp_all
  · simp [List.pairwise_cons, le_of_lt h7]

theorem factors3 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    ((3 : ℕ)^7 * q).primeFactorsList = [3,3,3,3,3,3,3,q] := by
  apply factors_from_sorted
  · norm_num <;> ring
  · have hp : Nat.Prime 3 := by norm_num
    simp_all
  · simp [List.pairwise_cons, le_of_lt h3]

theorem encoding7 (q : ℕ) (hq : q.Prime) (h7 : 7 < q) :
    OeisA67599.a ((7 : ℕ)^4 * q) =
      740 * 10 ^ (Nat.digits 10 q).length + 10*q + 1 := by
  have hn : ¬ (7 : ℕ)^4*q < 2 := by norm_num; omega
  have hne : q ≠ 7 := ne_of_gt h7
  have hne' : 7 ≠ q := ne_of_lt h7
  unfold OeisA67599.a
  rw [if_neg hn, factors7 q hq h7]
  norm_num [OeisA67599.concatenateNats, List.dedup, hne, hne'] <;> ring

theorem encoding3 (q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    OeisA67599.a ((3 : ℕ)^7 * q) =
      370 * 10 ^ (Nat.digits 10 q).length + 10*q + 1 := by
  have hn : ¬ (3 : ℕ)^7*q < 2 := by norm_num; omega
  have hne : q ≠ 3 := ne_of_gt h3
  have hne' : 3 ≠ q := ne_of_lt h3
  unfold OeisA67599.a
  rw [if_neg hn, factors3 q hq h3]
  norm_num [OeisA67599.concatenateNats, List.dedup, hne, hne'] <;> ring

/-- A quotient equation determines the exact decimal digit length. -/
theorem digits_of_equation (c d k q : ℕ)
    (hk : 1 ≤ k) (hc : 0 < c) (hcd : c < d) (hdc : d < 10*c)
    (heq : d*q = c*10^k+1) : (Nat.digits 10 q).length = k := by
  have hd : 0 < d := lt_trans hc hcd
  have hx : 0 < (10 : ℕ)^(k-1) := by positivity
  have hp : (10 : ℕ)^k = 10*10^(k-1) := by
    conv_lhs => rw [show k = (k-1)+1 by omega, pow_succ]
    ring
  have hlow : (10 : ℕ)^(k-1) ≤ q := by
    by_contra h
    have hmul := Nat.mul_lt_mul_of_pos_left (lt_of_not_ge h) hd
    have hmul' := Nat.mul_le_mul_right ((10 : ℕ)^(k-1)) (le_of_lt hdc)
    rw [hp] at heq
    nlinarith
  have hpow : 1 < (10 : ℕ)^k := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < (10 : ℕ)) hk
    norm_num at hh
    omega
  have hupp : q < (10 : ℕ)^k := by
    by_contra h
    have hmul := Nat.mul_le_mul_left d (le_of_not_gt h)
    have hmul' := Nat.mul_le_mul_right ((10 : ℕ)^k) (Nat.succ_le_of_lt hcd)
    nlinarith
  have hlenlo := (Nat.lt_digits_length_iff (by decide : 1 < (10 : ℕ)) q).2 hlow
  have hlenhi := (Nat.digits_length_le_iff (by decide : 1 < (10 : ℕ)) q).2 hupp
  omega

theorem q1_digits (t : ℕ) :
    (Nat.digits 10 (D13.q1 t)).length = 136+199*t := by
  exact digits_of_equation 740 2391 (136+199*t) (D13.q1 t)
    (by omega) (by decide) (by decide) (by decide) (D13.r9_q1_exact t)

theorem q2_digits (t : ℕ) :
    (Nat.digits 10 (D13.q2 t)).length = 666+930*t := by
  exact digits_of_equation 370 2177 (666+930*t) (D13.q2 t)
    (by omega) (by decide) (by decide) (by decide) (D13.r9_q2_exact t)

/-- This uses the actual upstream a, including exponent 1. -/
theorem q1_prime_gives_fixed_point (t : ℕ) (hp : (D13.q1 t).Prime) :
    OeisA67599.a ((7 : ℕ)^4 * D13.q1 t) = (7 : ℕ)^4 * D13.q1 t := by
  have h7 : 7 < D13.q1 t := lt_trans (by decide) (D13.q1_large t)
  rw [encoding7 (D13.q1 t) hp h7, q1_digits]
  have h := D13.r9_q1_exact t
  norm_num only [show (7 : ℕ)^4 = 2401 by decide]
  omega

theorem q2_prime_gives_fixed_point (t : ℕ) (hp : (D13.q2 t).Prime) :
    OeisA67599.a ((3 : ℕ)^7 * D13.q2 t) = (3 : ℕ)^7 * D13.q2 t := by
  have h3 : 3 < D13.q2 t := lt_trans (by decide) (D13.q2_large t)
  rw [encoding3 (D13.q2 t) hp h3, q2_digits]
  have h := D13.r9_q2_exact t
  norm_num only [show (3 : ℕ)^7 = 2187 by decide]
  omega

theorem q1_prime_implies_upstream_exists :
    (∃ t, (D13.q1 t).Prime) → ∃ n : ℕ, 2 ≤ n ∧ OeisA67599.a n = n := by
  rintro ⟨t, ht⟩
  refine ⟨(7 : ℕ)^4*D13.q1 t, ?_, q1_prime_gives_fixed_point t ht⟩
  have h := D13.q1_large t
  norm_num
  omega

theorem q2_prime_implies_upstream_exists :
    (∃ t, (D13.q2 t).Prime) → ∃ n : ℕ, 2 ≤ n ∧ OeisA67599.a n = n := by
  rintro ⟨t, ht⟩
  refine ⟨(3 : ℕ)^7*D13.q2 t, ?_, q2_prime_gives_fixed_point t ht⟩
  have h := D13.q2_large t
  norm_num
  omega

end D13.R9
