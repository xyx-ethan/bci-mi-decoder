import D17FiniteY

/-!
# D17 Round 24: bridge from the A063880 arithmetic equation to the ratio equation

The target branch is `n = 2^17 * x^4 * y^3 * z^3` with distinct odd prime
bases `x,y,z`.  This file first establishes the fixed prime-power closed
forms for ordinary and unitary divisor sums, then builds the multiplicative
bridge.
-/

namespace D17Round24

open scoped ArithmeticFunction.sigma
open OeisA63880

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Phi5N (t : ℕ) : ℕ := t^4 + t^3 + t^2 + t + 1

def Phi6N (t : ℕ) : ℕ := t^2 - t + 1

def BranchN (x y z : ℕ) : ℕ := 2^17 * x^4 * y^3 * z^3

theorem unitary_coprime_mul_iff {m n a b : ℕ}
    (hmn : m.Coprime n) (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (ha : a ∣ m) (hb : b ∣ n) :
    (a * b).Coprime ((m * n) / (a * b)) ↔
      a.Coprime (m / a) ∧ b.Coprime (n / b) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hmpos
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb hnpos
  have habpos : 0 < a * b := mul_pos hapos hbpos
  have hprod : m * n = (a * b) * ((m / a) * (n / b)) := by
    calc
      m * n = (a * (m / a)) * (b * (n / b)) := by
        rw [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb]
      _ = (a * b) * ((m / a) * (n / b)) := by ac_rfl
  have hcomp : (m * n) / (a * b) = (m / a) * (n / b) := by
    rw [hprod, Nat.mul_div_left _ habpos]
  rw [hcomp]
  constructor
  · intro h
    constructor
    · exact (h.coprime_dvd_left ((dvd_refl a).mul_right b)).coprime_dvd_right
        ((dvd_refl (m / a)).mul_right (n / b))
    · exact (h.coprime_dvd_left ((dvd_refl b).mul_left a)).coprime_dvd_right
        ((dvd_refl (n / b)).mul_left (m / a))
  · rintro ⟨haa, hbb⟩
    have han : a.Coprime n := hmn.coprime_dvd_left ha
    have hamb : a.Coprime (n / b) := han.coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have hbm : b.Coprime m := hmn.symm.coprime_dvd_left hb
    have hbma : b.Coprime (m / a) := hbm.coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    have hac : a.Coprime ((m / a) * (n / b)) := Nat.Coprime.mul_right haa hamb
    have hbc : b.Coprime ((m / a) * (n / b)) := Nat.Coprime.mul_right hbma hbb
    exact Nat.Coprime.mul_left hac hbc

theorem not_coprime_prime_pows {p i j : ℕ} (hp : p.Prime)
    (hi : i ≠ 0) (hj : j ≠ 0) : ¬ (p ^ i).Coprime (p ^ j) := by
  intro h
  have hpi : p ∣ p ^ i := dvd_pow_self p hi
  have hpj : p ∣ p ^ j := dvd_pow_self p hj
  have hpp : p.Coprime p := (h.coprime_dvd_left hpi).coprime_dvd_right hpj
  have hp1 : p = 1 := by simpa [Nat.Coprime] using hpp
  exact hp.ne_one hp1

theorem usigma_prime_pow_three {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 3) = 1 + p ^ 3 := by
  have h31 : p ^ 3 / p = p ^ 2 := by
    rw [show p ^ 3 = p * p ^ 2 by ring, Nat.mul_div_left _ hp.pos]
  have h32 : p ^ 3 / p ^ 2 = p := by
    rw [show p ^ 3 = p ^ 2 * p by ring, Nat.mul_div_left _ (pow_pos hp.pos 2)]
  have hc21 : ¬ (p ^ 2).Coprime p := not_coprime_prime_pows hp (by decide) (by decide)
  have hc12 : ¬ p.Coprime (p ^ 2) := not_coprime_prime_pows hp (by decide) (by decide)
  simp [usigma, unitaryDivisors, Nat.divisors_prime_pow hp, Finset.range_add_one,
    h31, h32, hc21, hc12, hp.ne_zero]

theorem usigma_prime_pow_four {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 4) = 1 + p ^ 4 := by
  have h41 : p ^ 4 / p = p ^ 3 := by
    rw [show p ^ 4 = p * p ^ 3 by ring, Nat.mul_div_left _ hp.pos]
  have h42 : p ^ 4 / p ^ 2 = p ^ 2 := by
    rw [show p ^ 4 = p ^ 2 * p ^ 2 by ring, Nat.mul_div_left _ (pow_pos hp.pos 2)]
  have h43 : p ^ 4 / p ^ 3 = p := by
    rw [show p ^ 4 = p ^ 3 * p by ring, Nat.mul_div_left _ (pow_pos hp.pos 3)]
  have hc31 : ¬ (p ^ 3).Coprime p := not_coprime_prime_pows hp (by decide) (by decide)
  have hc22 : ¬ (p ^ 2).Coprime (p ^ 2) := not_coprime_prime_pows hp (by decide) (by decide)
  have hc13 : ¬ p.Coprime (p ^ 3) := not_coprime_prime_pows hp (by decide) (by decide)
  simp [usigma, unitaryDivisors, Nat.divisors_prime_pow hp, Finset.range_add_one,
    h41, h42, h43, hc31, hc22, hc13, hp.ne_zero]

theorem usigma_two_pow_seventeen :
    usigma (2 ^ 17) = 1 + 2 ^ 17 := by
  rw [usigma, unitaryDivisors, Nat.divisors_prime_pow Nat.prime_two]
  norm_num [Finset.range_add_one, Nat.Coprime]

theorem sigma_prime_pow_three {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ 3) = (p + 1) * (p^2 + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

theorem sigma_prime_pow_four {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ 4) = Phi5N p := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, Phi5N]
  ring

theorem sigma_two_pow_seventeen :
    ArithmeticFunction.sigma 1 (2 ^ 17) = 262143 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  norm_num [Finset.sum_range_succ]

end D17Round24
