/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.OEIS.«67599»

/-!
# A prime-power obstruction for OEIS A067599

This file proves that no positive prime power is a fixed point of the decimal
prime-factorization encoding used by `OeisA67599.a`.
-/

namespace OeisA67599

/-- The A067599 encoding of a positive prime power is the decimal concatenation of
its prime base and exponent. -/
@[category API, AMS 11]
lemma a_prime_pow (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) = p * 10 ^ (Nat.digits 10 e).length + e := by
  rw [a]
  rw [if_neg]
  · rw [hp.primeFactorsList_pow]
    rw [List.replicate_dedup he.ne']
    simp [concatenateNats]
  · have hpow : 1 < p ^ e := one_lt_pow₀ hp.one_lt he.ne'
    omega

/-- A convenient elementary growth estimate used in the prime-power exclusion. -/
@[category API, AMS 11]
lemma eleven_mul_lt_two_pow_sub_one (e : ℕ) (he : 8 ≤ e) :
    11 * e < 2 ^ (e - 1) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
      have he1 : 1 ≤ e := by omega
      have hpow : 2 ^ e = 2 * 2 ^ (e - 1) := by
        conv_lhs => rw [show e = (e - 1) + 1 by omega]
        rw [pow_succ]
        omega
      simp only [Nat.add_sub_cancel]
      rw [hpow]
      nlinarith

/-- The bounded exceptional range needed after divisibility reduces the exponent. -/
@[category test, AMS 11]
lemma no_small_prime_power_fixed_point :
    ∀ p e : Fin 8,
      2 ≤ (p : ℕ) →
      1 ≤ (e : ℕ) →
      (p : ℕ).Prime →
      (p : ℕ) ∣ (e : ℕ) →
      (p : ℕ) * 10 ^ (Nat.digits 10 (e : ℕ)).length + (e : ℕ) ≠
        (p : ℕ) ^ (e : ℕ) := by
  native_decide

/-- No positive power of a prime is a fixed point of the A067599 encoding. -/
@[category research solved, AMS 11]
theorem no_prime_power_fixed_point (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) ≠ p ^ e := by
  rw [a_prime_pow p e hp he]
  intro hfix
  have hpdiv : p ∣ e := by
    have hmod : e % p = 0 := by
      have h := congrArg (fun n : ℕ ↦ n % p) hfix
      have hpmod : p ^ e % p = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_pow_self p he.ne')
      simpa [Nat.add_mod, Nat.mul_mod, hp.ne_zero, hpmod] using h
    exact Nat.dvd_of_mod_eq_zero hmod
  by_cases hsmall : e < 8
  · have hp8 : p < 8 := by
      have hple : p ≤ e := Nat.le_of_dvd he hpdiv
      omega
    have hne := no_small_prime_power_fixed_point
      (⟨p, hp8⟩ : Fin 8) (⟨e, hsmall⟩ : Fin 8)
      hp.two_le he hp hpdiv
    exact hne hfix
  · have he8 : 8 ≤ e := by omega
    have hdigits :
        10 ^ (Nat.digits 10 e).length ≤ 10 * e :=
      Nat.base_pow_length_digits_le 10 e (by norm_num) he.ne'
    have he_le_pe : e ≤ p * e := by
      simpa using Nat.mul_le_mul_right e hp.one_le
    have henc_le :
        p * 10 ^ (Nat.digits 10 e).length + e ≤ 11 * p * e := by
      calc
        p * 10 ^ (Nat.digits 10 e).length + e
            ≤ p * (10 * e) + e :=
              Nat.add_le_add_right (Nat.mul_le_mul_left p hdigits) e
        _ ≤ 11 * p * e := by nlinarith
    have hgrowth := eleven_mul_lt_two_pow_sub_one e he8
    have henc_lt_two :
        p * 10 ^ (Nat.digits 10 e).length + e < p * 2 ^ (e - 1) := by
      apply lt_of_le_of_lt henc_le
      have hmul := Nat.mul_lt_mul_of_pos_left hgrowth hp.pos
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hbase : 2 ^ (e - 1) ≤ p ^ (e - 1) :=
      pow_le_pow_left' hp.two_le (e - 1)
    have hpowers : p * 2 ^ (e - 1) ≤ p ^ e := by
      calc
        p * 2 ^ (e - 1) ≤ p * p ^ (e - 1) := Nat.mul_le_mul_left p hbase
        _ = p ^ e := by
          conv_rhs => rw [show e = (e - 1) + 1 by omega, pow_succ]
          simp [mul_comm]
    have hlt : p * 10 ^ (Nat.digits 10 e).length + e < p ^ e :=
      lt_of_lt_of_le henc_lt_two hpowers
    omega

end OeisA67599
