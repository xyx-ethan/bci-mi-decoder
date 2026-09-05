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

import Mathlib
import FormalConjectures.OEIS.«67599»

/-!
# D13: structural reduction for the finite `f ≥ 2` two-prime box
-/

namespace D13Round19Structural

/-- Arithmetic decimal encoding `p,e,q,f`; here `f ≤ 9`, so its final block is one digit. -/
def encoded (p q e f : ℕ) : ℕ :=
  ((p * 10 ^ (Nat.digits 10 e).length + e) * 10 ^ (Nat.digits 10 q).length + q) * 10 + f

/-- Certified upper bounds for the second prime when `f=3,...,9`. -/
def qBound : ℕ → ℕ
  | 3 => 216
  | 4 => 39
  | 5 => 16
  | 6 => 9
  | 7 => 6
  | 8 => 5
  | 9 => 4
  | _ => 0

/-- If the last exponent is 2, parity forces the first prime to be 2. -/
theorem p_eq_two_of_f2_solution (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hfix : encoded p q e 2 = p ^ e * q ^ 2) : p = 2 := by
  rcases hp.eq_two_or_odd with hp2 | hpodd
  · exact hp2
  have hqne : q ≠ 2 := by omega
  have hqodd := hq.eq_two_or_odd.resolve_left hqne
  have hm := congrArg (fun n : ℕ ↦ n % 2) hfix
  simp [encoded, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hpodd, hqodd] at hm

/-- Remove the factor `p^(e-1) ≥ 1` using the positivity of a prime. -/
theorem qpow_upper (p q e f : ℕ) (hp : p.Prime) (he14 : e ≤ 14)
    (hineq : p ^ (e - 1) * q ^ (f - 1) ≤ 1120 * e * f) :
    q ^ (f - 1) ≤ 1120 * 14 * f := by
  have hp1 : 1 ≤ p ^ (e - 1) := Nat.one_le_pow _ _ hp.pos
  calc
    q ^ (f - 1) = 1 * q ^ (f - 1) := by simp
    _ ≤ p ^ (e - 1) * q ^ (f - 1) := Nat.mul_le_mul_right _ hp1
    _ ≤ 1120 * e * f := hineq
    _ ≤ 1120 * 14 * f := by gcongr

/-- If `q^r ≤ C < (B+1)^r`, then `q≤B`. -/
theorem base_le_of_pow_le (q r B C : ℕ)
    (h : q ^ r ≤ C) (hcut : C < (B + 1) ^ r) : q ≤ B := by
  by_contra hq
  have hb : B + 1 ≤ q := by omega
  have hp : (B + 1) ^ r ≤ q ^ r := pow_le_pow_left' hb r
  omega

theorem q_le_qBound (p q e f : ℕ) (hp : p.Prime)
    (he14 : e ≤ 14) (hf3 : 3 ≤ f) (hf9 : f ≤ 9)
    (hineq : p ^ (e - 1) * q ^ (f - 1) ≤ 1120 * e * f) :
    q ≤ qBound f := by
  have h := qpow_upper p q e f hp he14 hineq
  interval_cases f
  · exact base_le_of_pow_le q 2 216 47040 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 3 39 62720 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 4 16 78400 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 5 9 94080 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 6 6 109760 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 7 5 125440 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 8 4 141120 (by simpa using h) (by norm_num)

/--
Every putative exact encoded solution in the inherited finite `f≥2` box
satisfies the explicit structural split used by the 21,112-case certificate.
-/
theorem finite_fge2_structural_reduction (p q e f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (he14 : e ≤ 14) (hf2 : 2 ≤ f) (hf9 : f ≤ 9)
    (hineq : p ^ (e - 1) * q ^ (f - 1) ≤ 1120 * e * f)
    (hfix : encoded p q e f = p ^ e * q ^ f) :
    (f = 2 ∧ p = 2) ∨ (3 ≤ f ∧ q ≤ qBound f) := by
  by_cases hf : f = 2
  · exact Or.inl ⟨hf, p_eq_two_of_f2_solution p q e hp hq hpq (hf ▸ hfix)⟩
  · have hf3 : 3 ≤ f := by omega
    exact Or.inr ⟨hf3, q_le_qBound p q e f hp he14 hf3 hf9 hineq⟩

example : encoded 2 3 11 2 = 21132 := by norm_num [encoded]
example : qBound 3 = 216 := by decide
example : qBound 9 = 4 := by decide

#print axioms D13Round19Structural.finite_fge2_structural_reduction

end D13Round19Structural
