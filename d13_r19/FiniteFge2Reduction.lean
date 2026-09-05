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
# D13: complete structural reduction of the finite `f ≥ 2` box
-/

namespace D13Round19Reduction

structure Case where
  p : ℕ
  q : ℕ
  e : ℕ
  f : ℕ
deriving DecidableEq, Repr

def encoded (p q e f : ℕ) : ℕ :=
  ((p * 10 ^ (Nat.digits 10 e).length + e) * 10 ^ (Nat.digits 10 q).length + q) * 10 + f

def primesUpTo (N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter Nat.Prime

def es : List ℕ := (List.range 15).filter fun e ↦ 1 ≤ e

def fsHigh : List ℕ := (List.range 10).filter fun f ↦ 3 ≤ f

def qBound : ℕ → ℕ
  | 3 => 216
  | 4 => 39
  | 5 => 16
  | 6 => 9
  | 7 => 6
  | 8 => 5
  | 9 => 4
  | _ => 0

def casesTwo : List Case :=
  (primesUpTo 2240).flatMap fun q ↦ es.map fun e ↦ ⟨2, q, e, 2⟩

def casesHigh : List Case :=
  fsHigh.flatMap fun f ↦
    ((primesUpTo 216).filter fun q ↦ q ≤ qBound f).flatMap fun q ↦
      ((primesUpTo 216).filter fun p ↦ p < q).flatMap fun p ↦
        es.map fun e ↦ ⟨p, q, e, f⟩

def cases : List Case := casesTwo ++ casesHigh

theorem cases_length : cases.length = 21112 := by
  decide +kernel

theorem mem_primesUpTo {N p : ℕ} : p ∈ primesUpTo N ↔ p ≤ N ∧ p.Prime := by
  simp [primesUpTo]
  omega

theorem mem_es {e : ℕ} : e ∈ es ↔ 1 ≤ e ∧ e ≤ 14 := by
  simp [es]
  omega

theorem mem_fsHigh {f : ℕ} : f ∈ fsHigh ↔ 3 ≤ f ∧ f ≤ 9 := by
  simp [fsHigh]
  omega

theorem mem_casesTwo (q e : ℕ) (hq : q.Prime) (hqN : q ≤ 2240)
    (he1 : 1 ≤ e) (he14 : e ≤ 14) : ⟨2, q, e, 2⟩ ∈ casesTwo := by
  simp [casesTwo, mem_primesUpTo, mem_es, hq, hqN, he1, he14]

theorem mem_casesHigh (p q e f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hp216 : p ≤ 216) (hq216 : q ≤ 216) (hqB : q ≤ qBound f)
    (he1 : 1 ≤ e) (he14 : e ≤ 14) (hf3 : 3 ≤ f) (hf9 : f ≤ 9) :
    ⟨p, q, e, f⟩ ∈ casesHigh := by
  simp [casesHigh, mem_primesUpTo, mem_es, mem_fsHigh,
    hp, hq, hpq, hp216, hq216, hqB, he1, he14, hf3, hf9]

theorem p_eq_two_of_f2_solution (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hfix : encoded p q e 2 = p ^ e * q ^ 2) : p = 2 := by
  rcases hp.eq_two_or_odd with hp2 | hpodd
  · exact hp2
  have hqne : q ≠ 2 := by omega
  have hqodd := hq.eq_two_or_odd.resolve_left hqne
  have hm := congrArg (fun n : ℕ ↦ n % 2) hfix
  simp [encoded, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hpodd, hqodd] at hm

theorem qpow_upper (p q e f : ℕ) (hp : p.Prime) (he14 : e ≤ 14)
    (hineq : p ^ (e - 1) * q ^ (f - 1) ≤ 1120 * e * f) :
    q ^ (f - 1) ≤ 1120 * 14 * f := by
  have hp1 : 1 ≤ p ^ (e - 1) := Nat.one_le_pow _ _ hp.pos
  calc
    q ^ (f - 1) = 1 * q ^ (f - 1) := by simp
    _ ≤ p ^ (e - 1) * q ^ (f - 1) := Nat.mul_le_mul_right _ hp1
    _ ≤ 1120 * e * f := hineq
    _ ≤ 1120 * 14 * f := by gcongr

theorem base_le_of_pow_le (q r B C : ℕ)
    (h : q ^ r ≤ C) (hcut : C < (B + 1) ^ r) : q ≤ B := by
  by_contra hq
  have hb : B + 1 ≤ q := by omega
  have hp : (B + 1) ^ r ≤ q ^ r := pow_le_pow_left' hb r
  omega

theorem q_le_qBound (p q e f : ℕ) (hp : p.Prime)
    (he14 : e ≤ 14) (hf3 : 3 ≤ f) (hf9 : f ≤ 9)
    (hineq : p ^ (e - 1) * q ^ (f - 1) ≤ 1120 * e * f) : q ≤ qBound f := by
  have h := qpow_upper p q e f hp he14 hineq
  interval_cases f
  · exact base_le_of_pow_le q 2 216 47040 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 3 39 62720 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 4 16 78400 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 5 9 94080 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 6 6 109760 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 7 5 125440 (by simpa using h) (by norm_num)
  · exact base_le_of_pow_le q 8 4 141120 (by simpa using h) (by norm_num)

theorem qBound_le_216 (f : ℕ) (hf3 : 3 ≤ f) (hf9 : f ≤ 9) : qBound f ≤ 216 := by
  interval_cases f <;> norm_num [qBound]

theorem finite_fge2_reduces_to_cases (p q e f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (he1 : 1 ≤ e) (he14 : e ≤ 14)
    (hf2 : 2 ≤ f) (hf9 : f ≤ 9)
    (hq2240 : q ≤ 2240)
    (hineq : p ^ (e - 1) * q ^ (f - 1) ≤ 1120 * e * f)
    (hfix : encoded p q e f = p ^ e * q ^ f) :
    ⟨p, q, e, f⟩ ∈ cases := by
  by_cases hf : f = 2
  · subst f
    have hp2 := p_eq_two_of_f2_solution p q e hp hq hpq hfix
    subst p
    exact List.mem_append_left _ (mem_casesTwo q e hq hq2240 he1 he14)
  · have hf3 : 3 ≤ f := by omega
    have hqB := q_le_qBound p q e f hp he14 hf3 hf9 hineq
    have hq216 : q ≤ 216 := hqB.trans (qBound_le_216 f hf3 hf9)
    have hp216 : p ≤ 216 := by omega
    exact List.mem_append_right _
      (mem_casesHigh p q e f hp hq hpq hp216 hq216 hqB he1 he14 hf3 hf9)

example : encoded 2 3 11 2 = 21132 := by norm_num [encoded]
example : encoded 3 19 3 3 = 33193 := by norm_num [encoded]

#print axioms D13Round19Reduction.cases_length
#print axioms D13Round19Reduction.finite_fge2_reduces_to_cases

end D13Round19Reduction
