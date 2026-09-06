import Mathlib

/-!
# D16 R29: a periodic divisibility obstruction in the A067720 Pell branch
-/

namespace D16R29Period263

abbrev R := ZMod 263

def stepN (z : ℕ × ℕ) : ℕ × ℕ :=
  (7 * z.1 + 12 * z.2 + 3, 4 * z.1 + 7 * z.2 + 2)

def stepZ (z : R × R) : R × R :=
  (7 * z.1 + 12 * z.2 + 3, 4 * z.1 + 7 * z.2 + 2)

def initN : ℕ × ℕ := (1, 1)

def initZ : R × R := (1, 1)

def castPair (z : ℕ × ℕ) : R × R := ((z.1 : R), (z.2 : R))

def pN (n : ℕ) : ℕ := ((stepN^[n]) initN).1

lemma cast_step (z : ℕ × ℕ) : castPair (stepN z) = stepZ (castPair z) := by
  ext <;> simp [castPair, stepN, stepZ]

lemma cast_iterate (n : ℕ) :
    castPair ((stepN^[n]) initN) = (stepZ^[n]) initZ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [cast_step, ih]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma period_131 : (stepZ^[131]) initZ = initZ := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma zero_104 : ((stepZ^[104]) initZ).1 = 0 := by
  decide

lemma period_mul (t : ℕ) : (stepZ^[131 * t]) initZ = initZ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, period_131, ih]

lemma zero_progression (t : ℕ) :
    ((stepZ^[104 + 131 * t]) initZ).1 = 0 := by
  rw [Function.iterate_add_apply, period_mul, zero_104]

lemma dvd_progression (t : ℕ) : 263 ∣ pN (104 + 131 * t) := by
  rw [← ZMod.natCast_eq_zero_iff]
  change (castPair ((stepN^[104 + 131 * t]) initN)).1 = 0
  rw [cast_iterate]
  exact zero_progression t

lemma pN_succ_lt (n : ℕ) : pN n < pN (n + 1) := by
  rw [show n + 1 = n.succ by omega]
  simp only [pN, Function.iterate_succ_apply']
  simp [stepN]
  omega

lemma pN_monotone : Monotone pN :=
  monotone_nat_of_le_succ fun n => (pN_succ_lt n).le

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma pN_two : pN 2 = 313 := by
  decide

lemma proper_divisor_progression (t : ℕ) : 263 < pN (104 + 131 * t) := by
  have hmono : pN 2 ≤ pN (104 + 131 * t) := pN_monotone (by omega)
  rw [pN_two] at hmono
  omega

theorem not_prime_progression (t : ℕ) :
    ¬ Nat.Prime (pN (104 + 131 * t)) := by
  exact Nat.not_prime_of_dvd_of_ne (dvd_progression t) (by norm_num)
    (Nat.ne_of_lt (proper_divisor_progression t))

end D16R29Period263
