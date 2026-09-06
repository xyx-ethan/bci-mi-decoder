import Mathlib

/-!
# D16 R35: an infinite composite progression in the A067720 Pell subbranch

This auxiliary module concerns the exact recurrence

`p₀=q₀=1`,
`pₙ₊₁=7pₙ+12qₙ+3`,
`qₙ₊₁=4pₙ+7qₙ+2`.

It proves that every index `112 + 1094352*t` has composite `p`-coordinate.
It does not assume or prove the full A067720 conjecture.
-/

namespace D16R35P112Period

/-- One affine Pell-coordinate step over the natural numbers. -/
def step (z : ℕ × ℕ) : ℕ × ℕ :=
  (7 * z.1 + 12 * z.2 + 3, 4 * z.1 + 7 * z.2 + 2)

/-- Pell coordinates generated from `(p₀,q₀)=(1,1)`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => step (pell n)

/-- The natural `p`-coordinate. -/
def p (n : ℕ) : ℕ := (pell n).1

/-- The natural `q`-coordinate. -/
def q (n : ℕ) : ℕ := (pell n).2

/-- The modulus supplied by the exact factor of `p₁₁₂`. -/
abbrev modulus : ℕ := 4377409

abbrev R := ZMod modulus

/-- A square root of 12 modulo `modulus`. -/
def s : R := 463611

/-- The two eigenvalues of the homogeneous Pell step modulo `modulus`. -/
def alpha : R := 927229

def beta : R := 3450194

/-- Inverse of 4 modulo `modulus`. -/
def inv4 : R := 3283057

/-- Split coordinate corresponding to `2p+1+s q`. -/
def u (n : ℕ) : R := 2 * (p n : R) + 1 + s * (q n : R)

/-- Split coordinate corresponding to `2p+1-s q`. -/
def v (n : ℕ) : R := 2 * (p n : R) + 1 - s * (q n : R)

/-- The period used in the modular progression certificate. -/
abbrev period : ℕ := 1094352

theorem s_sq : s ^ 2 = (12 : R) := by
  change (463611 : ZMod 4377409) ^ 2 = 12
  reduce_mod_char

theorem alpha_formula : alpha = 7 + 2 * s := by
  change (927229 : ZMod 4377409) = 7 + 2 * 463611
  norm_num

theorem beta_formula : beta = 7 - 2 * s := by
  change (3450194 : ZMod 4377409) = 7 - 2 * 463611
  reduce_mod_char

theorem inv4_spec : inv4 * 4 = (1 : R) := by
  change (3283057 : ZMod 4377409) * 4 = 1
  reduce_mod_char

theorem alpha_period : alpha ^ period = (1 : R) := by
  change (927229 : ZMod 4377409) ^ 1094352 = 1
  reduce_mod_char

theorem beta_period : beta ^ period = (1 : R) := by
  change (3450194 : ZMod 4377409) ^ 1094352 = 1
  reduce_mod_char

theorem u_succ (n : ℕ) : u (n + 1) = alpha * u n := by
  simp only [u, p, q, pell, step, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [alpha_formula]
  have hs : s * s = (12 : R) := by simpa [pow_two] using s_sq
  linear_combination -(2 * ((pell n).2 : R)) * hs

theorem v_succ (n : ℕ) : v (n + 1) = beta * v n := by
  simp only [v, p, q, pell, step, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [beta_formula]
  have hs : s * s = (12 : R) := by simpa [pow_two] using s_sq
  linear_combination -(2 * ((pell n).2 : R)) * hs

theorem u_closed (n : ℕ) : u n = u 0 * alpha ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [u_succ, ih, pow_succ]
      ring

theorem v_closed (n : ℕ) : v n = v 0 * beta ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [v_succ, ih, pow_succ]
      ring

theorem p_formula (n : ℕ) :
    (p n : R) = inv4 * (u n + v n - 2) := by
  have hsum : u n + v n - 2 = 4 * (p n : R) := by
    simp only [u, v]
    ring
  rw [hsum, ← mul_assoc, inv4_spec, one_mul]

theorem u_progression (t : ℕ) : u (112 + period * t) = u 112 := by
  calc
    u (112 + period * t) = u 0 * alpha ^ (112 + period * t) := u_closed _
    _ = u 0 * alpha ^ 112 := by
      rw [pow_add, pow_mul, alpha_period, one_pow, mul_one]
    _ = u 112 := (u_closed 112).symm

theorem v_progression (t : ℕ) : v (112 + period * t) = v 112 := by
  calc
    v (112 + period * t) = v 0 * beta ^ (112 + period * t) := v_closed _
    _ = v 0 * beta ^ 112 := by
      rw [pow_add, pow_mul, beta_period, one_pow, mul_one]
    _ = v 112 := (v_closed 112).symm

theorem p_cast_progression (t : ℕ) :
    (p (112 + period * t) : R) = (p 112 : R) := by
  rw [p_formula, p_formula, u_progression, v_progression]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Direct kernel computation at the first index of the progression. -/
theorem p112_cast_zero : (p 112 : R) = 0 := by
  decide

/-- Every coordinate in the progression is divisible by the fixed modulus. -/
theorem modulus_dvd_progression (t : ℕ) :
    modulus ∣ p (112 + period * t) := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [p_cast_progression, p112_cast_zero]

/-- The `p`-coordinate strictly increases at every natural step. -/
theorem p_lt_succ (n : ℕ) : p n < p (n + 1) := by
  simp only [p, pell, step]
  omega

theorem p_monotone : Monotone p :=
  monotone_nat_of_le_succ fun n => (p_lt_succ n).le

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A small exact lower-bound anchor, avoiding expansion at huge indices. -/
theorem p8_value : p 8 = 2288805793 := by
  decide

/-- The divisor is proper at every index in the progression. -/
theorem modulus_lt_progression (t : ℕ) :
    modulus < p (112 + period * t) := by
  have hindex : 8 ≤ 112 + period * t := by omega
  have hmono := p_monotone hindex
  rw [p8_value] at hmono
  exact lt_of_lt_of_le (by norm_num : modulus < 2288805793) hmono

/-- Infinite exact exclusion: no `p`-coordinate in this progression is prime. -/
theorem not_prime_progression (t : ℕ) :
    ¬ Nat.Prime (p (112 + period * t)) := by
  apply Nat.not_prime_of_dvd_of_ne
  · exact modulus_dvd_progression t
  · norm_num
  · exact Nat.ne_of_lt (modulus_lt_progression t)

end D16R35P112Period
