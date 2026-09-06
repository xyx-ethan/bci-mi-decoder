import Mathlib

/-!
# D16 R30: a periodic divisor for the prime-cube Pell branch

For the affine Pell-coordinate recurrence
`p' = 7p + 12q + 3`, `q' = 4p + 7q + 2`,
this file proves that every index `112 + 1094352*t` has p-coordinate
divisible by `4377409`, hence composite.
-/

namespace D16R30Period4377409

def modulus : ℕ := 4377409
def period : ℕ := 1094352

private theorem modulus_prime : Nat.Prime modulus := by
  norm_num [modulus]

local instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

abbrev R := ZMod modulus

def s : R := 463611
def u : R := 927229
def v : R := 3450194

def stepN (z : ℕ × ℕ) : ℕ × ℕ :=
  (7 * z.1 + 12 * z.2 + 3, 4 * z.1 + 7 * z.2 + 2)

def stepZ (z : R × R) : R × R :=
  (7 * z.1 + 24 * z.2, 2 * z.1 + 7 * z.2)

def initN : ℕ × ℕ := (1, 1)
def initZ : R × R := (3, 1)

def embed (z : ℕ × ℕ) : R × R :=
  (((2 * z.1 + 1 : ℕ) : R), (z.2 : R))

def plus (z : R × R) : R := z.1 + s * z.2
def minus (z : R × R) : R := z.1 - s * z.2

theorem s_sq : s ^ 2 = 12 := by
  change (463611 : ZMod 4377409) ^ 2 = 12
  decide

theorem u_formula : u = 7 + 2 * s := by
  change (927229 : ZMod 4377409) = 7 + 2 * 463611
  decide

theorem v_formula : v = 7 - 2 * s := by
  change (3450194 : ZMod 4377409) = 7 - 2 * 463611
  decide

theorem plus_step (z : R × R) : plus (stepZ z) = u * plus z := by
  rcases z with ⟨x, y⟩
  change 7 * x + 24 * y + s * (2 * x + 7 * y) = u * (x + s * y)
  rw [u_formula]
  have hs : s * s = 12 := by
    simpa [pow_two] using s_sq
  calc
    7 * x + 24 * y + s * (2 * x + 7 * y)
        = (7 + 2 * s) * (x + s * y) := by
            rw [show (24 : R) = 2 * (s * s) by rw [hs]; norm_num]
            ring
    _ = _ := rfl

theorem minus_step (z : R × R) : minus (stepZ z) = v * minus z := by
  rcases z with ⟨x, y⟩
  change 7 * x + 24 * y - s * (2 * x + 7 * y) = v * (x - s * y)
  rw [v_formula]
  have hs : s * s = 12 := by
    simpa [pow_two] using s_sq
  calc
    7 * x + 24 * y - s * (2 * x + 7 * y)
        = (7 - 2 * s) * (x - s * y) := by
            rw [show (24 : R) = 2 * (s * s) by rw [hs]; norm_num]
            ring
    _ = _ := rfl

theorem plus_iterate (n : ℕ) (z : R × R) :
    plus ((stepZ^[n]) z) = u ^ n * plus z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', plus_step, ih, pow_succ]
      ring

theorem minus_iterate (n : ℕ) (z : R × R) :
    minus ((stepZ^[n]) z) = v ^ n * minus z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', minus_step, ih, pow_succ]
      ring

theorem u_period : u ^ period = 1 := by
  let w : R := 1758704
  have hw4 : w ^ 4 = u := by
    change (1758704 : ZMod 4377409) ^ 4 = 927229
    decide
  have hw0 : w ≠ 0 := by
    change (1758704 : ZMod 4377409) ≠ 0
    decide
  calc
    u ^ period = (w ^ 4) ^ period := by rw [hw4]
    _ = w ^ (4 * period) := by rw [← pow_mul]
    _ = w ^ (modulus - 1) := by norm_num [period, modulus]
    _ = 1 := ZMod.pow_card_sub_one_eq_one hw0

theorem v_period : v ^ period = 1 := by
  let w : R := 819756
  have hw4 : w ^ 4 = v := by
    change (819756 : ZMod 4377409) ^ 4 = 3450194
    decide
  have hw0 : w ≠ 0 := by
    change (819756 : ZMod 4377409) ≠ 0
    decide
  calc
    v ^ period = (w ^ 4) ^ period := by rw [hw4]
    _ = w ^ (4 * period) := by rw [← pow_mul]
    _ = w ^ (modulus - 1) := by norm_num [period, modulus]
    _ = 1 := ZMod.pow_card_sub_one_eq_one hw0

theorem eq_of_plus_minus {z w : R × R}
    (hp : plus z = plus w) (hm : minus z = minus w) : z = w := by
  rcases z with ⟨x, y⟩
  rcases w with ⟨x', y'⟩
  change x + s * y = x' + s * y' at hp
  change x - s * y = x' - s * y' at hm
  apply Prod.ext
  · have h : (2 : R) * x = 2 * x' := by
      linear_combination hp + hm
    have htwo : (2 : R) ≠ 0 := by
      change (2 : ZMod 4377409) ≠ 0
      decide
    exact mul_left_cancel₀ htwo h
  · have h : (2 * s : R) * y = (2 * s) * y' := by
      linear_combination hp - hm
    have hs : (2 * s : R) ≠ 0 := by
      change (2 * (463611 : ZMod 4377409)) ≠ 0
      decide
    exact mul_left_cancel₀ hs h

theorem stepZ_period : stepZ^[period] = id := by
  funext z
  apply eq_of_plus_minus
  · rw [plus_iterate, u_period]
    simp
  · rw [minus_iterate, v_period]
    simp

theorem embed_step (z : ℕ × ℕ) : embed (stepN z) = stepZ (embed z) := by
  rcases z with ⟨p, q⟩
  ext <;> simp [embed, stepN, stepZ] <;> ring

theorem embed_iterate (n : ℕ) (z : ℕ × ℕ) :
    embed ((stepN^[n]) z) = (stepZ^[n]) (embed z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        embed_step, ih]

theorem init_embed : embed initN = initZ := by
  norm_num [embed, initN, initZ]

theorem stepZ_progression (t : ℕ) :
    (stepZ^[112 + period * t]) initZ = (stepZ^[112]) initZ := by
  have hper : stepZ^[period * t] = id := by
    rw [Function.iterate_mul, stepZ_period]
    simp
  rw [Function.iterate_add_apply, hper]
  rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem zero_at_112 : (((stepZ^[112]) initZ).1 = 1) := by
  decide

theorem modular_zero_progression (t : ℕ) :
    (((stepZ^[112 + period * t]) initZ).1 = 1) := by
  rw [stepZ_progression]
  exact zero_at_112

def pell (n : ℕ) : ℕ × ℕ := (stepN^[n]) initN

theorem cast_pell (n : ℕ) : embed (pell n) = (stepZ^[n]) initZ := by
  rw [pell, embed_iterate, init_embed]

theorem dvd_progression (t : ℕ) :
    modulus ∣ (pell (112 + period * t)).1 := by
  let P := (pell (112 + period * t)).1
  have hx : (((2 * P + 1 : ℕ) : R) = 1) := by
    have h := congr_arg Prod.fst (cast_pell (112 + period * t))
    simpa [embed, P] using h.trans (modular_zero_progression t)
  have hx' : (2 : R) * (P : R) + 1 = 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hx
  have hp2 : (2 : R) * (P : R) = 0 := by
    linear_combination hx'
  have htwo : (2 : R) ≠ 0 := by
    change (2 : ZMod 4377409) ≠ 0
    decide
  have hp : ((P : ℕ) : R) = 0 :=
    (mul_eq_zero.mp hp2).resolve_left htwo
  exact (ZMod.natCast_eq_zero_iff _ _).mp hp

theorem fst_lt_stepN (z : ℕ × ℕ) : z.1 < (stepN z).1 := by
  simp [stepN]
  omega

theorem fst_le_iterate (z : ℕ × ℕ) (n : ℕ) :
    z.1 ≤ ((stepN^[n]) z).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (fst_lt_stepN _).le

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem p112_eval :
    (pell 112).1 =
      211202391265569285850874283472314877222155907821958696818291540639103925102727358425092697801413506153388378847466511209371807937 := by
  decide

theorem modulus_lt_p112 : modulus < (pell 112).1 := by
  rw [p112_eval]
  norm_num [modulus]

theorem p112_le_progression (t : ℕ) :
    (pell 112).1 ≤ (pell (112 + period * t)).1 := by
  change ((stepN^[112]) initN).1 ≤ ((stepN^[112 + period * t]) initN).1
  rw [Nat.add_comm 112 (period * t), Function.iterate_add_apply]
  exact fst_le_iterate _ _

theorem not_prime_progression (t : ℕ) :
    ¬ Nat.Prime (pell (112 + period * t)).1 := by
  apply Nat.not_prime_of_dvd_of_ne (dvd_progression t)
  · norm_num [modulus]
  · exact Nat.ne_of_lt (modulus_lt_p112.trans_le (p112_le_progression t))

end D16R30Period4377409
