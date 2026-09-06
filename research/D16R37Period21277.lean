import FormalConjectures.Research.D16R34P112

/-!
# D16 R37: two infinite Pell-index progressions excluded by the divisor 21,277

This file concerns the already-derived square-Psi subbranch of the A067720
prime-cube case. It proves statements only about its Pell-coordinate recurrence
and does not assume the open A067720 conjecture.
-/

namespace D16R37Period21277

abbrev modulus : ℕ := 21277
abbrev period : ℕ := 10638
abbrev R := ZMod modulus

/-- Homogeneous step after replacing `p` by `X = 2p+1`. -/
def hstep (z : R × R) : R × R :=
  (7 * z.1 + 24 * z.2, 2 * z.1 + 7 * z.2)

/-- Homogeneous modular orbit starting from `(X₀,q₀)=(3,1)`. -/
def orbit : ℕ → R × R
  | 0 => (3, 1)
  | n + 1 => hstep (orbit n)

abbrev d : R := 4045
abbrev u : R := 8097
abbrev v : R := 13194

/-- The plus eigen-coordinate `X+dq`. -/
def plusCoord (z : R × R) : R := z.1 + d * z.2

/-- The minus eigen-coordinate `X-dq`. -/
def minusCoord (z : R × R) : R := z.1 - d * z.2

/-- The certified divisor is prime. -/
theorem modulus_prime : Nat.Prime modulus := by
  norm_num [modulus]

local instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- The homogeneous modular orbit is the image of the natural Pell recurrence. -/
theorem orbit_eq_pell (n : ℕ) :
    orbit n =
      (2 * ((D16R34P112.pell n).1 : R) + 1,
        ((D16R34P112.pell n).2 : R)) := by
  induction n with
  | zero => norm_num [orbit, D16R34P112.pell]
  | succ n ih =>
      simp only [orbit, D16R34P112.pell, hstep, D16R34P112.step, ih]
      apply Prod.ext <;> simp <;> ring

/-- `d` is a square root of 12 modulo `modulus`. -/
theorem d_sq : d * d = (12 : R) := by
  change (4045 : ZMod 21277) * 4045 = 12
  reduce_mod_char

/-- Two is nonzero in the prime residue field. -/
theorem two_ne_zero : (2 : R) ≠ 0 := by
  change (2 : ZMod 21277) ≠ 0
  decide

/-- The plus eigen-coordinate is multiplied by `u` in one step. -/
theorem plusCoord_hstep (z : R × R) :
    plusCoord (hstep z) = u * plusCoord z := by
  change (7 * z.1 + 24 * z.2) + d * (2 * z.1 + 7 * z.2) =
    u * (z.1 + d * z.2)
  have hu : u = 7 + 2 * d := by
    change (8097 : ZMod 21277) = 7 + 2 * 4045
    reduce_mod_char
  have h24 : (24 : R) = 2 * d * d := by
    calc
      (24 : R) = 2 * 12 := by norm_num
      _ = 2 * (d * d) := by rw [d_sq]
      _ = 2 * d * d := by ring
  rw [hu, h24]
  ring

/-- The minus eigen-coordinate is multiplied by `v` in one step. -/
theorem minusCoord_hstep (z : R × R) :
    minusCoord (hstep z) = v * minusCoord z := by
  change (7 * z.1 + 24 * z.2) - d * (2 * z.1 + 7 * z.2) =
    v * (z.1 - d * z.2)
  have hv : v = 7 - 2 * d := by
    change (13194 : ZMod 21277) = 7 - 2 * 4045
    reduce_mod_char
  have h24 : (24 : R) = 2 * d * d := by
    calc
      (24 : R) = 2 * 12 := by norm_num
      _ = 2 * (d * d) := by rw [d_sq]
      _ = 2 * d * d := by ring
  rw [hv, h24]
  ring

/-- Closed form for the plus eigen-coordinate. -/
theorem plusCoord_orbit (n : ℕ) :
    plusCoord (orbit n) = (3 + d) * u ^ n := by
  induction n with
  | zero => simp [orbit, plusCoord]
  | succ n ih =>
      rw [orbit, plusCoord_hstep, ih, pow_succ]
      ring

/-- Closed form for the minus eigen-coordinate. -/
theorem minusCoord_orbit (n : ℕ) :
    minusCoord (orbit n) = (3 - d) * v ^ n := by
  induction n with
  | zero => simp [orbit, minusCoord]
  | succ n ih =>
      rw [orbit, minusCoord_hstep, ih, pow_succ]
      ring

/-- Exact scalar period certificate for the plus eigenvalue. -/
theorem u_period : u ^ period = 1 := by
  change (8097 : ZMod 21277) ^ 10638 = 1
  reduce_mod_char

/-- Exact scalar period certificate for the minus eigenvalue. -/
theorem v_period : v ^ period = 1 := by
  change (13194 : ZMod 21277) ^ 10638 = 1
  reduce_mod_char

/-- The plus eigen-coordinate repeats after `period`. -/
theorem plusCoord_period (n : ℕ) :
    plusCoord (orbit (n + period)) = plusCoord (orbit n) := by
  rw [plusCoord_orbit, plusCoord_orbit, pow_add, u_period]
  ring

/-- The minus eigen-coordinate repeats after `period`. -/
theorem minusCoord_period (n : ℕ) :
    minusCoord (orbit (n + period)) = minusCoord (orbit n) := by
  rw [minusCoord_orbit, minusCoord_orbit, pow_add, v_period]
  ring

/-- The `X`-coordinate repeats after `period`. -/
theorem orbit_fst_period (n : ℕ) :
    (orbit (n + period)).1 = (orbit n).1 := by
  have hp := plusCoord_period n
  have hm := minusCoord_period n
  have h2 : (2 : R) * (orbit (n + period)).1 = 2 * (orbit n).1 := by
    dsimp [plusCoord, minusCoord] at hp hm
    linear_combination hp + hm
  apply mul_left_cancel₀ (a := (2 : R)) two_ne_zero
  exact h2

/-- Therefore the p-coordinate itself repeats modulo `modulus`. -/
theorem pell_fst_period (n : ℕ) :
    ((D16R34P112.pell (n + period)).1 : R) =
      ((D16R34P112.pell n).1 : R) := by
  have hx :
      2 * ((D16R34P112.pell (n + period)).1 : R) + 1 =
        2 * ((D16R34P112.pell n).1 : R) + 1 := by
    have hleft := congrArg Prod.fst (orbit_eq_pell (n + period))
    have hright := congrArg Prod.fst (orbit_eq_pell n)
    change (orbit (n + period)).1 =
      2 * ((D16R34P112.pell (n + period)).1 : R) + 1 at hleft
    change (orbit n).1 = 2 * ((D16R34P112.pell n).1 : R) + 1 at hright
    calc
      2 * ((D16R34P112.pell (n + period)).1 : R) + 1 =
          (orbit (n + period)).1 := hleft.symm
      _ = (orbit n).1 := orbit_fst_period n
      _ = 2 * ((D16R34P112.pell n).1 : R) + 1 := hright
  have h2 : (2 : R) * ((D16R34P112.pell (n + period)).1 : R) =
      2 * ((D16R34P112.pell n).1 : R) := by
    linear_combination hx
  apply mul_left_cancel₀ (a := (2 : R)) two_ne_zero
  exact h2

/-- Iterating the modular period any number of times. -/
theorem pell_fst_period_mul (n t : ℕ) :
    ((D16R34P112.pell (n + period * t)).1 : R) =
      ((D16R34P112.pell n).1 : R) := by
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [Nat.mul_succ, ← Nat.add_assoc]
      exact (pell_fst_period (n + period * t)).trans ih

/-- Plus eigen-coordinate at the first zero residue. -/
theorem plus_120 : plusCoord (orbit 120) = 3 := by
  rw [plusCoord_orbit]
  change ((3 : ZMod 21277) + 4045) * 8097 ^ 120 = 3
  have hpow : (8097 : ZMod 21277) ^ 120 = 4042 := by
    reduce_mod_char
  rw [hpow]
  reduce_mod_char

/-- Minus eigen-coordinate at the first zero residue. -/
theorem minus_120 : minusCoord (orbit 120) = -1 := by
  rw [minusCoord_orbit]
  change ((3 : ZMod 21277) - 4045) * 13194 ^ 120 = -1
  have hpow : (13194 : ZMod 21277) ^ 120 = 15534 := by
    reduce_mod_char
  rw [hpow]
  reduce_mod_char

/-- Plus eigen-coordinate at the second zero residue. -/
theorem plus_5198 : plusCoord (orbit 5198) = -1 := by
  rw [plusCoord_orbit]
  change ((3 : ZMod 21277) + 4045) * 8097 ^ 5198 = -1
  have hpow : (8097 : ZMod 21277) ^ 5198 = 5745 := by
    reduce_mod_char
  rw [hpow]
  reduce_mod_char

/-- Minus eigen-coordinate at the second zero residue. -/
theorem minus_5198 : minusCoord (orbit 5198) = 3 := by
  rw [minusCoord_orbit]
  change ((3 : ZMod 21277) - 4045) * 13194 ^ 5198 = 3
  have hpow : (13194 : ZMod 21277) ^ 5198 = 17229 := by
    reduce_mod_char
  rw [hpow]
  reduce_mod_char

/-- Adding the two eigen-coordinates recovers `2X`, so both base X-values are one. -/
theorem orbit_fst_eq_one_of_coords {n : ℕ}
    (hp : plusCoord (orbit n) + minusCoord (orbit n) = 2) :
    (orbit n).1 = 1 := by
  have h2 : (2 : R) * (orbit n).1 = 2 * (1 : R) := by
    dsimp [plusCoord, minusCoord] at hp
    linear_combination hp
  apply mul_left_cancel₀ (a := (2 : R)) two_ne_zero
  exact h2

/-- The first base p-coordinate is zero modulo the divisor. -/
theorem base120_zero : ((D16R34P112.pell 120).1 : R) = 0 := by
  have hX : (orbit 120).1 = 1 := by
    apply orbit_fst_eq_one_of_coords
    rw [plus_120, minus_120]
    norm_num
  have hEq := congrArg Prod.fst (orbit_eq_pell 120)
  change (orbit 120).1 = 2 * ((D16R34P112.pell 120).1 : R) + 1 at hEq
  have h2 : (2 : R) * ((D16R34P112.pell 120).1 : R) = 0 := by
    linear_combination hX - hEq
  apply mul_left_cancel₀ (a := (2 : R)) two_ne_zero
  calc
    (2 : R) * _ = 0 := h2
    _ = (2 : R) * 0 := by ring

/-- The second base p-coordinate is zero modulo the divisor. -/
theorem base5198_zero : ((D16R34P112.pell 5198).1 : R) = 0 := by
  have hX : (orbit 5198).1 = 1 := by
    apply orbit_fst_eq_one_of_coords
    rw [plus_5198, minus_5198]
    norm_num
  have hEq := congrArg Prod.fst (orbit_eq_pell 5198)
  change (orbit 5198).1 = 2 * ((D16R34P112.pell 5198).1 : R) + 1 at hEq
  have h2 : (2 : R) * ((D16R34P112.pell 5198).1 : R) = 0 := by
    linear_combination hX - hEq
  apply mul_left_cancel₀ (a := (2 : R)) two_ne_zero
  calc
    (2 : R) * _ = 0 := h2
    _ = (2 : R) * 0 := by ring

/-- Every index in the first progression is divisible by `modulus`. -/
theorem progression120_dvd (t : ℕ) :
    modulus ∣ (D16R34P112.pell (120 + period * t)).1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  calc
    ((D16R34P112.pell (120 + period * t)).1 : R) =
        ((D16R34P112.pell 120).1 : R) := pell_fst_period_mul 120 t
    _ = 0 := base120_zero

/-- Every index in the second progression is divisible by `modulus`. -/
theorem progression5198_dvd (t : ℕ) :
    modulus ∣ (D16R34P112.pell (5198 + period * t)).1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  calc
    ((D16R34P112.pell (5198 + period * t)).1 : R) =
        ((D16R34P112.pell 5198).1 : R) := pell_fst_period_mul 5198 t
    _ = 0 := base5198_zero

/-- Every Pell p-coordinate weakly increases at one step. -/
theorem pell_fst_le_succ (n : ℕ) :
    (D16R34P112.pell n).1 ≤ (D16R34P112.pell (n + 1)).1 := by
  simp [D16R34P112.pell, D16R34P112.step]
  omega

/-- The Pell p-coordinate is monotone. -/
theorem pell_fst_monotone : Monotone (fun n => (D16R34P112.pell n).1) :=
  monotone_nat_of_le_succ pell_fst_le_succ

/-- The divisor is strictly smaller than the p-coordinate at index 112. -/
theorem modulus_lt_p112 : modulus < D16R34P112.p112 := by
  norm_num [modulus, D16R34P112.p112]

/-- Every p-coordinate in the first infinite progression is composite. -/
theorem progression120_not_prime (t : ℕ) :
    ¬ Nat.Prime (D16R34P112.pell (120 + period * t)).1 := by
  apply Nat.not_prime_of_dvd_of_ne (progression120_dvd t)
  · norm_num [modulus]
  · apply Nat.ne_of_lt
    apply lt_of_lt_of_le modulus_lt_p112
    calc
      D16R34P112.p112 = (D16R34P112.pell 112).1 := by
        rw [D16R34P112.pell_112]
      _ ≤ (D16R34P112.pell (120 + period * t)).1 :=
        pell_fst_monotone (by omega)

/-- Every p-coordinate in the second infinite progression is composite. -/
theorem progression5198_not_prime (t : ℕ) :
    ¬ Nat.Prime (D16R34P112.pell (5198 + period * t)).1 := by
  apply Nat.not_prime_of_dvd_of_ne (progression5198_dvd t)
  · norm_num [modulus]
  · apply Nat.ne_of_lt
    apply lt_of_lt_of_le modulus_lt_p112
    calc
      D16R34P112.p112 = (D16R34P112.pell 112).1 := by
        rw [D16R34P112.pell_112]
      _ ≤ (D16R34P112.pell (5198 + period * t)).1 :=
        pell_fst_monotone (by omega)

/-- The two certified residue classes are both excluded. -/
theorem two_progressions_not_prime (t : ℕ) :
    ¬ Nat.Prime (D16R34P112.pell (120 + period * t)).1 ∧
      ¬ Nat.Prime (D16R34P112.pell (5198 + period * t)).1 := by
  exact ⟨progression120_not_prime t, progression5198_not_prime t⟩

end D16R37Period21277
