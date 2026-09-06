import Mathlib

/-!
# D16 R35: an infinite composite progression in the A067720 Pell branch

This auxiliary module concerns the already-derived strict subbranch
`p^2 + p + 1 = 3q^2`, equivalently `(2p+1)^2 - 12q^2 = -3`.
It proves that every Pell p-coordinate with index
`112 + 1094352 * t` is composite.  It does not assume or prove the open
A067720 conjecture.
-/

namespace D16R35Period4377409

/-- One affine step for the natural Pell coordinates `(p,q)`. -/
def step (z : ℕ × ℕ) : ℕ × ℕ :=
  (7 * z.1 + 12 * z.2 + 3, 4 * z.1 + 7 * z.2 + 2)

/-- Pell coordinates generated from `(p₀,q₀)=(1,1)`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => step (pell n)

/-- The modular period used by the certificate. -/
def period : ℕ := 1094352

/-- The p-coordinate at index 112. -/
def p112 : ℕ :=
  211202391265569285850874283472314877222155907821958696818291540639103925102727358425092697801413506153388378847466511209371807937

/-- The q-coordinate at index 112. -/
def q112 : ℕ :=
  121937757450669092534034104124291547331102297253961435522077251377945623160432409968545249569086637068032564498516415419471945313

/-- Exact cofactor for the divisor 4,377,409 of `p112`. -/
def p112Cofactor : ℕ :=
  48248265415813163871795914768831260049530648797486983011706591876405409022261195703918162045496207037859240214352031352193

abbrev R := ZMod 4377409

/-- A square root of 12 modulo 4,377,409. -/
def d : R := 463611

/-- The two split eigenvalues `7 ± 2d`. -/
def u : R := 927229
def v : R := 3450194

/-- `X_n = 2p_n+1`, reduced modulo 4,377,409. -/
def xZ (n : ℕ) : R := ((2 * (pell n).1 + 1 : ℕ) : R)

/-- The q-coordinate reduced modulo 4,377,409. -/
def qZ (n : ℕ) : R := ((pell n).2 : R)

lemma d_sq : d ^ 2 = (12 : R) := by
  norm_num [d]

lemma u_eq : u = 7 + 2 * d := by
  norm_num [u, d]

lemma v_eq : v = 7 - 2 * d := by
  norm_num [v, d]

lemma xZ_succ (n : ℕ) :
    xZ (n + 1) = 7 * xZ n + 24 * qZ n := by
  simp [xZ, qZ, pell, step]
  ring

lemma qZ_succ (n : ℕ) :
    qZ (n + 1) = 2 * xZ n + 7 * qZ n := by
  simp [xZ, qZ, pell, step]
  ring

lemma plus_formula (n : ℕ) :
    xZ n + d * qZ n = (3 + d) * u ^ n := by
  induction n with
  | zero => simp [xZ, qZ, pell]
  | succ n ih =>
      have h24 : (24 : R) = 2 * d ^ 2 := by rw [d_sq]; norm_num
      calc
        xZ (n + 1) + d * qZ (n + 1) =
            (7 * xZ n + 24 * qZ n) + d * (2 * xZ n + 7 * qZ n) := by
              rw [xZ_succ, qZ_succ]
        _ = (7 + 2 * d) * (xZ n + d * qZ n) := by
              rw [h24]
              ring
        _ = u * (xZ n + d * qZ n) := by rw [u_eq]
        _ = u * ((3 + d) * u ^ n) := by rw [ih]
        _ = (3 + d) * u ^ (n + 1) := by
              rw [pow_succ]
              ring

lemma minus_formula (n : ℕ) :
    xZ n - d * qZ n = (3 - d) * v ^ n := by
  induction n with
  | zero => simp [xZ, qZ, pell]
  | succ n ih =>
      have h24 : (24 : R) = 2 * d ^ 2 := by rw [d_sq]; norm_num
      calc
        xZ (n + 1) - d * qZ (n + 1) =
            (7 * xZ n + 24 * qZ n) - d * (2 * xZ n + 7 * qZ n) := by
              rw [xZ_succ, qZ_succ]
        _ = (7 - 2 * d) * (xZ n - d * qZ n) := by
              rw [h24]
              ring
        _ = v * (xZ n - d * qZ n) := by rw [v_eq]
        _ = v * ((3 - d) * v ^ n) := by rw [ih]
        _ = (3 - d) * v ^ (n + 1) := by
              rw [pow_succ]
              ring

lemma u_period : u ^ period = 1 := by
  change (927229 : ZMod 4377409) ^ 1094352 = 1
  reduce_mod_char

lemma v_period : v ^ period = 1 := by
  change (3450194 : ZMod 4377409) ^ 1094352 = 1
  reduce_mod_char

lemma plus_add_period (n : ℕ) :
    xZ (n + period) + d * qZ (n + period) = xZ n + d * qZ n := by
  rw [plus_formula, plus_formula, pow_add, u_period, mul_one]

lemma minus_add_period (n : ℕ) :
    xZ (n + period) - d * qZ (n + period) = xZ n - d * qZ n := by
  rw [minus_formula, minus_formula, pow_add, v_period, mul_one]

lemma cancel_two {a b : R} (h : 2 * a = 2 * b) : a = b := by
  have hi : (2188705 : R) * 2 = 1 := by norm_num
  calc
    a = ((2188705 : R) * 2) * a := by rw [hi]; simp
    _ = (2188705 : R) * (2 * a) := by ring
    _ = (2188705 : R) * (2 * b) := by rw [h]
    _ = ((2188705 : R) * 2) * b := by ring
    _ = b := by rw [hi]; simp

lemma xZ_add_period (n : ℕ) : xZ (n + period) = xZ n := by
  have hp := plus_add_period n
  have hm := minus_add_period n
  apply cancel_two
  linear_combination hp + hm

lemma pCast_add_period (n : ℕ) :
    (((pell (n + period)).1 : ℕ) : R) = (((pell n).1 : ℕ) : R) := by
  have hx := xZ_add_period n
  change (2 : R) * ((pell (n + period)).1 : R) + 1 =
      (2 : R) * ((pell n).1 : R) + 1 at hx
  apply cancel_two
  exact add_right_cancel hx

lemma pCast_add_mul_period (n t : ℕ) :
    (((pell (n + period * t)).1 : ℕ) : R) = (((pell n).1 : ℕ) : R) := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        (((pell (n + period * (t + 1))).1 : ℕ) : R) =
            (((pell ((n + period * t) + period)).1 : ℕ) : R) := by
              congr 3 <;> omega
        _ = (((pell (n + period * t)).1 : ℕ) : R) := pCast_add_period _
        _ = (((pell n).1 : ℕ) : R) := ih

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma pell_112 : pell 112 = (p112, q112) := by
  decide

lemma p112_factor : p112 = 4377409 * p112Cofactor := by
  norm_num [p112, p112Cofactor]

lemma p112_cast_zero : (p112 : R) = 0 := by
  rw [p112_factor]
  norm_num

lemma modulus_dvd_progression (t : ℕ) :
    4377409 ∣ (pell (112 + period * t)).1 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  calc
    (((pell (112 + period * t)).1 : ℕ) : R) =
        (((pell 112).1 : ℕ) : R) := pCast_add_mul_period 112 t
    _ = (p112 : R) := by rw [pell_112]
    _ = 0 := p112_cast_zero

lemma fst_lt_step (n : ℕ) : (pell n).1 < (pell (n + 1)).1 := by
  simp [pell, step]
  omega

lemma fst_le_add (n t : ℕ) : (pell n).1 ≤ (pell (n + t)).1 := by
  induction t with
  | zero => simp
  | succ t ih =>
      exact ih.trans (Nat.le_of_lt (by simpa [Nat.add_assoc] using fst_lt_step (n + t)))

lemma modulus_lt_progression (t : ℕ) :
    4377409 < (pell (112 + period * t)).1 := by
  have hbase : 4377409 < (pell 112).1 := by
    rw [pell_112]
    norm_num [p112]
  exact hbase.trans_le (fst_le_add 112 (period * t))

/-- Every index `112 + 1094352*t` has composite p-coordinate. -/
theorem not_prime_progression (t : ℕ) :
    ¬ Nat.Prime (pell (112 + period * t)).1 := by
  exact Nat.not_prime_of_dvd_of_ne
    (modulus_dvd_progression t)
    (by norm_num)
    (Nat.ne_of_lt (modulus_lt_progression t))

end D16R35Period4377409
