import Mathlib

namespace D23Round21

/-- Squared Gaussian norm, written on integer coordinates. -/
def normSq (x y : ℤ) : ℤ := x * x + y * y

/-- Determinant of two Gaussian-integer coordinate vectors. -/
def detZ (rx ry sx sy : ℤ) : ℤ := rx * sy - ry * sx

lemma normSq_nonneg (x y : ℤ) : 0 ≤ normSq x y := by
  simp only [normSq]
  positivity

lemma normSq_eq_zero_iff (x y : ℤ) : normSq x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx2 : x * x = 0 := by
      have hy2 : 0 ≤ y * y := by positivity
      have hx2n : 0 ≤ x * x := by positivity
      simp only [normSq] at h
      nlinarith
    have hy2 : y * y = 0 := by
      have hx2n : 0 ≤ x * x := by positivity
      have hy2n : 0 ≤ y * y := by positivity
      simp only [normSq] at h
      nlinarith
    rcases mul_eq_zero.mp hx2 with hx | hx <;>
      rcases mul_eq_zero.mp hy2 with hy | hy <;>
      exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [normSq]

/--
Full-rank scalar bound used in the quartic Gaussian branch of D23.

The hypotheses are exactly the arithmetic core after eliminating `P = 2β - qW` from

  |P|² + q (|T|² + 2|r|² + 2|s|²) = 4p²,
  |β|² = p².

No primality or congruence assumptions are needed: `0 < p ≤ q` and the nonzero determinant
of `r,s` suffice.  The conclusion is the fixed bound `0 < |W|² < 16`.
-/
theorem fullRank_scalar_norm_lt_sixteen
    (p q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : 0 < p)
    (hpq : p ≤ q)
    (hbeta : normSq A B = p * p)
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) :
    0 < normSq wx wy ∧ normSq wx wy < 16 := by
  have hrne : normSq rx ry ≠ 0 := by
    intro hr0
    obtain ⟨hrx, hry⟩ := (normSq_eq_zero_iff rx ry).mp hr0
    apply hdet
    simp [detZ, hrx, hry]
  have hsne : normSq sx sy ≠ 0 := by
    intro hs0
    obtain ⟨hsx, hsy⟩ := (normSq_eq_zero_iff sx sy).mp hs0
    apply hdet
    simp [detZ, hsx, hsy]
  have hrpos : 0 < normSq rx ry := by
    have := normSq_nonneg rx ry
    omega
  have hspos : 0 < normSq sx sy := by
    have := normSq_nonneg sx sy
    omega
  have ht_nonneg : 0 ≤ normSq tx ty := normSq_nonneg tx ty
  have hrespos :
      0 < normSq tx ty + 2 * normSq rx ry + 2 * normSq sx sy := by
    nlinarith
  have hwne : normSq wx wy ≠ 0 := by
    intro hw0
    obtain ⟨hwx, hwy⟩ := (normSq_eq_zero_iff wx wy).mp hw0
    subst wx
    subst wy
    simp [normSq] at henergy
    nlinarith
  have hw_nonneg : 0 ≤ normSq wx wy := normSq_nonneg wx wy
  have hwpos : 0 < normSq wx wy := by omega
  have hqpos : 0 < q := lt_of_lt_of_le hp hpq
  have hstrict :
      q * normSq wx wy < 4 * (A * wx + B * wy) := by
    nlinarith [henergy]
  have hqWpos : 0 < q * normSq wx wy := mul_pos hqpos hwpos
  have hinnerpos : 0 < A * wx + B * wy := by
    nlinarith
  have hcauchy :
      (A * wx + B * wy) * (A * wx + B * wy) ≤
        (p * p) * normSq wx wy := by
    have hcross : 0 ≤ (A * wy - B * wx) * (A * wy - B * wx) := by positivity
    simp only [normSq] at hbeta ⊢
    nlinarith
  let X : ℤ := q * normSq wx wy
  let Y : ℤ := 4 * (A * wx + B * wy)
  have hXY : X < Y := by simpa [X, Y] using hstrict
  have hXpos : 0 < X := by simpa [X] using hqWpos
  have hYpos : 0 < Y := by
    dsimp [Y]
    nlinarith
  have hfactorpos : 0 < (Y - X) * (Y + X) := by
    apply mul_pos
    · omega
    · omega
  have hsquare : X * X < Y * Y := by
    nlinarith
  have hsquare_bound :
      (q * normSq wx wy) * (q * normSq wx wy) <
        16 * (p * p) * normSq wx wy := by
    dsimp [X, Y] at hsquare
    nlinarith [hcauchy]
  have hp2pos : 0 < p * p := mul_pos hp hp
  have hq2ge : p * p ≤ q * q := by
    nlinarith
  have hlt16 : normSq wx wy < 16 := by
    by_contra hnot
    have hNge : 16 ≤ normSq wx wy := by omega
    have hscale_nonneg : 0 ≤ (p * p) * normSq wx wy := by positivity
    have hmulN := mul_le_mul_of_nonneg_right hNge hscale_nonneg
    have hN2nonneg : 0 ≤ normSq wx wy * normSq wx wy := by positivity
    have hmulQ := mul_le_mul_of_nonneg_right hq2ge hN2nonneg
    nlinarith [hsquare_bound, hmulN, hmulQ]
  exact ⟨hwpos, hlt16⟩

/-- Every nonzero Gaussian integer of squared norm below 16 has one of eight norms. -/
theorem smallGaussian_norm_cases (x y : ℤ)
    (hpos : 0 < normSq x y) (hlt : normSq x y < 16) :
    normSq x y = 1 ∨ normSq x y = 2 ∨ normSq x y = 4 ∨
    normSq x y = 5 ∨ normSq x y = 8 ∨ normSq x y = 9 ∨
    normSq x y = 10 ∨ normSq x y = 13 := by
  have hxlo : -3 ≤ x := by
    have hx2 : 0 ≤ y * y := by positivity
    simp only [normSq] at hlt
    nlinarith
  have hxhi : x ≤ 3 := by
    have hx2 : 0 ≤ y * y := by positivity
    simp only [normSq] at hlt
    nlinarith
  have hylo : -3 ≤ y := by
    have hy2 : 0 ≤ x * x := by positivity
    simp only [normSq] at hlt
    nlinarith
  have hyhi : y ≤ 3 := by
    have hy2 : 0 ≤ x * x := by positivity
    simp only [normSq] at hlt
    nlinarith
  interval_cases x <;> interval_cases y <;> norm_num [normSq] at hpos hlt ⊢

/-- The full-rank scalar identity therefore leaves only eight possible squared norms for `W`. -/
theorem fullRank_scalar_norm_cases
    (p q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : 0 < p)
    (hpq : p ≤ q)
    (hbeta : normSq A B = p * p)
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) :
    normSq wx wy = 1 ∨ normSq wx wy = 2 ∨ normSq wx wy = 4 ∨
    normSq wx wy = 5 ∨ normSq wx wy = 8 ∨ normSq wx wy = 9 ∨
    normSq wx wy = 10 ∨ normSq wx wy = 13 := by
  obtain ⟨hpos, hlt⟩ := fullRank_scalar_norm_lt_sixteen
    p q A B wx wy tx ty rx ry sx sy hp hpq hbeta hdet henergy
  exact smallGaussian_norm_cases wx wy hpos hlt

end D23Round21
