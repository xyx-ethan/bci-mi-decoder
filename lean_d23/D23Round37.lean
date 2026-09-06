import D23Round21

namespace D23Round37

open D23Round21

/--
If the Gaussian scalar `W = (wx, wy)` in the full-rank scalar identity is twice
an integer Gaussian scalar `w = (ux, uy)`, then the Round-21 norm bound leaves
exactly the eight possibilities `w ∈ {±1, ±i, ±1±i}`.

This is a bridge theorem for the strict subbranch in which the total quartic
coefficient sum is divisible by four: if `S = 2W = 4w`, then `W = 2w`.
-/
theorem fullRank_twiceGaussian_eight_points
    (p q A B wx wy ux uy tx ty rx ry sx sy : ℤ)
    (hp : 0 < p)
    (hpq : p ≤ q)
    (hbeta : normSq A B = p * p)
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy))
    (hwx : wx = 2 * ux)
    (hwy : wy = 2 * uy) :
    (ux = 1 ∧ uy = 0) ∨
    (ux = -1 ∧ uy = 0) ∨
    (ux = 0 ∧ uy = 1) ∨
    (ux = 0 ∧ uy = -1) ∨
    (ux = 1 ∧ uy = 1) ∨
    (ux = 1 ∧ uy = -1) ∨
    (ux = -1 ∧ uy = 1) ∨
    (ux = -1 ∧ uy = -1) := by
  obtain ⟨hWpos, hWlt⟩ := fullRank_scalar_norm_lt_sixteen
    p q A B wx wy tx ty rx ry sx sy hp hpq hbeta hdet henergy
  subst wx
  subst wy
  have hscale : normSq (2 * ux) (2 * uy) = 4 * normSq ux uy := by
    simp [normSq]
    ring
  rw [hscale] at hWpos hWlt
  have hwpos : 0 < normSq ux uy := by omega
  have hwlt : normSq ux uy < 4 := by omega
  have hxlo : -1 ≤ ux := by
    have hy2 : 0 ≤ uy * uy := by nlinarith [sq_nonneg uy]
    simp only [normSq] at hwlt
    by_contra h
    have hxle : ux ≤ -2 := by omega
    nlinarith
  have hxhi : ux ≤ 1 := by
    have hy2 : 0 ≤ uy * uy := by nlinarith [sq_nonneg uy]
    simp only [normSq] at hwlt
    by_contra h
    have hxge : 2 ≤ ux := by omega
    nlinarith
  have hylo : -1 ≤ uy := by
    have hx2 : 0 ≤ ux * ux := by nlinarith [sq_nonneg ux]
    simp only [normSq] at hwlt
    by_contra h
    have hyle : uy ≤ -2 := by omega
    nlinarith
  have hyhi : uy ≤ 1 := by
    have hx2 : 0 ≤ ux * ux := by nlinarith [sq_nonneg ux]
    simp only [normSq] at hwlt
    by_contra h
    have hyge : 2 ≤ uy := by omega
    nlinarith
  interval_cases ux <;> interval_cases uy
  all_goals norm_num [normSq] at *

/-- The corresponding quotient Gaussian scalar has squared norm one or two. -/
theorem fullRank_twiceGaussian_norm_one_or_two
    (p q A B wx wy ux uy tx ty rx ry sx sy : ℤ)
    (hp : 0 < p)
    (hpq : p ≤ q)
    (hbeta : normSq A B = p * p)
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy))
    (hwx : wx = 2 * ux)
    (hwy : wy = 2 * uy) :
    normSq ux uy = 1 ∨ normSq ux uy = 2 := by
  rcases fullRank_twiceGaussian_eight_points
      p q A B wx wy ux uy tx ty rx ry sx sy hp hpq hbeta hdet henergy hwx hwy with
    h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩ <;> norm_num [normSq]

end D23Round37
