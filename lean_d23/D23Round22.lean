import D23Round21

namespace D23Round22

open D23Round21

/--
Axis-β refinement of the full-rank scalar branch.

If the Gaussian parameter β = A + iB lies on a coordinate axis, then the
full-rank scalar identity from round 21 excludes the squared norms 8 and 13.
Thus only six squared norms remain for W.
-/
theorem axisBeta_scalar_norm_cases
    (p q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : 0 < p)
    (hpq : p ≤ q)
    (hbeta : normSq A B = p * p)
    (hdet : detZ rx ry sx sy ≠ 0)
    (haxis : A = 0 ∨ B = 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) :
    normSq wx wy = 1 ∨ normSq wx wy = 2 ∨ normSq wx wy = 4 ∨
    normSq wx wy = 5 ∨ normSq wx wy = 9 ∨ normSq wx wy = 10 := by
  obtain ⟨hpos, hlt⟩ := fullRank_scalar_norm_lt_sixteen
    p q A B wx wy tx ty rx ry sx sy hp hpq hbeta hdet henergy
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
    have h := normSq_nonneg rx ry
    omega
  have hspos : 0 < normSq sx sy := by
    have h := normSq_nonneg sx sy
    omega
  have ht_nonneg : 0 ≤ normSq tx ty := normSq_nonneg tx ty
  have hrespos :
      0 < normSq tx ty + 2 * normSq rx ry + 2 * normSq sx sy := by
    nlinarith
  have hxlo : -3 ≤ wx := by
    have hy2 : 0 ≤ wy * wy := by nlinarith [sq_nonneg wy]
    simp only [normSq] at hlt
    by_contra h
    have hxle : wx ≤ -4 := by omega
    nlinarith
  have hxhi : wx ≤ 3 := by
    have hy2 : 0 ≤ wy * wy := by nlinarith [sq_nonneg wy]
    simp only [normSq] at hlt
    by_contra h
    have hxge : 4 ≤ wx := by omega
    nlinarith
  have hylo : -3 ≤ wy := by
    have hx2 : 0 ≤ wx * wx := by nlinarith [sq_nonneg wx]
    simp only [normSq] at hlt
    by_contra h
    have hyle : wy ≤ -4 := by omega
    nlinarith
  have hyhi : wy ≤ 3 := by
    have hx2 : 0 ≤ wx * wx := by nlinarith [sq_nonneg wx]
    simp only [normSq] at hlt
    by_contra h
    have hyge : 4 ≤ wy := by omega
    nlinarith
  rcases haxis with hA | hB
  · subst A
    simp only [normSq, zero_mul, zero_add] at hbeta henergy
    have hBsign : B = p ∨ B = -p := (mul_self_eq_mul_self_iff).mp hbeta
    rcases hBsign with hBp | hBn
    · subst B
      interval_cases wx <;> interval_cases wy
      all_goals norm_num [normSq] at hpos hlt ⊢
      all_goals nlinarith [hrespos]
    · subst B
      interval_cases wx <;> interval_cases wy
      all_goals norm_num [normSq] at hpos hlt ⊢
      all_goals nlinarith [hrespos]
  · subst B
    simp only [normSq, mul_zero, add_zero] at hbeta henergy
    have hAsign : A = p ∨ A = -p := (mul_self_eq_mul_self_iff).mp hbeta
    rcases hAsign with hAp | hAn
    · subst A
      interval_cases wx <;> interval_cases wy
      all_goals norm_num [normSq] at hpos hlt ⊢
      all_goals nlinarith [hrespos]
    · subst A
      interval_cases wx <;> interval_cases wy
      all_goals norm_num [normSq] at hpos hlt ⊢
      all_goals nlinarith [hrespos]

/-- In the axis-β full-rank branch, the round-21 44-point set drops to 32 points. -/
def axisCandidate : ℤ × ℤ → Bool
  | (x, y) =>
      let n := normSq x y
      decide (0 < n ∧ n < 16 ∧ n ≠ 8 ∧ n ≠ 13)

/-- Kernel-computable count of the remaining lattice points in [-3,3]^2. -/
theorem axisCandidate_count_32 :
    ((List.range 7).flatMap fun i =>
      (List.range 7).map fun j =>
        ((i : ℤ) - 3, (j : ℤ) - 3)).countP axisCandidate = 32 := by
  decide

end D23Round22
