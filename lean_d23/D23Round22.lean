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
  have hNo8 : normSq wx wy ≠ 8 := by
    intro hN
    rcases haxis with hA | hB
    · subst A
      have hb2 : B * B = p * p := by simpa [normSq] using hbeta
      rcases (mul_self_eq_mul_self_iff.mp hb2) with hBp | hBn
      · subst B
        have hwy2 : wy * wy ≤ 8 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wx]
        have hwylt : wy < 3 := by nlinarith
        have hwyle : wy ≤ 2 := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
      · subst B
        have hwy2 : wy * wy ≤ 8 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wx]
        have hwygt : -3 < wy := by nlinarith
        have hwyge : -2 ≤ wy := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
    · subst B
      have ha2 : A * A = p * p := by simpa [normSq] using hbeta
      rcases (mul_self_eq_mul_self_iff.mp ha2) with hAp | hAn
      · subst A
        have hwx2 : wx * wx ≤ 8 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wy]
        have hwxlt : wx < 3 := by nlinarith
        have hwxle : wx ≤ 2 := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
      · subst A
        have hwx2 : wx * wx ≤ 8 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wy]
        have hwxgt : -3 < wx := by nlinarith
        have hwxge : -2 ≤ wx := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
  have hNo13 : normSq wx wy ≠ 13 := by
    intro hN
    rcases haxis with hA | hB
    · subst A
      have hb2 : B * B = p * p := by simpa [normSq] using hbeta
      rcases (mul_self_eq_mul_self_iff.mp hb2) with hBp | hBn
      · subst B
        have hwy2 : wy * wy ≤ 13 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wx]
        have hwylt : wy < 4 := by nlinarith
        have hwyle : wy ≤ 3 := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
      · subst B
        have hwy2 : wy * wy ≤ 13 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wx]
        have hwygt : -4 < wy := by nlinarith
        have hwyge : -3 ≤ wy := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
    · subst B
      have ha2 : A * A = p * p := by simpa [normSq] using hbeta
      rcases (mul_self_eq_mul_self_iff.mp ha2) with hAp | hAn
      · subst A
        have hwx2 : wx * wx ≤ 13 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wy]
        have hwxlt : wx < 4 := by nlinarith
        have hwxle : wx ≤ 3 := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
      · subst A
        have hwx2 : wx * wx ≤ 13 := by
          simp only [normSq] at hN
          nlinarith [sq_nonneg wy]
        have hwxgt : -4 < wx := by nlinarith
        have hwxge : -3 ≤ wx := by omega
        have he := henergy
        rw [hN] at he
        simp at he
        nlinarith [hrespos]
  have hcases := fullRank_scalar_norm_cases
    p q A B wx wy tx ty rx ry sx sy hp hpq hbeta hdet henergy
  rcases hcases with h1 | h2 | h4 | h5 | h8 | h9 | h10 | h13
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h4))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
  · exact (hNo8 h8).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h10))))
  · exact (hNo13 h13).elim

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
