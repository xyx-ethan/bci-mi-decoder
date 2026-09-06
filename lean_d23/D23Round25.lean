import D23Round22

namespace D23Round25

open D23Round21 D23Round22

/--
Semantic repair for the D23 Gaussian branch.

If an odd integer `p` is represented as `p = a^2 + b^2` with both Gaussian
coordinates nonzero, then the square

  `(a + bi)^2 = (a^2 - b^2) + (2ab)i`

has both coordinates nonzero.  Consequently the genuine split-Gaussian square
branch is disjoint from the axis-beta hypothesis used in D23 Round 22.
-/
theorem splitGaussianSquare_nonaxis
    (p a b : ℤ)
    (hpodd : Odd p)
    (hnorm : a * a + b * b = p)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    a * a - b * b ≠ 0 ∧ 2 * a * b ≠ 0 := by
  constructor
  · intro hreal
    have hab2 : a * a = b * b := by
      nlinarith
    have hpeven : Even p := by
      refine ⟨b * b, ?_⟩
      nlinarith [hnorm, hab2]
    exact (Int.not_even_iff_odd.2 hpodd) hpeven
  · exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb

/-- Exact disjointness with the axis condition from Round 22. -/
theorem splitGaussianSquare_disjoint_axisBeta
    (p a b : ℤ)
    (hpodd : Odd p)
    (hnorm : a * a + b * b = p)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ¬ ((a * a - b * b = 0) ∨ (2 * a * b = 0)) := by
  intro haxis
  obtain ⟨hreal, himag⟩ := splitGaussianSquare_nonaxis p a b hpodd hnorm ha hb
  rcases haxis with h | h
  · exact hreal h
  · exact himag h

/-- The non-axis property is preserved by the sign/conjugation/swap operations
used by the elementary D4 action on Gaussian coordinates. -/
theorem nonaxis_preserved_basicD4
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (-x ≠ 0 ∧ -y ≠ 0) ∧
    (y ≠ 0 ∧ x ≠ 0) ∧
    (x ≠ 0 ∧ -y ≠ 0) := by
  constructor
  · exact ⟨neg_ne_zero.mpr hx, neg_ne_zero.mpr hy⟩
  constructor
  · exact ⟨hy, hx⟩
  · exact ⟨hx, neg_ne_zero.mpr hy⟩

end D23Round25
