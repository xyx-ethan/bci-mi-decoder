import Mathlib

/-!
# D16 R39: quadratic-discriminant bridge for the A067720 four-factor branch

This file formalizes the generic algebraic obstruction used by the Round-38
finite certificate.  It does not assume the open A067720 conjecture and it does
not claim that the full Round-38 finite enumeration has been reflected into
Lean.
-/

namespace D16R39DiscriminantBridge

/-- The integer quadratic forced on a candidate prime parameter `p` in the
Round-38 four-factor branch. -/
def quadratic (q r m d p : ℤ) : ℤ :=
  q * p ^ 2 + (q + 81 * r ^ 3) * p + q + 3 * r * m - 3 * r * d ^ 2

/-- Its discriminant. -/
def discriminant (q r m d : ℤ) : ℤ :=
  (q + 81 * r ^ 3) ^ 2 - 4 * q * (q + 3 * r * m - 3 * r * d ^ 2)

/-- Completing the square for the Round-38 quadratic. -/
theorem discriminant_identity (q r m d p : ℤ) :
    (2 * q * p + (q + 81 * r ^ 3)) ^ 2 - discriminant q r m d =
      4 * q * quadratic q r m d p := by
  unfold quadratic discriminant
  ring

/-- Every integer root forces the discriminant to be an integer square. -/
theorem root_gives_square {q r m d p : ℤ}
    (hroot : quadratic q r m d p = 0) :
    ∃ z : ℤ, z ^ 2 = discriminant q r m d := by
  refine ⟨2 * q * p + (q + 81 * r ^ 3), ?_⟩
  have h := discriminant_identity q r m d p
  have hz :
      (2 * q * p + (q + 81 * r ^ 3)) ^ 2 - discriminant q r m d = 0 := by
    calc
      (2 * q * p + (q + 81 * r ^ 3)) ^ 2 - discriminant q r m d =
          4 * q * quadratic q r m d p := h
      _ = 0 := by rw [hroot]; ring
  exact sub_eq_zero.mp hz

/-- A certified nonsquare discriminant excludes every integer value of `p`. -/
theorem nonsquare_no_integer_root {q r m d : ℤ}
    (hns : ¬ ∃ z : ℤ, z ^ 2 = discriminant q r m d) :
    ¬ ∃ p : ℤ, quadratic q r m d p = 0 := by
  rintro ⟨p, hp⟩
  exact hns (root_gives_square hp)

/-- A negative discriminant is a particularly simple root obstruction. -/
theorem negative_discriminant_no_integer_root {q r m d : ℤ}
    (hneg : discriminant q r m d < 0) :
    ¬ ∃ p : ℤ, quadratic q r m d p = 0 := by
  apply nonsquare_no_integer_root
  rintro ⟨z, hz⟩
  have hsq : 0 ≤ z ^ 2 := sq_nonneg z
  rw [hz] at hsq
  omega

/-! ## Exact audit of the released Round-38 range totals -/

theorem range_partition_totals :
    116 + 182 + 281 + 513 + 965 + 1 = 2058 ∧
    18 + 572 + 7911 + 116322 + 1742136 + 4173 = 1871132 ∧
    56 + 1765 + 25233 + 364416 + 5448423 + 12146 = 5852039 ∧
    129 + 4258 + 61829 + 894191 + 13360921 + 29793 = 14351121 ∧
    259 + 8774 + 127148 + 1838638 + 27474183 + 61240 = 29510242 ∧
    83 + 2556 + 36542 + 528559 + 7899157 + 17609 = 8484506 := by
  norm_num

/-! ## Exact integer-width audit for the released checker bounds -/

theorem discriminant_bound_bitlength :
    2 ^ 104 ≤ (26935368824271383820149270433065 : ℕ) ∧
      (26935368824271383820149270433065 : ℕ) < 2 ^ 105 := by
  norm_num

theorem maxW_bitlength :
    2 ^ 50 ≤ (1729944729091124 : ℕ) ∧
      (1729944729091124 : ℕ) < 2 ^ 51 := by
  norm_num

theorem maxd_bitlength :
    2 ^ 25 ≤ (41592604 : ℕ) ∧ (41592604 : ℕ) < 2 ^ 26 := by
  norm_num

theorem maxAbsQ_bitlength :
    2 ^ 19 ≤ (953356 : ℕ) ∧ (953356 : ℕ) < 2 ^ 20 := by
  norm_num

end D16R39DiscriminantBridge
