import FormalConjectures.Research.D16R39DiscriminantBridge

/-!
# D16 R40: source equations imply the Round-38 quadratic

This file formalizes the algebraic step from the exact source equations used in
Round 38 to the quadratic handled by `D16R39DiscriminantBridge`.  It is a strict
subproblem of the open A067720 conjecture.  It neither assumes the conjecture nor
claims that the full Round-38 finite enumeration is reflected into Lean.
-/

namespace D16R40SourceToQuadratic

open D16R39DiscriminantBridge

/-- The four exact source equations retained from the Round-38 strict branch. -/
def SourceSystem (p q r s d m u : ℤ) : Prop :=
  p ^ 2 + p + 1 = 3 * r * s ∧
    u = 1 + d * s ∧
    q * u = d ^ 3 - 27 * d * r ^ 2 * p - 27 * r ^ 3 ∧
    q + 27 * r ^ 3 = d * m

/-- Before cancelling `d`, the source equations imply `d` times the target
quadratic.  This form is valid even in the degenerate `d = 0` case. -/
theorem source_equations_give_multiple {p q r s d m u : ℤ}
    (hpsi : p ^ 2 + p + 1 = 3 * r * s)
    (hu : u = 1 + d * s)
    (hE : q * u = d ^ 3 - 27 * d * r ^ 2 * p - 27 * r ^ 3)
    (hm : q + 27 * r ^ 3 = d * m) :
    d * quadratic q r m d p = 0 := by
  unfold quadratic
  linear_combination
    3 * r * hE - 3 * r * q * hu - 3 * r * hm + d * q * hpsi

/-- The nondegenerate source system forces the Round-38 quadratic equation. -/
theorem source_equations_give_quadratic {p q r s d m u : ℤ}
    (hpsi : p ^ 2 + p + 1 = 3 * r * s)
    (hu : u = 1 + d * s)
    (hE : q * u = d ^ 3 - 27 * d * r ^ 2 * p - 27 * r ^ 3)
    (hm : q + 27 * r ^ 3 = d * m)
    (hd : d ≠ 0) :
    quadratic q r m d p = 0 := by
  have hmul := source_equations_give_multiple hpsi hu hE hm
  exact (mul_eq_zero.mp hmul).resolve_left hd

/-- Packaged version using `SourceSystem`. -/
theorem sourceSystem_gives_quadratic {p q r s d m u : ℤ}
    (hsource : SourceSystem p q r s d m u)
    (hd : d ≠ 0) :
    quadratic q r m d p = 0 := by
  rcases hsource with ⟨hpsi, hu, hE, hm⟩
  exact source_equations_give_quadratic hpsi hu hE hm hd

/-- Composing R40 with the R39 discriminant bridge: every nondegenerate source
system forces an explicit square discriminant. -/
theorem sourceSystem_gives_square {p q r s d m u : ℤ}
    (hsource : SourceSystem p q r s d m u)
    (hd : d ≠ 0) :
    ∃ z : ℤ, z ^ 2 = discriminant q r m d := by
  exact root_gives_square (sourceSystem_gives_quadratic hsource hd)

/-- A certified nonsquare discriminant excludes the entire corresponding source
system, including both integer unknowns `p` and `u`. -/
theorem nonsquare_excludes_sourceSystem {q r s d m : ℤ}
    (hd : d ≠ 0)
    (hns : ¬ ∃ z : ℤ, z ^ 2 = discriminant q r m d) :
    ¬ ∃ p u : ℤ, SourceSystem p q r s d m u := by
  rintro ⟨p, u, hsource⟩
  exact hns (sourceSystem_gives_square hsource hd)

/-! ## Exact positive and mutation controls -/

/-- A small exact nondegenerate instance of the source equations. -/
theorem positive_source_instance :
    SourceSystem 10 (-7) 1 37 4 5 149 := by
  norm_num [SourceSystem]

/-- The bridge gives the expected zero quadratic on the positive instance. -/
theorem positive_quadratic_instance :
    quadratic (-7) 1 5 4 10 = 0 := by
  norm_num [quadratic]

/-- All source equations may hold when `d = 0`. -/
theorem zero_d_source_instance :
    SourceSystem 4 (-27) 1 7 0 0 1 := by
  norm_num [SourceSystem]

/-- In the preceding degenerate instance the uncancelled quadratic is nonzero;
thus the hypothesis `d ≠ 0` in the cancellation theorem is essential. -/
theorem zero_d_quadratic_nonzero :
    quadratic (-27) 1 0 0 4 = -243 := by
  norm_num [quadratic]

end D16R40SourceToQuadratic
