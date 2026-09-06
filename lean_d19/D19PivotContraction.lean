import FormalConjectures.Paper.MonochromaticQuantumGraph

/-!
# D19 pivot contraction on the three-active-residual-vertex branch

A fixed-size algebraic bridge from a constrained eight-vertex solution to the official
six-vertex equation system.
-/

open scoped BigOperators

noncomputable section

namespace D19PivotContraction

open MonochromaticQuantumGraph

/-- Reindex the six residual vertices as the original vertices `2,...,7`. -/
def liftResidual (u : Fin 6) : Fin 8 :=
  ⟨u.1 + 2, by omega⟩

/-- Extend a residual colouring by colours on the two pivot vertices. -/
def extendColor (a b : Fin 3) (ι : Fin 6 → Fin 3) (v : Fin 8) : Fin 3 :=
  if h0 : v.1 = 0 then a
  else if h1 : v.1 = 1 then b
  else ι ⟨v.1 - 2, by omega⟩

/-- Sum of all endpoint-colour weights on the pivot edge `(0,1)`. -/
def pivotSum (W : WeightsN 8 3 ℂ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, W (mkEdge 0 1 a b)

/-- Colour-summed leg from pivot vertex `0` to residual vertex `u`. -/
def leftLeg (W : WeightsN 8 3 ℂ) (u : Fin 6) (c : Fin 3) : ℂ :=
  ∑ a : Fin 3, W (mkEdge 0 (liftResidual u) a c)

/-- Colour-summed leg from pivot vertex `1` to residual vertex `u`. -/
def rightLeg (W : WeightsN 8 3 ℂ) (u : Fin 6) (c : Fin 3) : ℂ :=
  ∑ b : Fin 3, W (mkEdge 1 (liftResidual u) b c)

/-- Restriction of the original weights to the six residual vertices. -/
def residualWeight (W : WeightsN 8 3 ℂ) : WeightsN 6 3 ℂ :=
  fun e => W (mkEdge (liftResidual e.u) (liftResidual e.v) e.i e.j)

/-- Symmetric rank-two update produced when the pivots are matched to two residual vertices. -/
def pivotUpdate (W : WeightsN 8 3 ℂ) : WeightsN 6 3 ℂ :=
  fun e =>
    leftLeg W e.u e.i * rightLeg W e.v e.j +
      rightLeg W e.u e.i * leftLeg W e.v e.j

/-- Polynomially scaled residual update. -/
def updatedWeight (W : WeightsN 8 3 ℂ) : WeightsN 6 3 ℂ :=
  fun e => pivotSum W * residualWeight W e + pivotUpdate W e

/-- Normalize the update by scaling exactly the matching edge incident to residual vertex `0`. -/
def contractedWeight (W : WeightsN 8 3 ℂ) : WeightsN 6 3 ℂ :=
  fun e =>
    if e.u = (0 : Fin 6) then
      (pivotSum W ^ 2)⁻¹ * updatedWeight W e
    else
      updatedWeight W e

/-- The two pivot-leg vectors vanish outside three residual vertices. -/
def ThreeActivePivot (W : WeightsN 8 3 ℂ) : Prop :=
  ∀ u : Fin 6, 3 ≤ u.1 → ∀ c : Fin 3,
    leftLeg W u c = 0 ∧ rightLeg W u c = 0

lemma allEqual_extend_iff (a b : Fin 3) (ι : Fin 6 → Fin 3) :
    allEqual (extendColor a b ι) ↔
      a = b ∧ b = ι 0 ∧ allEqual ι := by
  simp [allEqual, allEqualList, vertices, extendColor]

/-- Exact fixed-size contraction identity for the three-active-residual-vertex branch. -/
theorem contracted_pmSum_eq_extension_sum
    (W : WeightsN 8 3 ℂ)
    (hs : pivotSum W ≠ 0)
    (hactive : ThreeActivePivot W)
    (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 (contractedWeight W) ι =
      ∑ a : Fin 3, ∑ b : Fin 3, pmSumN 8 3 W (extendColor a b ι) := by
  classical
  have hA3 (c : Fin 3) : leftLeg W (3 : Fin 6) c = 0 :=
    (hactive 3 (by norm_num) c).1
  have hB3 (c : Fin 3) : rightLeg W (3 : Fin 6) c = 0 :=
    (hactive 3 (by norm_num) c).2
  have hA4 (c : Fin 3) : leftLeg W (4 : Fin 6) c = 0 :=
    (hactive 4 (by norm_num) c).1
  have hB4 (c : Fin 3) : rightLeg W (4 : Fin 6) c = 0 :=
    (hactive 4 (by norm_num) c).2
  have hA5 (c : Fin 3) : leftLeg W (5 : Fin 6) c = 0 :=
    (hactive 5 (by norm_num) c).1
  have hB5 (c : Fin 3) : rightLeg W (5 : Fin 6) c = 0 :=
    (hactive 5 (by norm_num) c).2
  simp [pmSumN, pmSumList, pmSumListAux, vertices]
  simp [contractedWeight, updatedWeight, residualWeight, pivotUpdate, liftResidual,
    hA3, hB3, hA4, hB4, hA5, hB5]
  simp [pivotSum, leftLeg, rightLeg, extendColor, Fin.sum_univ_succ]
  field_simp [hs] <;> ring

/-- A solution on eight vertices in this branch contracts to a six-vertex solution. -/
theorem eqSystem6_of_eqSystem8_threeActivePivot
    (W : WeightsN 8 3 ℂ)
    (hW : EqSystemN 8 3 W)
    (hs : pivotSum W ≠ 0)
    (hactive : ThreeActivePivot W) :
    EqSystemN 6 3 (contractedWeight W) := by
  classical
  unfold EqSystemN at hW ⊢
  intro ι
  rw [contracted_pmSum_eq_extension_sum W hs hactive ι]
  simp_rw [hW]
  by_cases hι : allEqual ι
  · simp [allEqual_extend_iff, hι]
  · simp [allEqual_extend_iff, hι]

/-- Assuming the known six-vertex nonexistence proposition, the three-active pivot branch is empty. -/
theorem no_eqSystem8_threeActivePivot
    (h6 : ¬ ∃ U : WeightsN 6 3 ℂ, EqSystemN 6 3 U) :
    ¬ ∃ W : WeightsN 8 3 ℂ,
      EqSystemN 8 3 W ∧ pivotSum W ≠ 0 ∧ ThreeActivePivot W := by
  rintro ⟨W, hW, hs, hactive⟩
  exact h6 ⟨contractedWeight W,
    eqSystem6_of_eqSystem8_threeActivePivot W hW hs hactive⟩

end D19PivotContraction
