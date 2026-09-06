import FormalConjectures.Paper.MonochromaticQuantumGraph

/-!
# D19 pivot contraction on the three-active-residual-vertex branch

A fixed-size algebraic bridge from a constrained eight-vertex solution to the official
six-vertex equation system.
-/

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

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

/-- The official six-vertex edge selected by endpoints and a colouring. -/
def edgeWeight6 {D : Nat} {α : Type} [CommSemiring α]
    (W : WeightsN 6 D α) (ι : V 6 → Fin D) (u v : V 6) : α :=
  W (mkEdge u v (ι u) (ι v))

/-- Exact fifteen-term expansion of the official six-vertex matching sum. -/
theorem pmSumN_six_explicit {D : Nat} {α : Type} [CommSemiring α]
    (W : WeightsN 6 D α) (ι : V 6 → Fin D) :
    pmSumN 6 D W ι =
        edgeWeight6 W ι 0 1 * edgeWeight6 W ι 2 3 * edgeWeight6 W ι 4 5
      + edgeWeight6 W ι 0 1 * edgeWeight6 W ι 2 4 * edgeWeight6 W ι 3 5
      + edgeWeight6 W ι 0 1 * edgeWeight6 W ι 2 5 * edgeWeight6 W ι 3 4
      + edgeWeight6 W ι 0 2 * edgeWeight6 W ι 1 3 * edgeWeight6 W ι 4 5
      + edgeWeight6 W ι 0 2 * edgeWeight6 W ι 1 4 * edgeWeight6 W ι 3 5
      + edgeWeight6 W ι 0 2 * edgeWeight6 W ι 1 5 * edgeWeight6 W ι 3 4
      + edgeWeight6 W ι 0 3 * edgeWeight6 W ι 1 2 * edgeWeight6 W ι 4 5
      + edgeWeight6 W ι 0 3 * edgeWeight6 W ι 1 4 * edgeWeight6 W ι 2 5
      + edgeWeight6 W ι 0 3 * edgeWeight6 W ι 1 5 * edgeWeight6 W ι 2 4
      + edgeWeight6 W ι 0 4 * edgeWeight6 W ι 1 2 * edgeWeight6 W ι 3 5
      + edgeWeight6 W ι 0 4 * edgeWeight6 W ι 1 3 * edgeWeight6 W ι 2 5
      + edgeWeight6 W ι 0 4 * edgeWeight6 W ι 1 5 * edgeWeight6 W ι 2 3
      + edgeWeight6 W ι 0 5 * edgeWeight6 W ι 1 2 * edgeWeight6 W ι 3 4
      + edgeWeight6 W ι 0 5 * edgeWeight6 W ι 1 3 * edgeWeight6 W ι 2 4
      + edgeWeight6 W ι 0 5 * edgeWeight6 W ι 1 4 * edgeWeight6 W ι 2 3 := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices, edgeWeight6]
  ring

/-- Matching sum on four explicitly listed residual vertices. -/
def fourMatchSum (X : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3)
    (a b c d : Fin 6) : ℂ :=
  edgeWeight6 X ι a b * edgeWeight6 X ι c d +
  edgeWeight6 X ι a c * edgeWeight6 X ι b d +
  edgeWeight6 X ι a d * edgeWeight6 X ι b c

/-- The full linear-in-update part indexed by the fifteen residual endpoint pairs. -/
def linearUpdateSum (W : WeightsN 8 3 ℂ) (ι : Fin 6 → Fin 3) : ℂ :=
  let X := residualWeight W
  let R := pivotUpdate W
  edgeWeight6 R ι 0 1 * fourMatchSum X ι 2 3 4 5 +
  edgeWeight6 R ι 0 2 * fourMatchSum X ι 1 3 4 5 +
  edgeWeight6 R ι 0 3 * fourMatchSum X ι 1 2 4 5 +
  edgeWeight6 R ι 0 4 * fourMatchSum X ι 1 2 3 5 +
  edgeWeight6 R ι 0 5 * fourMatchSum X ι 1 2 3 4 +
  edgeWeight6 R ι 1 2 * fourMatchSum X ι 0 3 4 5 +
  edgeWeight6 R ι 1 3 * fourMatchSum X ι 0 2 4 5 +
  edgeWeight6 R ι 1 4 * fourMatchSum X ι 0 2 3 5 +
  edgeWeight6 R ι 1 5 * fourMatchSum X ι 0 2 3 4 +
  edgeWeight6 R ι 2 3 * fourMatchSum X ι 0 1 4 5 +
  edgeWeight6 R ι 2 4 * fourMatchSum X ι 0 1 3 5 +
  edgeWeight6 R ι 2 5 * fourMatchSum X ι 0 1 3 4 +
  edgeWeight6 R ι 3 4 * fourMatchSum X ι 0 1 2 5 +
  edgeWeight6 R ι 3 5 * fourMatchSum X ι 0 1 2 4 +
  edgeWeight6 R ι 4 5 * fourMatchSum X ι 0 1 2 3

lemma allEqual_extend_iff (a b : Fin 3) (ι : Fin 6 → Fin 3) :
    allEqual (extendColor a b ι) ↔
      a = b ∧ b = ι 0 ∧ allEqual ι := by
  simp [allEqual, allEqualList, vertices, extendColor]

/-- The target values of the nine pivot-colour extensions sum to the six-vertex target value. -/
lemma extension_target_sum (ι : Fin 6 → Fin 3) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      if allEqual (extendColor a b ι) then (1 : ℂ) else 0) =
        (if allEqual ι then (1 : ℂ) else 0) := by
  classical
  by_cases hι : allEqual ι
  · have hinner (a c : Fin 3) :
        (∑ b : Fin 3, if a = b ∧ b = c then (1 : ℂ) else 0) =
          (if a = c then 1 else 0) := by
      by_cases hac : a = c
      · subst a
        simp
      · simp [hac]
    simp_rw [allEqual_extend_iff, hι, hinner]
    simp
  · simp [allEqual_extend_iff, hι]

/-- Partition the eight-vertex matchings by whether the two pivots are paired together. -/
lemma extension_sum_eq_compact
    (W : WeightsN 8 3 ℂ) (ι : Fin 6 → Fin 3) :
    (∑ a : Fin 3, ∑ b : Fin 3, pmSumN 8 3 W (extendColor a b ι)) =
      pivotSum W * pmSumN 6 3 (residualWeight W) ι + linearUpdateSum W ι := by
  classical
  simp [pmSumN, pmSumList, pmSumListAux, vertices]
  simp [linearUpdateSum, fourMatchSum, edgeWeight6, residualWeight, pivotUpdate,
    pivotSum, leftLeg, rightLeg, liftResidual, extendColor, Fin.sum_univ_succ]
  ring

/-- Exact fixed-size contraction identity for the three-active-residual-vertex branch. -/
theorem contracted_pmSum_eq_extension_sum
    (W : WeightsN 8 3 ℂ)
    (hs : pivotSum W ≠ 0)
    (hactive : ThreeActivePivot W)
    (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 (contractedWeight W) ι =
      ∑ a : Fin 3, ∑ b : Fin 3, pmSumN 8 3 W (extendColor a b ι) := by
  classical
  rw [extension_sum_eq_compact]
  have hU (u v : Fin 6) (i j : Fin 3) (hv : 3 ≤ v.1) :
      pivotUpdate W (mkEdge u v i j) = 0 := by
    have hA := (hactive v hv j).1
    have hB := (hactive v hv j).2
    change leftLeg W u i * rightLeg W v j +
      rightLeg W u i * leftLeg W v j = 0
    simp [hA, hB]
  have hU03 (i j : Fin 3) : pivotUpdate W (mkEdge 0 3 i j) = 0 :=
    hU 0 3 i j (by norm_num)
  have hU04 (i j : Fin 3) : pivotUpdate W (mkEdge 0 4 i j) = 0 :=
    hU 0 4 i j (by norm_num)
  have hU05 (i j : Fin 3) : pivotUpdate W (mkEdge 0 5 i j) = 0 :=
    hU 0 5 i j (by norm_num)
  have hU13 (i j : Fin 3) : pivotUpdate W (mkEdge 1 3 i j) = 0 :=
    hU 1 3 i j (by norm_num)
  have hU14 (i j : Fin 3) : pivotUpdate W (mkEdge 1 4 i j) = 0 :=
    hU 1 4 i j (by norm_num)
  have hU15 (i j : Fin 3) : pivotUpdate W (mkEdge 1 5 i j) = 0 :=
    hU 1 5 i j (by norm_num)
  have hU23 (i j : Fin 3) : pivotUpdate W (mkEdge 2 3 i j) = 0 :=
    hU 2 3 i j (by norm_num)
  have hU24 (i j : Fin 3) : pivotUpdate W (mkEdge 2 4 i j) = 0 :=
    hU 2 4 i j (by norm_num)
  have hU25 (i j : Fin 3) : pivotUpdate W (mkEdge 2 5 i j) = 0 :=
    hU 2 5 i j (by norm_num)
  have hU34 (i j : Fin 3) : pivotUpdate W (mkEdge 3 4 i j) = 0 :=
    hU 3 4 i j (by norm_num)
  have hU35 (i j : Fin 3) : pivotUpdate W (mkEdge 3 5 i j) = 0 :=
    hU 3 5 i j (by norm_num)
  have hU45 (i j : Fin 3) : pivotUpdate W (mkEdge 4 5 i j) = 0 :=
    hU 4 5 i j (by norm_num)
  simp_rw [pmSumN_six_explicit]
  simp [edgeWeight6, contractedWeight, updatedWeight, residualWeight,
    linearUpdateSum, fourMatchSum,
    hU03, hU04, hU05, hU13, hU14, hU15,
    hU23, hU24, hU25, hU34, hU35, hU45]
  simp [pivotUpdate]
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
  exact extension_target_sum ι

/-- Assuming the known six-vertex nonexistence proposition, the three-active pivot branch is empty. -/
theorem no_eqSystem8_threeActivePivot
    (h6 : ¬ ∃ U : WeightsN 6 3 ℂ, EqSystemN 6 3 U) :
    ¬ ∃ W : WeightsN 8 3 ℂ,
      EqSystemN 8 3 W ∧ pivotSum W ≠ 0 ∧ ThreeActivePivot W := by
  rintro ⟨W, hW, hs, hactive⟩
  exact h6 ⟨contractedWeight W,
    eqSystem6_of_eqSystem8_threeActivePivot W hW hs hactive⟩

end D19PivotContraction
