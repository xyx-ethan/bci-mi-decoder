import FormalConjectures.Paper.MonochromaticQuantumGraph

/-!
# D19 Round 20: a characteristic-zero pivot-star contraction bridge

For an eight-vertex, three-colour weight system over a field, sum over the
colours of the first two vertices.  The matching expansion consists of the
residual six-vertex matching sum multiplied by the all-colour mass of the
pivot edge, plus a rank-two correction on residual edges.

If that correction is supported on the star at residual vertex `0`, no perfect
matching can use it more than once.  Adding the normalized correction and then
multiplying all edges incident to residual vertex `0` by the pivot mass gives a
six-vertex weight system whose amplitude is exactly the sum over the nine
pivot-colour extensions.  No root extraction and no finite search are used.
-/

open scoped BigOperators
open MonochromaticQuantumGraph

namespace D19Round20

/-- Embed the six residual vertices as old vertices `2, ..., 7`. -/
def liftResidual (u : Fin 6) : Fin 8 := u.succ.succ

/-- Extend a residual colouring by assigning colours `a,b` to old vertices `0,1`. -/
def extendColor (a b : Fin 3) (ι : Fin 6 → Fin 3) : Fin 8 → Fin 3 :=
  Fin.cases a (Fin.cases b ι)

@[simp] theorem extendColor_zero (a b : Fin 3) (ι : Fin 6 → Fin 3) :
    extendColor a b ι 0 = a := by
  rfl

@[simp] theorem extendColor_one (a b : Fin 3) (ι : Fin 6 → Fin 3) :
    extendColor a b ι 1 = b := by
  rfl

@[simp] theorem extendColor_liftResidual (a b : Fin 3) (ι : Fin 6 → Fin 3)
    (u : Fin 6) :
    extendColor a b ι (liftResidual u) = ι u := by
  rfl

/-- Regard a residual endpoint-coloured edge as an edge on old vertices `2, ..., 7`. -/
def residualEdge (e : EdgeN 6 3) : EdgeN 8 3 :=
  mkEdge (liftResidual e.u) (liftResidual e.v) e.i e.j

/-- Sum of all nine endpoint-colour weights on the pivot edge `(0,1)`. -/
def pivotMass {K : Type} [CommSemiring K] (W : WeightsN 8 3 K) : K :=
  ∑ a : Fin 3, ∑ b : Fin 3, W (mkEdge 0 1 a b)

/-- Colour-summed profile from old pivot `0` to a residual vertex. -/
def leftProfile {K : Type} [CommSemiring K] (W : WeightsN 8 3 K)
    (u : Fin 6) (i : Fin 3) : K :=
  ∑ a : Fin 3, W (mkEdge 0 (liftResidual u) a i)

/-- Colour-summed profile from old pivot `1` to a residual vertex. -/
def rightProfile {K : Type} [CommSemiring K] (W : WeightsN 8 3 K)
    (u : Fin 6) (i : Fin 3) : K :=
  ∑ b : Fin 3, W (mkEdge 1 (liftResidual u) b i)

/-- Rank-two correction produced when the two pivots are matched to two distinct
residual vertices.  Only canonically ordered residual edges are read by `pmSumN`. -/
def pivotCorrection {K : Type} [CommSemiring K] (W : WeightsN 8 3 K)
    (e : EdgeN 6 3) : K :=
  leftProfile W e.u e.i * rightProfile W e.v e.j +
    rightProfile W e.u e.i * leftProfile W e.v e.j

/-- The correction has canonical star support at residual vertex `0`.
The condition is intentionally stronger on unused raw `EdgeN` coordinates; this makes
its relation to the recursive ordered matching enumeration explicit. -/
def CorrectionOnZeroStar {K : Type} [CommSemiring K]
    (W : WeightsN 8 3 K) : Prop :=
  ∀ e : EdgeN 6 3, e.u ≠ 0 → pivotCorrection W e = 0

/-- Normalize the correction by the pivot mass and multiply every canonical edge
incident to residual vertex `0` by the pivot mass.  Every perfect matching has exactly
one such edge, so this final star scaling clears the normalization without extracting
a cube root. -/
noncomputable def pivotStarContract {K : Type} [Field K]
    (W : WeightsN 8 3 K) : WeightsN 6 3 K :=
  fun e =>
    let updated := W (residualEdge e) + (pivotMass W)⁻¹ * pivotCorrection W e
    if e.u = 0 then pivotMass W * updated else updated

/-- Exact fixed-size contraction identity.  Under star support, higher correction
terms in the six-vertex matching expansion vanish identically. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
theorem pmSumN_pivotStarContract
    {K : Type} [Field K]
    (W : WeightsN 8 3 K)
    (hs : pivotMass W ≠ 0)
    (hStar : CorrectionOnZeroStar W)
    (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 (pivotStarContract W) ι =
      ∑ a : Fin 3, ∑ b : Fin 3, pmSumN 8 3 W (extendColor a b ι) := by
  classical
  simp [pmSumN, pmSumList, pmSumListAux, vertices, pivotStarContract,
    pivotMass, pivotCorrection, leftProfile, rightProfile, residualEdge,
    liftResidual, extendColor, CorrectionOnZeroStar, hStar, Fin.sum_univ_succ]
  field_simp [hs]
  ring

end D19Round20
