import PMTree6
import PMTree8

/-!
# D19 Round 20: a characteristic-zero pivot-star contraction bridge

For an eight-vertex, three-colour weight system over a field, sum over the
colours of the first two vertices. The matching expansion consists of the
residual six-vertex matching sum multiplied by the all-colour mass of the
pivot edge, plus a rank-two correction on residual edges.

If that correction is supported on the canonical star at residual vertex `0`,
no perfect matching can use it more than once. Adding the normalized correction
and then multiplying all canonical edges incident to residual vertex `0` by the
pivot mass gives a six-vertex weight system whose amplitude is exactly the sum
over the nine pivot-colour extensions. No root extraction and no finite search
are used.
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
residual vertices. Only canonically ordered residual edges are read by `pmSumN`. -/
def pivotCorrection {K : Type} [CommSemiring K] (W : WeightsN 8 3 K)
    (e : EdgeN 6 3) : K :=
  leftProfile W e.u e.i * rightProfile W e.v e.j +
    rightProfile W e.u e.i * leftProfile W e.v e.j

/-- Reverse both residual endpoints and their endpoint colours. -/
def reverseResidualEdge (e : EdgeN 6 3) : EdgeN 6 3 :=
  mkEdge e.v e.u e.j e.i

/-- The correction is invariant under simultaneous reversal of endpoints and colours. -/
theorem pivotCorrection_reverse
    {K : Type} [CommSemiring K]
    (W : WeightsN 8 3 K) (e : EdgeN 6 3) :
    pivotCorrection W (reverseResidualEdge e) = pivotCorrection W e := by
  simp only [reverseResidualEdge, pivotCorrection, mkEdge]
  ring

/-- Legacy raw-coordinate predicate. Because `EdgeN` contains both endpoint orders,
this condition is stronger than canonical star support. -/
def CorrectionOnRawZeroStar {K : Type} [CommSemiring K]
    (W : WeightsN 8 3 K) : Prop :=
  ∀ e : EdgeN 6 3, e.u ≠ 0 → pivotCorrection W e = 0

/-- Correct support predicate: among the canonical coordinates `u < v` read by
`pmSumN`, the correction may be nonzero only when `u = 0`. -/
def CorrectionOnZeroStar {K : Type} [CommSemiring K]
    (W : WeightsN 8 3 K) : Prop :=
  ∀ u v : Fin 6, u < v → u ≠ 0 →
    ∀ i j : Fin 3, pivotCorrection W (mkEdge u v i j) = 0

/-- The raw-coordinate predicate implies the repaired canonical predicate. -/
theorem rawZeroStar_implies_zeroStar
    {K : Type} [CommSemiring K]
    (W : WeightsN 8 3 K)
    (hRaw : CorrectionOnRawZeroStar W) :
    CorrectionOnZeroStar W := by
  intro u v huv hu i j
  exact hRaw (mkEdge u v i j) (by simpa [mkEdge] using hu)

/-- Semantic audit: the raw-coordinate predicate actually kills every live
canonical correction, including those on the star, because the reversed raw
coordinate has nonzero first endpoint. -/
theorem rawZeroStar_forces_allCanonical
    {K : Type} [CommSemiring K]
    (W : WeightsN 8 3 K)
    (hRaw : CorrectionOnRawZeroStar W)
    (u v : Fin 6) (huv : u < v) (i j : Fin 3) :
    pivotCorrection W (mkEdge u v i j) = 0 := by
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by omega
    have hrev := hRaw (reverseResidualEdge (mkEdge u v i j)) (by
      simpa [reverseResidualEdge, mkEdge] using hv)
    rw [pivotCorrection_reverse] at hrev
    exact hrev
  · exact hRaw (mkEdge u v i j) (by simpa [mkEdge] using hu)

/-- Normalize the correction by the pivot mass and multiply every canonical edge
incident to residual vertex `0` by the pivot mass. Every perfect matching has exactly
one such edge, so this final star scaling clears the normalization without extracting
a cube root. -/
noncomputable def pivotStarContract {K : Type} [Field K]
    (W : WeightsN 8 3 K) : WeightsN 6 3 K :=
  fun e =>
    let updated := W (residualEdge e) + (pivotMass W)⁻¹ * pivotCorrection W e
    if e.u = 0 then pivotMass W * updated else updated

/-- Exact fixed-size contraction identity. Under canonical star support,
higher correction terms in the six-vertex matching expansion vanish identically. -/
set_option maxHeartbeats 10000000 in
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
  have h12 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (1 : Fin 6) 2 i j) = 0 :=
    hStar 1 2 (by decide) (by decide)
  have h13 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (1 : Fin 6) 3 i j) = 0 :=
    hStar 1 3 (by decide) (by decide)
  have h14 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (1 : Fin 6) 4 i j) = 0 :=
    hStar 1 4 (by decide) (by decide)
  have h15 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (1 : Fin 6) 5 i j) = 0 :=
    hStar 1 5 (by decide) (by decide)
  have h23 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (2 : Fin 6) 3 i j) = 0 :=
    hStar 2 3 (by decide) (by decide)
  have h24 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (2 : Fin 6) 4 i j) = 0 :=
    hStar 2 4 (by decide) (by decide)
  have h25 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (2 : Fin 6) 5 i j) = 0 :=
    hStar 2 5 (by decide) (by decide)
  have h34 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (3 : Fin 6) 4 i j) = 0 :=
    hStar 3 4 (by decide) (by decide)
  have h35 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (3 : Fin 6) 5 i j) = 0 :=
    hStar 3 5 (by decide) (by decide)
  have h45 : ∀ i j : Fin 3,
      pivotCorrection W (mkEdge (4 : Fin 6) 5 i j) = 0 :=
    hStar 4 5 (by decide) (by decide)
  rw [pmSumN_six_eq_tree]
  simp_rw [pmSumN_eight_eq_tree]
  simp [pmTree6, pmTree8, pmTree8Branch1, pmTree8Branch2, pmTree8Branch3,
    pmTree8Branch4, pmTree8Branch5, pmTree8Branch6, pmTree8Branch7,
    pivotStarContract, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
    pivotMass, pivotCorrection, leftProfile, rightProfile,
    residualEdge, liftResidual, extendColor, Fin.sum_univ_succ]
  field_simp [hs]
  ring

end D19Round20
