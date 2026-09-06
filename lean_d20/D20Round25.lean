import D20Round24
import Mathlib.Logic.Equiv.Fintype

/-!
# D20 Round 25: an explicit index-one strength-four support projection theorem

For a minimally supported `AME(8,6)` state, every ordered choice of four coordinate positions
induces a bijection from the nonzero computational-basis support to `Config 4 6`.  This is the
precise finite projection property underlying the orthogonal-array / nonlinear-MDS-code bridge.
-/

open OpenQuantumProblem35
open D20Round20 D20Round21 D20Round22 D20Round23 D20Round24

namespace D20Round25

/-- Restrict an eight-symbol configuration to its first four positions. -/
def firstFour (x : Config 8 6) : Config 4 6 :=
  fun i => x (leftIndex (m := 4) (n := 8) (by omega) i)

/-- Restrict an eight-symbol configuration to its last four positions. -/
def lastFour (x : Config 8 6) : Config 4 6 :=
  fun i => x (rightIndex (m := 4) (n := 8) (by omega) i)

/-- Splitting an eight-symbol configuration into its first and last four positions and then
recombining recovers the original configuration. -/
@[simp]
theorem combineFirst_firstFour_lastFour (x : Config 8 6) :
    combineFirst (n := 8) (d := 6) 4 (by omega) (firstFour x) (lastFour x) = x := by
  funext i
  by_cases hi : i.1 < 4
  · simp [combineFirst, firstFour, hi, leftIndex]
  · have hge : 4 ≤ i.1 := Nat.le_of_not_gt hi
    have hsum : 4 + (i.1 - 4) = i.1 := Nat.add_sub_of_le hge
    simp [combineFirst, lastFour, hi, rightIndex, hsum]

/-- In a minimally supported AME state, two nonzero configurations in the same permuted state
are equal as soon as their first four coordinates agree. -/
theorem minSupport_permuted_eq_of_firstFour_eq
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (π : Equiv.Perm (Fin 8))
    (a b : Config 8 6)
    (ha : permuteState π ψ a ≠ 0)
    (hb : permuteState π ψ b ≠ 0)
    (hfirst : firstFour a = firstFour b) :
    a = b := by
  rcases ame8_6_minSupport_unique_completion_perm ψ hψ hcount π (firstFour a) with
    ⟨z, hz, huniq⟩
  have haCompletion :
      permuteState π ψ
        (combineFirst (n := 8) (d := 6) 4 (by omega)
          (firstFour a) (lastFour a)) ≠ 0 := by
    simpa using ha
  have hbCompletion :
      permuteState π ψ
        (combineFirst (n := 8) (d := 6) 4 (by omega)
          (firstFour a) (lastFour b)) ≠ 0 := by
    rw [hfirst]
    simpa using hb
  have hlastA : lastFour a = z := huniq (lastFour a) haCompletion
  have hlastB : lastFour b = z := huniq (lastFour b) hbCompletion
  have hlast : lastFour a = lastFour b := hlastA.trans hlastB.symm
  calc
    a = combineFirst (n := 8) (d := 6) 4 (by omega)
        (firstFour a) (lastFour a) := (combineFirst_firstFour_lastFour a).symm
    _ = combineFirst (n := 8) (d := 6) 4 (by omega)
        (firstFour b) (lastFour b) := by rw [hfirst, hlast]
    _ = b := combineFirst_firstFour_lastFour b

/-- Standard embedding of the first four coordinate positions into eight positions. -/
def standardFirstFour : Fin 4 ↪ Fin 8 where
  toFun i := leftIndex (m := 4) (n := 8) (by omega) i
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa [leftIndex] using congrArg (fun k : Fin 8 => k.1) hij

/-- Projection of a nonzero support word to an ordered selection of four coordinates. -/
def supportProjection
    (ψ : StateVector 8 6) (e : Fin 4 ↪ Fin 8)
    (x : {y : Config 8 6 // ψ y ≠ 0}) : Config 4 6 :=
  fun i => x.1 (e i)

/-- Every ordered four-coordinate projection is injective on the minimal support. -/
theorem ame8_6_minSupport_projection_injective
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (e : Fin 4 ↪ Fin 8) :
    Function.Injective (supportProjection ψ e) := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    standardFirstFour e standardFirstFour.injective e.injective
  intro x y hproj
  apply Subtype.ext
  let a : Config 8 6 := permuteConfig σ x.1
  let b : Config 8 6 := permuteConfig σ y.1
  have ha : permuteState σ.symm ψ a ≠ 0 := by
    simpa [a, permuteConfig_symm_right] using x.2
  have hb : permuteState σ.symm ψ b ≠ 0 := by
    simpa [b, permuteConfig_symm_right] using y.2
  have hfirst : firstFour a = firstFour b := by
    funext i
    have hi := congrFun hproj i
    change x.1 (e i) = y.1 (e i) at hi
    have hσi : σ (standardFirstFour i) = e i := hσ i
    change x.1 (σ (standardFirstFour i)) = y.1 (σ (standardFirstFour i))
    rw [hσi]
    exact hi
  have hab := minSupport_permuted_eq_of_firstFour_eq
    ψ hψ hcount σ.symm a b ha hb hfirst
  have horig := congrArg (permuteConfig σ.symm) hab
  simpa [a, b, permuteConfig_symm_right] using horig

/-- Every ordered four-coordinate projection is bijective on the minimal support.  This is an
index-one strength-four orthogonal-array statement expressed directly in the project types. -/
theorem ame8_6_minSupport_projection_bijective
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (e : Fin 4 ↪ Fin 8) :
    Function.Bijective (supportProjection ψ e) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨ame8_6_minSupport_projection_injective ψ hψ hcount e, ?_⟩
  calc
    Fintype.card {y : Config 8 6 // ψ y ≠ 0} = 1296 := by
      simpa [supportCount] using hcount
    _ = Fintype.card (Config 4 6) := by norm_num [card_config]

/-- Distinct minimal-support words cannot agree on any ordered set of four distinct coordinates.
This is the distance-five form of the projection theorem. -/
theorem ame8_6_minSupport_no_four_coordinate_agreement
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (x y : {w : Config 8 6 // ψ w ≠ 0})
    (hxy : x ≠ y)
    (e : Fin 4 ↪ Fin 8) :
    ∃ i : Fin 4, x.1 (e i) ≠ y.1 (e i) := by
  by_contra h
  apply hxy
  apply ame8_6_minSupport_projection_injective ψ hψ hcount e
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

/-- The project-level index-one strength-four property. -/
def HasIndexOneStrengthFourSupport (ψ : StateVector 8 6) : Prop :=
  ∀ e : Fin 4 ↪ Fin 8, Function.Bijective (supportProjection ψ e)

/-- A minimally supported `AME(8,6)` state has index-one strength-four computational support. -/
theorem ame8_6_minSupport_hasIndexOneStrengthFourSupport
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296) :
    HasIndexOneStrengthFourSupport ψ := by
  intro e
  exact ame8_6_minSupport_projection_bijective ψ hψ hcount e

end D20Round25
