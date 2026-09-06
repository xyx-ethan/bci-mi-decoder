import D20Round20

/-!
# D20 Round 21: a kernel-certified product-basis support lower bound for AME(8,6)

This file uses the Round-20 exact four-party cylinder-mass theorem and proves that every
`AME(8,6)` state has at least `6^4 = 1296` nonzero amplitudes in the computational basis.
The argument is purely finite: every four-symbol prefix has positive Born mass, hence at least
one nonzero completion, and distinct prefixes give distinct basis configurations.
-/

open OpenQuantumProblem35
open D20Round20

namespace D20Round21

/-- Number of nonzero computational-basis amplitudes of an eight-party quhex state. -/
noncomputable def supportCount (ψ : StateVector 8 6) : ℕ :=
  Fintype.card {x : Config 8 6 // ψ x ≠ 0}

/-- Every four-symbol computational-basis prefix of an `AME(8,6)` state has a nonzero completion. -/
theorem ame8_6_fourPrefix_has_nonzero_completion
    (ψ : StateVector 8 6) (hψ : IsAME ψ) (x : Config 4 6) :
    ∃ z : Config 4 6,
      ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z) ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : fourBlockMass ψ (Equiv.refl (Fin 8)) x = 0 := by
    simp [fourBlockMass, basisProb, permuteState_refl, h]
  have hunif := ame8_6_fourBlockMass_uniform ψ hψ (Equiv.refl (Fin 8)) x
  rw [hzero] at hunif
  norm_num at hunif

/-- Every `AME(8,6)` state has at least `1296 = 6^4` nonzero computational-basis amplitudes. -/
theorem ame8_6_supportCount_ge_1296
    (ψ : StateVector 8 6) (hψ : IsAME ψ) :
    1296 ≤ supportCount ψ := by
  classical
  choose z hz using fun x : Config 4 6 => ame8_6_fourPrefix_has_nonzero_completion ψ hψ x
  have hinj : Function.Injective
      (fun x : Config 4 6 =>
        (⟨combineFirst (n := 8) (d := 6) 4 (by omega) x (z x), hz x⟩ :
          {y : Config 8 6 // ψ y ≠ 0})) := by
    intro x y hxy
    apply funext
    intro i
    have hcoord := congrArg
      (fun q : {y : Config 8 6 // ψ y ≠ 0} => q.1 (leftIndex (by omega) i)) hxy
    simpa using hcoord
  have hcard :
      Fintype.card (Config 4 6) ≤ Fintype.card {y : Config 8 6 // ψ y ≠ 0} :=
    Fintype.card_le_of_injective _ hinj
  simpa [supportCount, card_config] using hcard

end D20Round21
