import D20Round23

/-!
# D20 Round 24: minimal support forces equal Born weights

For an `AME(8,6)` state whose computational-basis support attains the lower bound `1296`,
every nonzero cell of the fixed first-four/last-four computational decomposition has squared
modulus exactly `1/1296`.  Thus the remaining freedom on the minimal-support branch is in the
support combinatorics and phases, not in amplitude magnitudes.
-/

open scoped BigOperators
open OpenQuantumProblem35
open D20Round20 D20Round21 D20Round22 D20Round23

namespace D20Round24

/-- Under minimal computational support, a nonzero basis cell carries exactly the full uniform
four-prefix probability mass. -/
theorem ame8_6_minSupport_nonzero_cell_normSq
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (x z : Config 4 6)
    (hz : ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z) ≠ 0) :
    Complex.normSq
        (ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z)) =
      (1 : ℝ) / 1296 := by
  classical
  rcases ame8_6_minSupport_unique_completion ψ hψ hcount x with ⟨w, hw, huniq⟩
  have hzw : z = w := huniq z hz
  subst w
  have hmass := ame8_6_fourBlockMass_uniform ψ hψ (Equiv.refl (Fin 8)) x
  rw [fourBlockMass] at hmass
  simp_rw [permuteState_refl] at hmass
  have hsum :
      (∑ z' : Config 4 6,
        basisProb ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z')) =
      basisProb ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z) := by
    refine Fintype.sum_eq_single z ?_
    intro z' hne
    have hz'zero :
        ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z') = 0 := by
      by_contra hnonzero
      have hz'eq : z' = z := huniq z' hnonzero
      exact hne hz'eq
    simp [basisProb, hz'zero]
  rw [hsum] at hmass
  simpa [basisProb] using hmass

end D20Round24
