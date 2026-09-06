import FormalConjectures.OpenQuantumProblems.«35»

open scoped BigOperators
open OpenQuantumProblem35

namespace D20Round20

/-- Computational-basis Born probability of a state vector coordinate. -/
noncomputable def basisProb {n d : ℕ} (ψ : StateVector n d) (x : Config n d) : ℝ :=
  Complex.normSq (ψ x)

/--
For an eight-party state, after a party permutation `π`, the probability mass of a fixed
four-symbol prefix, summing over the remaining four parties.
-/
noncomputable def fourBlockMass (ψ : StateVector 8 6) (π : Equiv.Perm (Fin 8))
    (x : Config 4 6) : ℝ :=
  ∑ z : Config 4 6,
    basisProb (permuteState π ψ)
      (combineFirst (n := 8) (d := 6) 4 (by omega) x z)

/--
Every four-party computational-basis cylinder of an `AME(8,6)` state has probability `1/6^4`.
This is the exact quantum-to-classical diagonal bridge used by the support argument.
-/
theorem ame8_6_fourBlockMass_uniform
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (π : Equiv.Perm (Fin 8)) (x : Config 4 6) :
    fourBlockMass ψ π x = (1 : ℝ) / 1296 := by
  have hred := hψ.2 π
  rw [HasMaximallyMixedFirstReduction] at hred
  have hentry := congrArg (fun M => M x x) hred
  have hre := congrArg Complex.re hentry
  simpa [fourBlockMass, basisProb, reducedDensityFirst, maximallyMixed_apply,
    card_config, Complex.mul_conj] using hre

/-- Probability mass of a fixed two-symbol prefix, with the next two symbols and the final
four parties all summed out. -/
noncomputable def twoBlockMass (ψ : StateVector 8 6) (π : Equiv.Perm (Fin 8))
    (u : Config 2 6) : ℝ :=
  ∑ v : Config 2 6,
    fourBlockMass ψ π
      (combineFirst (n := 4) (d := 6) 2 (by omega) u v)

/-- Every two-party computational-basis cylinder of an `AME(8,6)` state has mass `1/6^2`. -/
theorem ame8_6_twoBlockMass_uniform
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (π : Equiv.Perm (Fin 8)) (u : Config 2 6) :
    twoBlockMass ψ π u = (1 : ℝ) / 36 := by
  rw [twoBlockMass]
  simp_rw [ame8_6_fourBlockMass_uniform ψ hψ π]
  rw [Finset.sum_const, card_config]
  norm_num

/--
Conditioning on the first two symbols of any permuted computational basis, the next two symbols
are exactly uniform.  This is the pairwise-uniform conditional-distribution bridge needed before
any finite support-profile certificate can be applied to `ExistsAME 8 6`.
-/
theorem ame8_6_conditional_nextTwo_uniform
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (π : Equiv.Perm (Fin 8)) (u v : Config 2 6) :
    fourBlockMass ψ π
        (combineFirst (n := 4) (d := 6) 2 (by omega) u v) /
      twoBlockMass ψ π u = (1 : ℝ) / 36 := by
  rw [ame8_6_fourBlockMass_uniform ψ hψ π,
      ame8_6_twoBlockMass_uniform ψ hψ π]
  norm_num

/-- The conditioning event in the previous theorem is nonzero. -/
theorem ame8_6_twoBlockMass_pos
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (π : Equiv.Perm (Fin 8)) (u : Config 2 6) :
    0 < twoBlockMass ψ π u := by
  rw [ame8_6_twoBlockMass_uniform ψ hψ π]
  norm_num

end D20Round20
