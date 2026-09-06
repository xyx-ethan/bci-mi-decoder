import D20Round22

/-!
# D20 Round 23: permutation-covariant minimal-support graph property

This file proves that computational-basis support cardinality is invariant under party
permutations and upgrades Round 22's fixed-cut unique-completion theorem to every permuted
4|4 cut.  The result still concerns the computational basis; it does not assert invariance
under arbitrary local basis changes.
-/

open OpenQuantumProblem35
open D20Round20 D20Round21 D20Round22

namespace D20Round23

/-- Applying a party permutation and then its inverse recovers a configuration. -/
theorem permuteConfig_symm_left
    (π : Equiv.Perm (Fin 8)) (x : Config 8 6) :
    permuteConfig π (permuteConfig π.symm x) = x := by
  ext i
  simp [permuteConfig]

/-- Applying the inverse permutation and then the permutation also recovers a configuration. -/
theorem permuteConfig_symm_right
    (π : Equiv.Perm (Fin 8)) (x : Config 8 6) :
    permuteConfig π.symm (permuteConfig π x) = x := by
  ext i
  simp [permuteConfig]

/-- Party permutation induces an equivalence between the nonzero supports before and after
permuting the state. -/
noncomputable def supportPermEquiv
    (ψ : StateVector 8 6) (π : Equiv.Perm (Fin 8)) :
    {x : Config 8 6 // permuteState π ψ x ≠ 0} ≃
      {x : Config 8 6 // ψ x ≠ 0} where
  toFun x := ⟨permuteConfig π x.1, by
    simpa using x.2⟩
  invFun y := ⟨permuteConfig π.symm y.1, by
    rw [permuteState_apply, permuteConfig_symm_left]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact permuteConfig_symm_right π x.1
  right_inv y := by
    apply Subtype.ext
    exact permuteConfig_symm_left π y.1

/-- Computational-basis support size is invariant under party permutations. -/
theorem supportCount_permuteState
    (ψ : StateVector 8 6) (π : Equiv.Perm (Fin 8)) :
    supportCount (permuteState π ψ) = supportCount ψ := by
  unfold supportCount
  exact Fintype.card_congr (supportPermEquiv ψ π)

/-- For every party permutation and every four-symbol prefix in that permuted ordering,
there is a nonzero completion. -/
theorem ame8_6_fourPrefix_has_nonzero_completion_perm
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (π : Equiv.Perm (Fin 8)) (x : Config 4 6) :
    ∃ z : Config 4 6,
      permuteState π ψ
        (combineFirst (n := 8) (d := 6) 4 (by omega) x z) ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : fourBlockMass ψ π x = 0 := by
    rw [fourBlockMass]
    apply Finset.sum_eq_zero
    intro z hz
    unfold basisProb
    rw [h z]
    simp
  have hunif := ame8_6_fourBlockMass_uniform ψ hψ π x
  rw [hzero] at hunif
  norm_num at hunif

/-- If an `AME(8,6)` state has the minimal computational support size `1296`, then after any
party permutation every four-symbol prefix has exactly one nonzero four-symbol completion. -/
theorem ame8_6_minSupport_unique_completion_perm
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (π : Equiv.Perm (Fin 8)) (x : Config 4 6) :
    ∃! z : Config 4 6,
      permuteState π ψ
        (combineFirst (n := 8) (d := 6) 4 (by omega) x z) ≠ 0 := by
  classical
  let φ : StateVector 8 6 := permuteState π ψ
  choose z hz using fun u : Config 4 6 =>
    ame8_6_fourPrefix_has_nonzero_completion_perm ψ hψ π u
  let f : Config 4 6 → {y : Config 8 6 // φ y ≠ 0} := fun u =>
    ⟨combineFirst (n := 8) (d := 6) 4 (by omega) u (z u), by
      simpa [φ] using hz u⟩
  have hinj : Function.Injective f := by
    intro u v huv
    apply funext
    intro i
    have hcoord := congrArg
      (fun q : {y : Config 8 6 // φ y ≠ 0} =>
        q.1 (leftIndex (m := 4) (n := 8) (by omega) i)) huv
    simpa [f] using hcoord
  have hcard_dom : Fintype.card (Config 4 6) = 1296 := by
    calc
      Fintype.card (Config 4 6) = 6 ^ 4 := card_config 4 6
      _ = 1296 := by norm_num
  have hφcount : supportCount φ = 1296 := by
    calc
      supportCount φ = supportCount ψ := by
        simpa [φ] using supportCount_permuteState ψ π
      _ = 1296 := hcount
  have hcard_cod : Fintype.card {y : Config 8 6 // φ y ≠ 0} = 1296 := by
    simpa [supportCount] using hφcount
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hinj, hcard_dom.trans hcard_cod.symm⟩
  refine ⟨z x, by simpa [φ] using hz x, ?_⟩
  intro w hw
  let yw : {y : Config 8 6 // φ y ≠ 0} :=
    ⟨combineFirst (n := 8) (d := 6) 4 (by omega) x w, by
      simpa [φ] using hw⟩
  obtain ⟨u, hu⟩ := hbij.2 yw
  have hux : u = x := by
    apply funext
    intro i
    have hcoord := congrArg
      (fun q : {y : Config 8 6 // φ y ≠ 0} =>
        q.1 (leftIndex (m := 4) (n := 8) (by omega) i)) hu
    simpa [f, yw] using hcoord
  subst u
  have hfull :
      combineFirst (n := 8) (d := 6) 4 (by omega) x (z x) =
        combineFirst (n := 8) (d := 6) 4 (by omega) x w := by
    exact congrArg Subtype.val hu
  apply funext
  intro i
  have hcoord := congrArg
    (fun q : Config 8 6 =>
      q (rightIndex (m := 4) (n := 8) (by omega) i)) hfull
  simpa using hcoord.symm

end D20Round23
