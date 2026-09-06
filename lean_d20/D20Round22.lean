import D20Round21

/-!
# D20 Round 22: minimal computational support is a graph

If an `AME(8,6)` state attains the Round-21 lower bound of 1296 nonzero computational-basis
amplitudes, then every four-symbol prefix has exactly one nonzero completion.  This is the
finite graph property underlying the usual minimal-support AME / orthogonal-array / MDS-code
correspondence, proved here directly from the pinned Formal Conjectures `IsAME` definition.
-/

open OpenQuantumProblem35
open D20Round20 D20Round21

namespace D20Round22

/-- At the minimal computational support size 1296, every four-symbol prefix has a unique
nonzero four-symbol completion. -/
theorem ame8_6_minSupport_unique_completion
    (ψ : StateVector 8 6) (hψ : IsAME ψ)
    (hcount : supportCount ψ = 1296)
    (x : Config 4 6) :
    ∃! z : Config 4 6,
      ψ (combineFirst (n := 8) (d := 6) 4 (by omega) x z) ≠ 0 := by
  classical
  choose z hz using fun u : Config 4 6 => ame8_6_fourPrefix_has_nonzero_completion ψ hψ u
  let f : Config 4 6 → {y : Config 8 6 // ψ y ≠ 0} := fun u =>
    ⟨combineFirst (n := 8) (d := 6) 4 (by omega) u (z u), hz u⟩
  have hinj : Function.Injective f := by
    intro u v huv
    apply funext
    intro i
    have hcoord := congrArg
      (fun q : {y : Config 8 6 // ψ y ≠ 0} =>
        q.1 (leftIndex (m := 4) (n := 8) (by omega) i)) huv
    simpa [f] using hcoord
  have hcard_dom : Fintype.card (Config 4 6) = 1296 := by
    calc
      Fintype.card (Config 4 6) = 6 ^ 4 := card_config 4 6
      _ = 1296 := by norm_num
  have hcard_cod : Fintype.card {y : Config 8 6 // ψ y ≠ 0} = 1296 := by
    simpa [supportCount] using hcount
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard_dom.trans hcard_cod.symm⟩
  refine ⟨z x, hz x, ?_⟩
  intro w hw
  let yw : {y : Config 8 6 // ψ y ≠ 0} :=
    ⟨combineFirst (n := 8) (d := 6) 4 (by omega) x w, hw⟩
  obtain ⟨u, hu⟩ := hbij.2 yw
  have hux : u = x := by
    apply funext
    intro i
    have hcoord := congrArg
      (fun q : {y : Config 8 6 // ψ y ≠ 0} =>
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
    (fun q : Config 8 6 => q (rightIndex (m := 4) (n := 8) (by omega) i)) hfull
  simpa using hcoord

end D20Round22
