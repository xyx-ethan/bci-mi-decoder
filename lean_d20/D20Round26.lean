import D20Round25

/-!
# D20 Round 26: a 15-by-23 triple-incidence bound

This file isolates the robust double-counting component of the remaining support-48
`t = 11` analysis.  Fifteen incidence rows, each of total weight three, distribute
45 incidences over 23 light words.  Hence some light word has incidence degree at most one.
-/

open scoped BigOperators

namespace D20Round26

/-- Degree of a light word in an abstract family of fifteen triple-cell incidence rows. -/
def tripleDegree (I : Fin 15 → Fin 23 → ℕ) (x : Fin 23) : ℕ :=
  ∑ p : Fin 15, I p x

/-- If every one of fifteen incidence rows has total weight three, their total incidence is 45. -/
theorem sum_tripleDegree
    (I : Fin 15 → Fin 23 → ℕ)
    (hrow : ∀ p : Fin 15, ∑ x : Fin 23, I p x = 3) :
    ∑ x : Fin 23, tripleDegree I x = 45 := by
  unfold tripleDegree
  rw [Finset.sum_comm]
  simp_rw [hrow]
  norm_num

/-- Fifteen triples on 23 light words always admit a word lying in at most one triple. -/
theorem exists_tripleDegree_le_one
    (I : Fin 15 → Fin 23 → ℕ)
    (hrow : ∀ p : Fin 15, ∑ x : Fin 23, I p x = 3) :
    ∃ x : Fin 23, tripleDegree I x ≤ 1 := by
  by_contra h
  push Not at h
  have hdeg : ∀ x : Fin 23, 2 ≤ tripleDegree I x := by
    intro x
    omega
  have hlower : 46 ≤ ∑ x : Fin 23, tripleDegree I x := by
    calc
      46 = ∑ _x : Fin 23, (2 : ℕ) := by norm_num
      _ ≤ ∑ x : Fin 23, tripleDegree I x := by
        exact Finset.sum_le_sum fun x _hx => hdeg x
  have htotal := sum_tripleDegree I hrow
  omega

end D20Round26
