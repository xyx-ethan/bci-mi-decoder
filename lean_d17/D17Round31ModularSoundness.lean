import D17Round30SurvivorGaps

/-!
# D17 Round 31: kernel soundness of all modular discriminant filters

This file formalizes the local soundness layer used by the Round-28 modular
cover for the ordered template

  n = 2^14 * p^17 * q^9 * r^3,  p < q < r.

For every nonzero modulus, a Boolean check that the reciprocal-quadratic
discriminant has no square residue modulo that modulus is proved to rule out
an integer square, and hence to rule out `OeisA63880.A` for the branch.
The twenty moduli used in Round 28 are reconstructed in the kernel and their
complete residue-table cardinalities are checked exactly.
-/

namespace D17Round31

open OeisA63880
open D17Round29
open D17Round30

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The exact discriminant reduced to `ZMod m`. -/
def discZ (m p q : ℕ) : ZMod m :=
  (discriminant p q : ZMod m)

/-- Executable modular non-square filter.  The finite universal quantifier is
spelled out explicitly, so no noncomputable existential decision procedure is
used. -/
def killedBy (m : ℕ) [NeZero m] (p q : ℕ) : Bool :=
  (Finset.univ : Finset (ZMod m)).toList.all fun x =>
    decide (discZ m p q ≠ x ^ 2)

theorem killedBy_iff (m : ℕ) [NeZero m] (p q : ℕ) :
    killedBy m p q = true ↔
      ∀ x : ZMod m, discZ m p q ≠ x ^ 2 := by
  simp [killedBy]

/-- A modular non-square certificate rules out an integer square. -/
theorem killedBy_not_int_square {m p q : ℕ} [NeZero m]
    (hkill : killedBy m p q = true) :
    ¬ IsIntSquare (discriminant p q) := by
  have hmod : ∀ x : ZMod m, discZ m p q ≠ x ^ 2 :=
    (killedBy_iff m p q).mp hkill
  rintro ⟨s, hs⟩
  apply hmod (s : ZMod m)
  have hcast := congrArg (fun z : ℤ => (z : ZMod m)) hs
  simpa [discZ] using hcast

/-- Direct bridge from any successful modular filter to nonexistence of an
A063880 term in the `(14;17,9,3)` branch. -/
theorem no_A_of_killedBy {m p q r : ℕ} [NeZero m]
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hkill : killedBy m p q = true) :
    ¬ A (Branch p q r) := by
  intro hA
  exact killedBy_not_int_square hkill
    (A_branch_discriminant_square hp hq hr h2p hpq hqr hA)

/-- Complete residue-table cardinality for a modulus. -/
def killedCount (m : ℕ) [NeZero m] : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin m)).filter
    (fun pq => killedBy m pq.1.val pq.2.val = true)).card

/-- The twenty moduli used by the exact Round-28 cover. -/
def filterPrimes : List ℕ :=
  [11, 13, 17, 23, 41, 43, 47, 53, 59, 67,
   71, 79, 83, 89, 97, 101, 103, 107, 127, 131]

theorem filterPrimes_prime :
    ∀ m ∈ filterPrimes, m.Prime := by
  norm_num [filterPrimes]

theorem killedCount_11 : killedCount 11 = 82 := by decide
theorem killedCount_13 : killedCount 13 = 41 := by decide
theorem killedCount_17 : killedCount 17 = 71 := by decide
theorem killedCount_23 : killedCount 23 = 222 := by decide
theorem killedCount_41 : killedCount 41 = 907 := by decide
theorem killedCount_43 : killedCount 43 = 760 := by decide
theorem killedCount_47 : killedCount 47 = 913 := by decide
theorem killedCount_53 : killedCount 53 = 1272 := by decide
theorem killedCount_59 : killedCount 59 = 1508 := by decide
theorem killedCount_67 : killedCount 67 = 2068 := by decide
theorem killedCount_71 : killedCount 71 = 2715 := by decide
theorem killedCount_79 : killedCount 79 = 3062 := by decide
theorem killedCount_83 : killedCount 83 = 2976 := by decide
theorem killedCount_89 : killedCount 89 = 3707 := by decide
theorem killedCount_97 : killedCount 97 = 4247 := by decide
theorem killedCount_101 : killedCount 101 = 5132 := by decide
theorem killedCount_103 : killedCount 103 = 5784 := by decide
theorem killedCount_107 : killedCount 107 = 5259 := by decide
theorem killedCount_127 : killedCount 127 = 7265 := by decide
theorem killedCount_131 : killedCount 131 = 8719 := by decide

/-- Compact exact audit of all twenty complete residue tables. -/
theorem all_filter_counts :
    [killedCount 11, killedCount 13, killedCount 17, killedCount 23,
     killedCount 41, killedCount 43, killedCount 47, killedCount 53,
     killedCount 59, killedCount 67, killedCount 71, killedCount 79,
     killedCount 83, killedCount 89, killedCount 97, killedCount 101,
     killedCount 103, killedCount 107, killedCount 127, killedCount 131] =
    [82, 41, 71, 222, 907, 760, 913, 1272, 1508, 2068,
     2715, 3062, 2976, 3707, 4247, 5132, 5784, 5259, 7265, 8719] := by
  rw [killedCount_11, killedCount_13, killedCount_17, killedCount_23,
    killedCount_41, killedCount_43, killedCount_47, killedCount_53,
    killedCount_59, killedCount_67, killedCount_71, killedCount_79,
    killedCount_83, killedCount_89, killedCount_97, killedCount_101,
    killedCount_103, killedCount_107, killedCount_127, killedCount_131]

/-- Mutation control: the first table is not the accidental complement. -/
theorem first_filter_not_complement : killedCount 11 ≠ 39 := by
  rw [killedCount_11]
  decide

#print axioms killedBy_not_int_square
#print axioms no_A_of_killedBy
#print axioms filterPrimes_prime
#print axioms all_filter_counts
#print axioms first_filter_not_complement

end D17Round31
