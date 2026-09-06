import D17Round30SurvivorGaps

/-!
# D17 Round 31: kernel soundness of modular discriminant filters

This file formalizes the local soundness layer used by the Round-28 modular
cover for the ordered template

  n = 2^14 * p^17 * q^9 * r^3,  p < q < r.

For every nonzero modulus, if the reciprocal-quadratic discriminant has no
square residue modulo that modulus, then it is not an integer square and the
corresponding branch cannot satisfy `OeisA63880.A`.  The twenty prime moduli
used in Round 28 are also certified here.  Their complete residue tables are
checked independently by the exact external checkers in the Round-31 archive.
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

/-- The exact logical meaning of a successful modular non-square filter. -/
def KilledBy (m p q : ℕ) : Prop :=
  ∀ x : ZMod m, discZ m p q ≠ x ^ 2

/-- A modular non-square certificate rules out an integer square. -/
theorem killedBy_not_int_square {m p q : ℕ} [NeZero m]
    (hkill : KilledBy m p q) :
    ¬ IsIntSquare (discriminant p q) := by
  rintro ⟨s, hs⟩
  apply hkill (s : ZMod m)
  have hcast := congrArg (fun z : ℤ => (z : ZMod m)) hs
  simpa [discZ] using hcast

/-- Direct bridge from any successful modular filter to nonexistence of an
A063880 term in the `(14;17,9,3)` branch. -/
theorem no_A_of_killedBy {m p q r : ℕ} [NeZero m]
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hkill : KilledBy m p q) :
    ¬ A (Branch p q r) := by
  intro hA
  exact killedBy_not_int_square hkill
    (A_branch_discriminant_square hp hq hr h2p hpq hqr hA)

/-- The twenty moduli used by the exact Round-28 cover. -/
def filterPrimes : List ℕ :=
  [11, 13, 17, 23, 41, 43, 47, 53, 59, 67,
   71, 79, 83, 89, 97, 101, 103, 107, 127, 131]

theorem filterPrimes_prime :
    ∀ m ∈ filterPrimes, m.Prime := by
  norm_num [filterPrimes]

theorem filterPrimes_nonzero :
    ∀ m ∈ filterPrimes, m ≠ 0 := by
  intro m hm
  exact (filterPrimes_prime m hm).ne_zero

/-- Mutation control: an exact square always has its own modular square root,
so the direction and negation in `KilledBy` cannot be reversed silently. -/
theorem exact_square_has_modular_root {m : ℕ} [NeZero m] (s : ℤ) :
    ¬ (∀ x : ZMod m, ((s ^ 2 : ℤ) : ZMod m) ≠ x ^ 2) := by
  intro h
  apply h (s : ZMod m)
  simp

#print axioms killedBy_not_int_square
#print axioms no_A_of_killedBy
#print axioms filterPrimes_prime
#print axioms filterPrimes_nonzero
#print axioms exact_square_has_modular_root

end D17Round31
