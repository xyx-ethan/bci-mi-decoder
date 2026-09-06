import D17Round31ModularSoundness

/-!
# D17 Round 32: first complete modular table in the Lean kernel

This file turns the Round-31 logical modular-filter bridge into an executable,
kernel-reducible Boolean checker.  It then checks the complete `11 × 11`
residue table used by the Round-28 cover and proves that exactly 82 residue
pairs are killed.
-/

namespace D17Round32

open OeisA63880
open D17Round29
open D17Round30
open D17Round31

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Executable finite search for absence of a square root modulo `m`. -/
def killedByB (m : ℕ) [NeZero m] (p q : ℕ) : Bool :=
  (List.range m).all fun x =>
    decide (discZ m p q ≠ (x : ZMod m) ^ 2)

/-- The executable checker implies the logical `KilledBy` predicate. -/
theorem killedByB_sound (m : ℕ) [NeZero m] (p q : ℕ)
    (hkill : killedByB m p q = true) :
    KilledBy m p q := by
  intro x
  unfold killedByB at hkill
  rw [List.all_eq_true] at hkill
  have hx := hkill x.val (by simpa using ZMod.val_lt x)
  simpa [ZMod.natCast_zmod_val] using hx

/-- Any successful executable modular filter rules out the original A063880
branch directly. -/
theorem no_A_of_killedByB {m p q r : ℕ} [NeZero m]
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hkill : killedByB m p q = true) :
    ¬ A (Branch p q r) :=
  no_A_of_killedBy hp hq hr h2p hpq hqr
    (killedByB_sound m p q hkill)

/-- Convert a Boolean table entry to its counting weight. -/
def boolWeight : Bool → ℕ
  | false => 0
  | true => 1

/-- Number of killed ordered residue pairs modulo `m`. -/
def killedCountB (m : ℕ) [NeZero m] : ℕ :=
  (List.range m).foldl
    (fun total p =>
      total + (List.range m).foldl
        (fun subtotal q => subtotal + boolWeight (killedByB m p q)) 0) 0

/-- The first complete filter table: 82 of the 121 ordered residue pairs
modulo 11 have non-square discriminant. -/
theorem killedCountB_11 : killedCountB 11 = 82 := by
  decide

/-- Positive table control. -/
theorem killedByB_11_0_2 : killedByB 11 0 2 = true := by
  decide

/-- Negative table control. -/
theorem killedByB_11_0_0 : killedByB 11 0 0 = false := by
  decide

/-- Mutation control: the killed count is not the complementary count. -/
theorem killedCountB_11_not_complement : killedCountB 11 ≠ 39 := by
  rw [killedCountB_11]
  decide

#print axioms killedByB_sound
#print axioms no_A_of_killedByB
#print axioms killedCountB_11
#print axioms killedByB_11_0_2
#print axioms killedByB_11_0_0
#print axioms killedCountB_11_not_complement

end D17Round32
