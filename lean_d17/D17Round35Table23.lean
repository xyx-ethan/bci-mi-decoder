import D17Round34Table17

/-!
# D17 Round 35: complete modulus-23 table in the Lean kernel

This file extends the executable modular-filter layer by checking all
`23 × 23` residue pairs for the fourth modulus in the Round-28 cover.
The full row-major Boolean table and its killed count are reduced by ordinary
kernel computation only.
-/

namespace D17Round35

open OeisA63880
open D17Round29
open D17Round30
open D17Round31
open D17Round32
open D17Round33
open D17Round34

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Complete row-major table for modulus 23. This theorem checks all 529
ordered residue pairs in the kernel, not merely their total cardinality. -/
theorem killedTableB_23 : killedTableB 23 =
[
    false, false, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false, false, false, true, false, false,
    false, false, false, true, false, false, false, true, true, false, true, false, false, true, false, false, true, true, false, true, false, false, false,
    true, false, false, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false,
    false, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false, false, true, false, true, true, false,
    false, false, true, false, false, false, false, true, false, true, true, false, true, false, false, false, false, false, true, false, false, false, false,
    false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false,
    false, false, true, false, false, false, false, true, false, true, true, false, true, false, false, false, false, false, true, false, false, false, false,
    false, false, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, false,
    false, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false, false, true, false, true, true, false,
    false, false, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, false,
    false, false, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, false,
    true, true, false, true, true, false, true, false, true, true, false, false, false, true, false, true, true, true, true, true, true, false, false,
    true, false, false, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false,
    false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false,
    false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false,
    false, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, true, true, true, false, false, false,
    false, true, false, false, true, false, true, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false,
    false, true, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false, false,
    false, false, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, false,
    false, true, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false, false,
    false, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, true, true, true, false, false, false,
    true, true, false, true, true, false, true, false, true, true, false, false, false, true, false, true, true, true, true, true, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false
] := by
  decide

/-- The modulus-23 table has 222 killed and 307 allowed cells. -/
theorem killedCountB_23 : killedCountB 23 = 222 := by
  decide

/-- Positive table control. -/
theorem killedByB_23_0_2 : killedByB 23 0 2 = true := by
  decide

/-- Negative table control. -/
theorem killedByB_23_0_0 : killedByB 23 0 0 = false := by
  decide

/-- Mutation control: the killed count is not the complementary count. -/
theorem killedCountB_23_not_complement : killedCountB 23 ≠ 307 := by
  rw [killedCountB_23]
  decide

#print axioms killedTableB_23
#print axioms killedCountB_23
#print axioms killedByB_23_0_2
#print axioms killedByB_23_0_0
#print axioms killedCountB_23_not_complement

end D17Round35
