import D17Round33Table13

/-!
# D17 Round 34: complete modulus-17 table in the Lean kernel

This file extends the executable modular-filter layer by checking all
`17 × 17` residue pairs for the third modulus in the Round-28 cover.
The full row-major Boolean table and its killed count are reduced by ordinary
kernel computation only.
-/

namespace D17Round34

open OeisA63880
open D17Round29
open D17Round30
open D17Round31
open D17Round32
open D17Round33

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Complete row-major table for modulus 17. This theorem checks all 289
ordered residue pairs in the kernel, not merely their total cardinality. -/
theorem killedTableB_17 : killedTableB 17 =
[
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    true, false, true, false, true, true, false, true, true, true, true, false, true, true, false, true, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false,
    false, false, false, false, false, true, false, true, false, false, false, true, false, false, true, false, false
] := by
  decide

/-- The modulus-17 table has 71 killed and 218 allowed cells. -/
theorem killedCountB_17 : killedCountB 17 = 71 := by
  decide

/-- Positive table control. -/
theorem killedByB_17_0_5 : killedByB 17 0 5 = true := by
  decide

/-- Negative table control. -/
theorem killedByB_17_0_0 : killedByB 17 0 0 = false := by
  decide

/-- Mutation control: the killed count is not the complementary count. -/
theorem killedCountB_17_not_complement : killedCountB 17 ≠ 218 := by
  rw [killedCountB_17]
  decide

#print axioms killedTableB_17
#print axioms killedCountB_17
#print axioms killedByB_17_0_5
#print axioms killedByB_17_0_0
#print axioms killedCountB_17_not_complement

end D17Round34
