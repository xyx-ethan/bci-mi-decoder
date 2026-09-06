import D17Round32FirstTable

/-!
# D17 Round 33: complete modulus-13 table in the Lean kernel

This file extends the Round-32 executable modular-filter layer by checking
all `13 × 13` residue pairs for the second modulus in the Round-28 cover.
The full row-major Boolean table and its killed count are reduced by the
Lean kernel; no `native_decide` or compiler-trust mechanism is used.
-/

namespace D17Round33

open OeisA63880
open D17Round29
open D17Round30
open D17Round31
open D17Round32

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Complete row-major table for modulus 13. This theorem checks all 169
ordered residue pairs in the kernel, not merely their total cardinality. -/
theorem killedTableB_13 : killedTableB 13 =
    [false, true, true, false, false, false, false, true, false, false, false, false, false,
     true, true, false, true, false, true, false, false, true, true, false, false, false,
     true, true, false, true, false, true, false, false, true, true, false, false, false,
     false, false, false, false, false, false, false, false, false, false, false, false, false,
     false, false, false, false, false, false, false, false, false, false, false, false, false,
     false, true, true, false, false, false, false, true, false, false, false, false, false,
     false, true, true, true, false, false, true, true, false, true, false, true, false,
     true, true, false, true, false, true, false, false, true, true, false, false, false,
     false, true, true, false, false, false, false, true, false, false, false, false, false,
     false, false, false, false, false, false, false, false, false, false, false, false, false,
     false, false, false, false, false, false, false, false, false, false, false, false, false,
     false, true, true, true, false, false, true, true, false, true, false, true, false,
     false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  decide

/-- The modulus-13 table has 41 killed and 128 allowed cells. -/
theorem killedCountB_13 : killedCountB 13 = 41 := by
  decide

/-- Positive table control. -/
theorem killedByB_13_0_1 : killedByB 13 0 1 = true := by
  decide

/-- Negative table control. -/
theorem killedByB_13_0_0 : killedByB 13 0 0 = false := by
  decide

/-- Mutation control: the killed count is not the complementary count. -/
theorem killedCountB_13_not_complement : killedCountB 13 ≠ 128 := by
  rw [killedCountB_13]
  decide

#print axioms killedTableB_13
#print axioms killedCountB_13
#print axioms killedByB_13_0_1
#print axioms killedByB_13_0_0
#print axioms killedCountB_13_not_complement

end D17Round33
