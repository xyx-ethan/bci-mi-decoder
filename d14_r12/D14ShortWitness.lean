/- D14 exact odd witness. See the accompanying CI evidence for verification status.
Imports and uses the original upstream definition, without redefining it.
-/
import FormalConjectures.OEIS.«51903»

/-! An exact odd nonsquarefree witness using the upstream maximum multiplicity. -/

namespace D14.R5
open OeisA51903

theorem short_answer :
    True ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  constructor
  · intro _
    let N : ℕ := 348634396442820771857
    have hprod : ([7, 31, 73, 79, 89, 271, 937, 3511, 3511] : List ℕ).prod = N := by
      norm_num [N, List.prod_cons, List.prod_nil]
    have hp : ∀ p ∈ ([7, 31, 73, 79, 89, 271, 937, 3511, 3511] : List ℕ), Nat.Prime p := by
      intro p h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num
    have hs : ([7, 31, 73, 79, 89, 271, 937, 3511, 3511] : List ℕ).Pairwise (· ≤ ·) := by
      decide
    have hf : N.primeFactorsList = [7, 31, 73, 79, 89, 271, 937, 3511, 3511] :=
      ((Nat.primeFactorsList_unique hprod hp).eq_of_pairwise'
        hs (Nat.primeFactorsList_sorted N).pairwise).symm
    have ha : a N = 2 := by
      unfold a
      rw [hf]
      decide
    refine ⟨N, ?_, ?_, ?_⟩
    · exact ⟨174317198221410385928, by norm_num [N]⟩
    · rw [ha]
      decide
    · rw [ha]
      have hperiod : (2 : ZMod N) ^ 19305 = 1 := by
        change (2 : ZMod 348634396442820771857) ^ 19305 = 1
        reduce_mod_char
      have hn : 19305 * 18059279795017911 + 2 = N := by norm_num [N]
      have hz : (2 : ZMod N) ^ N = 2 ^ 2 := by
        have h : (2 : ZMod N) ^ (19305 * 18059279795017911 + 2) = 2 ^ 2 := by
          rw [pow_add, pow_mul, hperiod, one_pow, one_mul]
        rw [hn] at h
        exact h
      apply (ZMod.natCast_eq_natCast_iff (2 ^ N) (2 ^ 2) N).mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hz
  · intro _
    trivial

theorem exists_odd_witness :
    ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] :=
  short_answer.mp True.intro

end D14.R5

#print axioms D14.R5.short_answer
#print axioms D14.R5.exists_odd_witness
