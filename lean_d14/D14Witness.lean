/-
D14 Round 11: explicit odd witness for OeisA51903.conjecture3.
No declaration below uses the open conjecture itself.
-/
import Mathlib
import FormalConjectures.OEIS.51903

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace D14Round11
open OeisA51903

def N : ℕ := 348634396442820771857

theorem primeFactorsList_from_certificate {n : ℕ} {l : List ℕ}
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, Nat.Prime p)
    (hsorted : l.Pairwise (· ≤ ·)) : n.primeFactorsList = l := by
  exact ((Nat.primeFactorsList_unique hprod hprime).eq_of_pairwise'
    hsorted (Nat.primeFactorsList_sorted _).pairwise).symm

theorem maximumExponent_from_factorList {n : ℕ} {l : List ℕ}
    (h : n.primeFactorsList = l) :
    a n = (l.map (fun p => l.count p)).foldr max 0 := by
  simp only [OeisA51903.a, h]

theorem factorList_N :
    N.primeFactorsList = [7,31,73,79,89,271,937,3511,3511] := by
  apply primeFactorsList_from_certificate
  · norm_num [N, List.prod_cons, List.prod_nil]
  · intro p hp
    simp only [List.mem_cons, List.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · decide

theorem a_N : a N = 2 := by
  calc
    a N = (([7,31,73,79,89,271,937,3511,3511] : List ℕ).map
      (fun p => ([7,31,73,79,89,271,937,3511,3511] : List ℕ).count p)).foldr max 0 :=
        maximumExponent_from_factorList factorList_N
    _ = 2 := by decide

theorem odd_N : Odd N := by
  refine ⟨174317198221410385928, ?_⟩
  norm_num [N]

theorem mul_mod_certificate {m b e f r s t : ℕ}
    (he : b ^ e % m = r) (hf : b ^ f % m = s)
    (hprod : (r * s) % m = t) : b ^ (e + f) % m = t := by
  rw [pow_add, Nat.mul_mod, he, hf]
  exact hprod

theorem congruence_from_period {b m L k E : ℕ}
    (hL : b ^ L ≡ 1 [MOD m]) : b ^ (L * k + E) ≡ b ^ E [MOD m] := by
  have hk := hL.pow k
  have he := hk.mul (Nat.ModEq.refl (b ^ E))
  simpa only [pow_add, pow_mul, one_pow, one_mul] using he

theorem period_remainder : (2 : ℕ) ^ 19305 % N = 1 := by
  have h0 : (2 : ℕ) ^ 1 % N = 2 := by norm_num [N]
  have h1 : (2 : ℕ) ^ 2 % N = 4 := by
    exact mul_mod_certificate h0 h0 (by norm_num [N])
  have h2 : (2 : ℕ) ^ 4 % N = 16 := by
    exact mul_mod_certificate h1 h1 (by norm_num [N])
  have h3 : (2 : ℕ) ^ 8 % N = 256 := by
    exact mul_mod_certificate h2 h2 (by norm_num [N])
  have h4 : (2 : ℕ) ^ 9 % N = 512 := by
    exact mul_mod_certificate h3 h0 (by norm_num [N])
  have h5 : (2 : ℕ) ^ 18 % N = 262144 := by
    exact mul_mod_certificate h4 h4 (by norm_num [N])
  have h6 : (2 : ℕ) ^ 36 % N = 68719476736 := by
    exact mul_mod_certificate h5 h5 (by norm_num [N])
  have h7 : (2 : ℕ) ^ 37 % N = 137438953472 := by
    exact mul_mod_certificate h6 h0 (by norm_num [N])
  have h8 : (2 : ℕ) ^ 74 % N = 63208523566259174506 := by
    exact mul_mod_certificate h7 h7 (by norm_num [N])
  have h9 : (2 : ℕ) ^ 75 % N = 126417047132518349012 := by
    exact mul_mod_certificate h8 h0 (by norm_num [N])
  have h10 : (2 : ℕ) ^ 150 % N = 288579228995573438994 := by
    exact mul_mod_certificate h9 h9 (by norm_num [N])
  have h11 : (2 : ℕ) ^ 300 % N = 103240986426981408776 := by
    exact mul_mod_certificate h10 h10 (by norm_num [N])
  have h12 : (2 : ℕ) ^ 301 % N = 206481972853962817552 := by
    exact mul_mod_certificate h11 h0 (by norm_num [N])
  have h13 : (2 : ℕ) ^ 602 % N = 155587830862772300402 := by
    exact mul_mod_certificate h12 h12 (by norm_num [N])
  have h14 : (2 : ℕ) ^ 603 % N = 311175661725544600804 := by
    exact mul_mod_certificate h13 h0 (by norm_num [N])
  have h15 : (2 : ℕ) ^ 1206 % N = 268085361059503476119 := by
    exact mul_mod_certificate h14 h14 (by norm_num [N])
  have h16 : (2 : ℕ) ^ 2412 % N = 13920523456345416702 := by
    exact mul_mod_certificate h15 h15 (by norm_num [N])
  have h17 : (2 : ℕ) ^ 2413 % N = 27841046912690833404 := by
    exact mul_mod_certificate h16 h0 (by norm_num [N])
  have h18 : (2 : ℕ) ^ 4826 % N = 46011531192491994063 := by
    exact mul_mod_certificate h17 h17 (by norm_num [N])
  have h19 : (2 : ℕ) ^ 9652 % N = 244977283311463632330 := by
    exact mul_mod_certificate h18 h18 (by norm_num [N])
  have h20 : (2 : ℕ) ^ 19304 % N = 174317198221410385929 := by
    exact mul_mod_certificate h19 h19 (by norm_num [N])
  have h21 : (2 : ℕ) ^ 19305 % N = 1 := by
    exact mul_mod_certificate h20 h0 (by norm_num [N])
  exact h21

theorem exponent_decomposition :
    N = 19305 * 18059279795017911 + 2 := by
  norm_num [N]

theorem powerN_congruence : (2 : ℕ) ^ N ≡ 2 ^ 2 [MOD N] := by
  have hL : (2 : ℕ) ^ 19305 ≡ 1 [MOD N] := by
    change (2 : ℕ) ^ 19305 % N = 1 % N
    rw [period_remainder]
    norm_num [N]
  have h := congruence_from_period (k := 18059279795017911) (E := 2) hL
  rwa [← exponent_decomposition] at h

theorem witness_congruence : (2 : ℕ) ^ N ≡ 2 ^ (a N) [MOD N] := by
  rw [a_N]
  exact powerN_congruence

theorem exists_odd_witness :
    ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  refine ⟨N, odd_N, ?_, witness_congruence⟩
  rw [a_N]
  decide

/-- The ordinary mathematical content of `OeisA51903.conjecture3` with the answer fixed to true. -/
theorem conjecture3_true_iff :
    True ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  constructor
  · intro _
    exact exists_odd_witness
  · intro _
    trivial

end D14Round11
