import D17FiniteY

/-!
# D17 Round 24: bridge from the A063880 arithmetic equation to the ratio equation

The target branch is `n = 2^17 * x^4 * y^3 * z^3` with distinct odd prime
bases `x,y,z`.  This file first establishes the fixed prime-power closed
forms for ordinary and unitary divisor sums, then builds the multiplicative
bridge.
-/

namespace D17Round24

open scoped ArithmeticFunction.sigma
open OeisA63880

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Phi5N (t : ℕ) : ℕ := t^4 + t^3 + t^2 + t + 1

def Phi6N (t : ℕ) : ℕ := t^2 - t + 1

def BranchN (x y z : ℕ) : ℕ := 2^17 * x^4 * y^3 * z^3

theorem usigma_prime_pow_three {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 3) = 1 + p ^ 3 := by
  simp [usigma, unitaryDivisors, Nat.divisors_prime_pow hp, Finset.range_add_one,
    Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff, hp.ne_one]

theorem usigma_prime_pow_four {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 4) = 1 + p ^ 4 := by
  simp [usigma, unitaryDivisors, Nat.divisors_prime_pow hp, Finset.range_add_one,
    Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff, hp.ne_one]

theorem usigma_two_pow_seventeen :
    usigma (2 ^ 17) = 1 + 2 ^ 17 := by
  norm_num [usigma, unitaryDivisors]

theorem sigma_prime_pow_three {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ 3) = (p + 1) * (p^2 + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

theorem sigma_prime_pow_four {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ 4) = Phi5N p := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, Phi5N]
  ring

theorem sigma_two_pow_seventeen :
    ArithmeticFunction.sigma 1 (2 ^ 17) = 262143 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  norm_num [Finset.sum_range_succ]

end D17Round24
