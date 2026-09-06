import D17FiniteY

/-!
# D17 Round 24: bridge from the A063880 arithmetic equation to the ratio equation

First isolate the fixed prime-power unitary-divisor sums needed by the
`2^17 * x^4 * y^3 * z^3` branch.
-/

namespace D17Round24

open scoped ArithmeticFunction.sigma
open OeisA63880

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem usigma_prime_pow_three {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 3) = 1 + p ^ 3 := by
  simp [usigma, unitaryDivisors, Nat.divisors_prime_pow hp, Finset.range_succ, hp.ne_one]

theorem usigma_prime_pow_four {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 4) = 1 + p ^ 4 := by
  simp [usigma, unitaryDivisors, Nat.divisors_prime_pow hp, Finset.range_succ, hp.ne_one]

theorem usigma_two_pow_seventeen :
    usigma (2 ^ 17) = 1 + 2 ^ 17 := by
  simpa using usigma_prime_pow_three (p := 2) Nat.prime_two

end D17Round24
