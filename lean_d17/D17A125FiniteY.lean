import D17RatioBridge

/-!
# D17: a=125 direct ratio bridge and finite-minimum theorem

For the restricted A063880 branch

  n = 2^125 * x^4 * y^3 * z^3,

this file derives the exact rational ratio equation directly from
`OeisA63880.A`, without invoking either research-open theorem in the upstream
file. Under the middle-order chain `y < x < z`, it then proves the exact
finite bound `y < 2^126 + 1`.
-/

namespace D17A125

open scoped ArithmeticFunction.sigma
open OeisA63880
open D17Round24

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Branch125 (x y z : ℕ) : ℕ := 2^125 * x^4 * y^3 * z^3

def Target125 : ℚ :=
  85070591730234615865843651857942052866 /
    85070591730234615865843651857942052863

theorem sigma_two_pow_125 :
    ArithmeticFunction.sigma 1 (2 ^ 125) =
      85070591730234615865843651857942052863 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  norm_num [Finset.sum_range_succ]

theorem usigma_two_pow_125 :
    usigma (2 ^ 125) =
      42535295865117307932921825928971026433 := by
  simpa using (usigma_prime_pow Nat.prime_two (show (125 : ℕ) ≠ 0 by decide))

theorem branch125_coprimes {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z) :
    (2 ^ 125).Coprime (x ^ 4) ∧
      ((2 ^ 125) * x ^ 4).Coprime (y ^ 3) ∧
      (((2 ^ 125) * x ^ 4) * y ^ 3).Coprime (z ^ 3) := by
  have h2x : 2 ≠ x := by omega
  have h2z : 2 ≠ z := by omega
  have hxy : x ≠ y := by omega
  have hxz_ne : x ≠ z := by omega
  have hyz : y ≠ z := by omega
  have c2x : (2 ^ 125).Coprime (x ^ 4) :=
    Nat.coprime_pow_primes 125 4 Nat.prime_two hx h2x
  have c2y : (2 ^ 125).Coprime (y ^ 3) :=
    Nat.coprime_pow_primes 125 3 Nat.prime_two hy (by omega)
  have c2z : (2 ^ 125).Coprime (z ^ 3) :=
    Nat.coprime_pow_primes 125 3 Nat.prime_two hz h2z
  have cxy : (x ^ 4).Coprime (y ^ 3) :=
    Nat.coprime_pow_primes 4 3 hx hy hxy
  have cxz : (x ^ 4).Coprime (z ^ 3) :=
    Nat.coprime_pow_primes 4 3 hx hz hxz_ne
  have cyz : (y ^ 3).Coprime (z ^ 3) :=
    Nat.coprime_pow_primes 3 3 hy hz hyz
  refine ⟨c2x, Nat.Coprime.mul_left c2y cxy, ?_⟩
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_left c2z cxz) cyz

theorem sigma_branch125 {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z) :
    ArithmeticFunction.sigma 1 (Branch125 x y z) =
      85070591730234615865843651857942052863 * Phi5N x *
        ((y + 1) * (y ^ 2 + 1)) * ((z + 1) * (z ^ 2 + 1)) := by
  rcases branch125_coprimes hx hy hz h2y hyx hxz with ⟨c2x, cAxy, cAxyz⟩
  simp only [Branch125]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cAxyz,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cAxy,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime c2x,
    sigma_two_pow_125, sigma_prime_pow_four hx,
    sigma_prime_pow_three hy, sigma_prime_pow_three hz]

theorem usigma_branch125 {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z) :
    usigma (Branch125 x y z) =
      42535295865117307932921825928971026433 *
        (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3) := by
  rcases branch125_coprimes hx hy hz h2y hyx hxz with ⟨c2x, cAxy, cAxyz⟩
  have h20 : 2 ^ 125 ≠ 0 := by norm_num
  have hx40 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx.ne_zero
  have hy30 : y ^ 3 ≠ 0 := pow_ne_zero 3 hy.ne_zero
  have hz30 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz.ne_zero
  have h2x0 : (2 ^ 125) * x ^ 4 ≠ 0 := mul_ne_zero h20 hx40
  have h2xy0 : ((2 ^ 125) * x ^ 4) * y ^ 3 ≠ 0 := mul_ne_zero h2x0 hy30
  simp only [Branch125]
  rw [usigma_mul_of_coprime cAxyz h2xy0 hz30,
    usigma_mul_of_coprime cAxy h2x0 hy30,
    usigma_mul_of_coprime c2x h20 hx40,
    usigma_two_pow_125, usigma_prime_pow_four hx,
    usigma_prime_pow_three hy, usigma_prime_pow_three hz]

theorem A_branch125_uncancelled {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z)
    (hA : A (Branch125 x y z)) :
    85070591730234615865843651857942052863 * Phi5N x *
        ((y + 1) * (y ^ 2 + 1)) * ((z + 1) * (z ^ 2 + 1)) =
      85070591730234615865843651857942052866 *
        (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3) := by
  calc
    85070591730234615865843651857942052863 * Phi5N x *
        ((y + 1) * (y ^ 2 + 1)) * ((z + 1) * (z ^ 2 + 1)) =
        ArithmeticFunction.sigma 1 (Branch125 x y z) :=
      (sigma_branch125 hx hy hz h2y hyx hxz).symm
    _ = 2 * usigma (Branch125 x y z) := hA.2
    _ = 2 * (42535295865117307932921825928971026433 *
        (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3)) := by
      rw [usigma_branch125 hx hy hz h2y hyx hxz]
    _ = 85070591730234615865843651857942052866 *
        (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3) := by ring

theorem A_branch125_cross_rat {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z)
    (hA : A (Branch125 x y z)) :
    (85070591730234615865843651857942052863 : ℚ) *
        D17Round22.Phi5 (x : ℚ) * ((y : ℚ) ^ 2 + 1) * ((z : ℚ) ^ 2 + 1) =
      (85070591730234615865843651857942052866 : ℚ) *
        ((x : ℚ) ^ 4 + 1) * D17Round22.Phi6 (y : ℚ) *
        D17Round22.Phi6 (z : ℚ) := by
  have hnat := A_branch125_uncancelled hx hy hz h2y hyx hxz hA
  have hq :
      (85070591730234615865843651857942052863 : ℚ) * (Phi5N x : ℚ) *
          (((y : ℚ) + 1) * ((y : ℚ) ^ 2 + 1)) *
          (((z : ℚ) + 1) * ((z : ℚ) ^ 2 + 1)) =
        (85070591730234615865843651857942052866 : ℚ) *
          (1 + (x : ℚ) ^ 4) * (1 + (y : ℚ) ^ 3) *
          (1 + (z : ℚ) ^ 3) := by
    exact_mod_cast hnat
  have hxPhi : (Phi5N x : ℚ) = D17Round22.Phi5 (x : ℚ) := by
    norm_num [Phi5N, D17Round22.Phi5]
  rw [hxPhi] at hq
  have hyFactor : (1 : ℚ) + (y : ℚ) ^ 3 =
      ((y : ℚ) + 1) * D17Round22.Phi6 (y : ℚ) := by
    simp [D17Round22.Phi6]
    ring
  have hzFactor : (1 : ℚ) + (z : ℚ) ^ 3 =
      ((z : ℚ) + 1) * D17Round22.Phi6 (z : ℚ) := by
    simp [D17Round22.Phi6]
    ring
  let c : ℚ := ((y : ℚ) + 1) * ((z : ℚ) + 1)
  let lhs : ℚ :=
    (85070591730234615865843651857942052863 : ℚ) *
      D17Round22.Phi5 (x : ℚ) * ((y : ℚ) ^ 2 + 1) * ((z : ℚ) ^ 2 + 1)
  let rhs : ℚ :=
    (85070591730234615865843651857942052866 : ℚ) *
      ((x : ℚ) ^ 4 + 1) * D17Round22.Phi6 (y : ℚ) * D17Round22.Phi6 (z : ℚ)
  have hcommon : c * lhs = c * rhs := by
    dsimp [c, lhs, rhs]
    calc
      (((y : ℚ) + 1) * ((z : ℚ) + 1)) *
          ((85070591730234615865843651857942052863 : ℚ) *
            D17Round22.Phi5 (x : ℚ) * ((y : ℚ) ^ 2 + 1) *
            ((z : ℚ) ^ 2 + 1)) =
          (85070591730234615865843651857942052863 : ℚ) *
            D17Round22.Phi5 (x : ℚ) *
            (((y : ℚ) + 1) * ((y : ℚ) ^ 2 + 1)) *
            (((z : ℚ) + 1) * ((z : ℚ) ^ 2 + 1)) := by ring
      _ = (85070591730234615865843651857942052866 : ℚ) *
            (1 + (x : ℚ) ^ 4) * (1 + (y : ℚ) ^ 3) *
            (1 + (z : ℚ) ^ 3) := hq
      _ = (((y : ℚ) + 1) * ((z : ℚ) + 1)) *
          ((85070591730234615865843651857942052866 : ℚ) *
            ((x : ℚ) ^ 4 + 1) * D17Round22.Phi6 (y : ℚ) *
            D17Round22.Phi6 (z : ℚ)) := by
        rw [hyFactor, hzFactor]
        ring
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  exact mul_left_cancel₀ hc0 hcommon

theorem A_branch125_ratio {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z)
    (hA : A (Branch125 x y z)) :
    D17Round22.R4 (x : ℚ) * D17Round22.R3 (y : ℚ) *
        D17Round22.R3 (z : ℚ) = Target125 := by
  have hcross := A_branch125_cross_rat hx hy hz h2y hyx hxz hA
  have hyQ : (1 : ℚ) < y := by exact_mod_cast (show 1 < y by omega)
  have hzQ : (1 : ℚ) < z := by exact_mod_cast (show 1 < z by omega)
  have hdx : (x : ℚ) ^ 4 + 1 ≠ 0 := by positivity
  have hdy : D17Round22.Phi6 (y : ℚ) ≠ 0 := (D17Round22.phi6_pos hyQ).ne'
  have hdz : D17Round22.Phi6 (z : ℚ) ≠ 0 := (D17Round22.phi6_pos hzQ).ne'
  simp only [D17Round22.R4, D17Round22.R3, Target125]
  field_simp [hdx, hdy, hdz]
  ring_nf at hcross ⊢
  exact hcross

theorem ratio_product_lt_cube_125 {x y z : ℚ}
    (hy : 1 < y) (hyx : y ≤ x) (hyz : y ≤ z)
    (hEq : D17Round22.R4 x * D17Round22.R3 y *
      D17Round22.R3 z = Target125) :
    Target125 < D17Round22.U y ^ 3 := by
  have hx : 1 < x := lt_of_lt_of_le hy hyx
  have hz : 1 < z := lt_of_lt_of_le hy hyz
  have hUx : D17Round22.U x ≤ D17Round22.U y := D17Round22.U_antitone hy hyx
  have hUz : D17Round22.U z ≤ D17Round22.U y := D17Round22.U_antitone hy hyz
  have h4 : D17Round22.R4 x < D17Round22.U y :=
    lt_of_lt_of_le (D17Round22.R4_lt_U hx) hUx
  have h3y : D17Round22.R3 y < D17Round22.U y := D17Round22.R3_lt_U hy
  have h3z : D17Round22.R3 z < D17Round22.U y :=
    lt_of_lt_of_le (D17Round22.R3_lt_U hz) hUz
  have hUp : 0 ≤ D17Round22.U y := le_of_lt (D17Round22.U_pos hy)
  have h12 : D17Round22.R4 x * D17Round22.R3 y <
      D17Round22.U y * D17Round22.U y := by
    exact mul_lt_mul h4 (le_of_lt h3y) (D17Round22.R3_pos hy) hUp
  have hUU : 0 ≤ D17Round22.U y * D17Round22.U y := mul_nonneg hUp hUp
  have h123 : (D17Round22.R4 x * D17Round22.R3 y) *
      D17Round22.R3 z <
      (D17Round22.U y * D17Round22.U y) * D17Round22.U y := by
    exact mul_lt_mul h12 (le_of_lt h3z) (D17Round22.R3_pos hz) hUU
  calc
    Target125 = (D17Round22.R4 x * D17Round22.R3 y) *
        D17Round22.R3 z := by simpa [mul_assoc] using hEq.symm
    _ < (D17Round22.U y * D17Round22.U y) * D17Round22.U y := h123
    _ = D17Round22.U y ^ 3 := by ring

theorem boundary_cube_125 :
    D17Round22.U (85070591730234615865843651857942052865 : ℚ) ^ 3 <
      Target125 := by
  norm_num [D17Round22.U, Target125]

theorem finite_y_bound_125 {x y z : ℚ}
    (hy : 1 < y) (hyx : y ≤ x) (hyz : y ≤ z)
    (hEq : D17Round22.R4 x * D17Round22.R3 y *
      D17Round22.R3 z = Target125) :
    y < 85070591730234615865843651857942052865 := by
  have hprod : Target125 < D17Round22.U y ^ 3 :=
    ratio_product_lt_cube_125 hy hyx hyz hEq
  by_contra hnot
  have hcy : (85070591730234615865843651857942052865 : ℚ) ≤ y :=
    le_of_not_gt hnot
  have hU : D17Round22.U y ≤
      D17Round22.U (85070591730234615865843651857942052865 : ℚ) :=
    D17Round22.U_antitone (by norm_num) hcy
  have hcube : D17Round22.U y ^ 3 ≤
      D17Round22.U (85070591730234615865843651857942052865 : ℚ) ^ 3 := by
    exact pow_le_pow_left₀ (le_of_lt (D17Round22.U_pos hy)) hU 3
  have hb := boundary_cube_125
  linarith

theorem A_branch125_finite_y {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyx : y < x) (hxz : x < z)
    (hA : A (Branch125 x y z)) :
    y < 85070591730234615865843651857942052865 := by
  have hratio := A_branch125_ratio hx hy hz h2y hyx hxz hA
  have hyQ : (1 : ℚ) < y := by exact_mod_cast (show 1 < y by omega)
  have hyxQ : (y : ℚ) ≤ x := by exact_mod_cast hyx.le
  have hyzQ : (y : ℚ) ≤ z := by exact_mod_cast (hyx.trans hxz).le
  have hQ := finite_y_bound_125 hyQ hyxQ hyzQ hratio
  exact_mod_cast hQ

#print axioms sigma_two_pow_125
#print axioms usigma_two_pow_125
#print axioms A_branch125_cross_rat
#print axioms A_branch125_ratio
#print axioms boundary_cube_125
#print axioms A_branch125_finite_y

end D17A125
