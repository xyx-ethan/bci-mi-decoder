import D17FiniteY

/-!
# D17 Round 24: bridge from the A063880 arithmetic equation to the ratio equation

The target branch is `n = 2^17 * x^4 * y^3 * z^3` with distinct odd prime
bases `x,y,z`.  This file proves symbolic prime-power and coprime-product
formulas for ordinary and unitary divisor sums, then derives the exact
ratio equation used by Round 23 directly from `OeisA63880.A`.
-/

namespace D17Round24

open scoped ArithmeticFunction.sigma
open OeisA63880

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Phi5N (t : ℕ) : ℕ := t^4 + t^3 + t^2 + t + 1

def Phi6N (t : ℕ) : ℕ := t^2 - t + 1

def BranchN (x y z : ℕ) : ℕ := 2^17 * x^4 * y^3 * z^3

theorem unitary_coprime_mul_iff {m n a b : ℕ}
    (hmn : m.Coprime n) (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (ha : a ∣ m) (hb : b ∣ n) :
    (a * b).Coprime ((m * n) / (a * b)) ↔
      a.Coprime (m / a) ∧ b.Coprime (n / b) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha hmpos
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb hnpos
  have habpos : 0 < a * b := mul_pos hapos hbpos
  have hprod : m * n = (a * b) * ((m / a) * (n / b)) := by
    calc
      m * n = (a * (m / a)) * (b * (n / b)) := by
        rw [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb]
      _ = (a * b) * ((m / a) * (n / b)) := by ac_rfl
  have hcomp : (m * n) / (a * b) = (m / a) * (n / b) := by
    rw [hprod, mul_comm (a * b) ((m / a) * (n / b)), Nat.mul_div_left _ habpos]
  rw [hcomp]
  constructor
  · intro h
    constructor
    · exact (h.coprime_dvd_left ((dvd_refl a).mul_right b)).coprime_dvd_right
        ((dvd_refl (m / a)).mul_right (n / b))
    · exact (h.coprime_dvd_left ((dvd_refl b).mul_left a)).coprime_dvd_right
        ((dvd_refl (n / b)).mul_left (m / a))
  · rintro ⟨haa, hbb⟩
    have han : a.Coprime n := hmn.coprime_dvd_left ha
    have hamb : a.Coprime (n / b) := han.coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have hbm : b.Coprime m := hmn.symm.coprime_dvd_left hb
    have hbma : b.Coprime (m / a) := hbm.coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    have hac : a.Coprime ((m / a) * (n / b)) := Nat.Coprime.mul_right haa hamb
    have hbc : b.Coprime ((m / a) * (n / b)) := Nat.Coprime.mul_right hbma hbb
    exact Nat.Coprime.mul_left hac hbc

theorem unitaryDivisors_mul {m n : ℕ} (hmn : m.Coprime n)
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) :
    unitaryDivisors (m * n) =
      (unitaryDivisors m ×ˢ unitaryDivisors n).image (fun ab => ab.1 * ab.2) := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_filter.mp hd with ⟨hdDiv, hdCop⟩
    have hdvd : d ∣ m * n := (Nat.mem_divisors.mp hdDiv).1
    let a := Nat.gcd d m
    let b := Nat.gcd d n
    have ha : a ∣ m := Nat.gcd_dvd_right d m
    have hb : b ∣ n := Nat.gcd_dvd_right d n
    have hab : a * b = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).2 hdvd
    have hpair : a.Coprime (m / a) ∧ b.Coprime (n / b) := by
      apply (unitary_coprime_mul_iff hmn hm0 hn0 ha hb).1
      simpa [hab] using hdCop
    have haDiv : a ∈ m.divisors := Nat.mem_divisors.mpr ⟨ha, hm0⟩
    have hbDiv : b ∈ n.divisors := Nat.mem_divisors.mpr ⟨hb, hn0⟩
    have haU : a ∈ unitaryDivisors m := Finset.mem_filter.mpr ⟨haDiv, hpair.1⟩
    have hbU : b ∈ unitaryDivisors n := Finset.mem_filter.mpr ⟨hbDiv, hpair.2⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨haU, hbU⟩, hab⟩
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨ab, habU, rfl⟩
    rcases Finset.mem_product.mp habU with ⟨haU, hbU⟩
    rcases Finset.mem_filter.mp haU with ⟨haDiv, haCop⟩
    rcases Finset.mem_filter.mp hbU with ⟨hbDiv, hbCop⟩
    have ha : ab.1 ∣ m := (Nat.mem_divisors.mp haDiv).1
    have hb : ab.2 ∣ n := (Nat.mem_divisors.mp hbDiv).1
    have hdiv : ab.1 * ab.2 ∣ m * n := Nat.mul_dvd_mul ha hb
    have hDiv : ab.1 * ab.2 ∈ (m * n).divisors :=
      Nat.mem_divisors.mpr ⟨hdiv, mul_ne_zero hm0 hn0⟩
    have hCop : (ab.1 * ab.2).Coprime ((m * n) / (ab.1 * ab.2)) :=
      (unitary_coprime_mul_iff hmn hm0 hn0 ha hb).2 ⟨haCop, hbCop⟩
    exact Finset.mem_filter.mpr ⟨hDiv, hCop⟩

theorem usigma_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n)
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) :
    usigma (m * n) = usigma m * usigma n := by
  rw [usigma, unitaryDivisors_mul hmn hm0 hn0]
  rw [Finset.sum_image]
  · simp only [Finset.sum_product, usigma]
    rw [← Finset.sum_mul_sum]
  · intro a ha b hb heq
    rcases Finset.mem_product.mp ha with ⟨ha1, ha2⟩
    rcases Finset.mem_product.mp hb with ⟨hb1, hb2⟩
    have haD : a ∈ m.divisors ×ˢ n.divisors := Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp ha1).1, (Finset.mem_filter.mp ha2).1⟩
    have hbD : b ∈ m.divisors ×ˢ n.divisors := Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hb1).1, (Finset.mem_filter.mp hb2).1⟩
    exact hmn.mul_injOn_divisors (by simpa using haD) (by simpa using hbD) heq

theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  ext d
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    rcases Finset.mem_filter.mp hd with ⟨hdDiv, hdCop⟩
    have hdvd : d ∣ p ^ k := (Nat.mem_divisors.mp hdDiv).1
    obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    by_cases hi0 : i = 0
    · left
      simp [hi0]
    by_cases hikEq : i = k
    · right
      simp [hikEq]
    exfalso
    have hi_lt : i < k := lt_of_le_of_ne hik hikEq
    have hpi : p ∣ p ^ i := dvd_pow_self p hi0
    have hpik : p ^ i ∣ p ^ k := pow_dvd_pow p hik
    have hpq : p ∣ p ^ k / p ^ i := by
      apply (Nat.dvd_div_iff_mul_dvd hpik).2
      rw [← pow_succ]
      exact pow_dvd_pow p (Nat.succ_le_of_lt hi_lt)
    have hpp : p.Coprime p := (hdCop.coprime_dvd_left hpi).coprime_dvd_right hpq
    have hp1 : p = 1 := by simpa [Nat.Coprime] using hpp
    exact hp.ne_one hp1
  · rintro (rfl | rfl)
    · simp [unitaryDivisors, hp.ne_zero]
    · have hpkpos : 0 < p ^ k := pow_pos hp.pos k
      have hdivself : p ^ k / p ^ k = 1 := Nat.div_self hpkpos
      simp [unitaryDivisors, hp.ne_zero, hdivself]

theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = 1 + p ^ k := by
  have hpk1 : p ^ k ≠ 1 := (one_lt_pow₀ hp.one_lt hk).ne'
  rw [usigma, unitaryDivisors_prime_pow hp]
  rw [Finset.sum_insert]
  · simp
  · simpa [eq_comm] using hpk1

theorem usigma_prime_pow_three {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 3) = 1 + p ^ 3 := by
  exact usigma_prime_pow hp (by decide)

theorem usigma_prime_pow_four {p : ℕ} (hp : p.Prime) :
    usigma (p ^ 4) = 1 + p ^ 4 := by
  exact usigma_prime_pow hp (by decide)

theorem usigma_two_pow_seventeen :
    usigma (2 ^ 17) = 1 + 2 ^ 17 := by
  exact usigma_prime_pow Nat.prime_two (by decide)

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

theorem branch_coprimes {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x) :
    (2 ^ 17).Coprime (x ^ 4) ∧
      ((2 ^ 17) * x ^ 4).Coprime (y ^ 3) ∧
      (((2 ^ 17) * x ^ 4) * y ^ 3).Coprime (z ^ 3) := by
  have h2x : 2 ≠ x := by omega
  have h2z : 2 ≠ z := by omega
  have hxy : x ≠ y := by omega
  have hxz : x ≠ z := by omega
  have hyz_ne : y ≠ z := by omega
  have c2x : (2 ^ 17).Coprime (x ^ 4) :=
    Nat.coprime_pow_primes 17 4 Nat.prime_two hx h2x
  have c2y : (2 ^ 17).Coprime (y ^ 3) :=
    Nat.coprime_pow_primes 17 3 Nat.prime_two hy (by omega)
  have c2z : (2 ^ 17).Coprime (z ^ 3) :=
    Nat.coprime_pow_primes 17 3 Nat.prime_two hz h2z
  have cxy : (x ^ 4).Coprime (y ^ 3) :=
    Nat.coprime_pow_primes 4 3 hx hy hxy
  have cxz : (x ^ 4).Coprime (z ^ 3) :=
    Nat.coprime_pow_primes 4 3 hx hz hxz
  have cyz : (y ^ 3).Coprime (z ^ 3) :=
    Nat.coprime_pow_primes 3 3 hy hz hyz_ne
  refine ⟨c2x, Nat.Coprime.mul_left c2y cxy, ?_⟩
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_left c2z cxz) cyz

theorem sigma_branch {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x) :
    ArithmeticFunction.sigma 1 (BranchN x y z) =
      262143 * Phi5N x * ((y + 1) * (y ^ 2 + 1)) * ((z + 1) * (z ^ 2 + 1)) := by
  rcases branch_coprimes hx hy hz h2y hyz hzx with ⟨c2x, cAxy, cAxyz⟩
  simp only [BranchN]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cAxyz,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cAxy,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime c2x,
    sigma_two_pow_seventeen, sigma_prime_pow_four hx,
    sigma_prime_pow_three hy, sigma_prime_pow_three hz]

theorem usigma_branch {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x) :
    usigma (BranchN x y z) =
      131073 * (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3) := by
  rcases branch_coprimes hx hy hz h2y hyz hzx with ⟨c2x, cAxy, cAxyz⟩
  have h20 : 2 ^ 17 ≠ 0 := by norm_num
  have hx40 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx.ne_zero
  have hy30 : y ^ 3 ≠ 0 := pow_ne_zero 3 hy.ne_zero
  have hz30 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz.ne_zero
  have h2x0 : (2 ^ 17) * x ^ 4 ≠ 0 := mul_ne_zero h20 hx40
  have h2xy0 : ((2 ^ 17) * x ^ 4) * y ^ 3 ≠ 0 := mul_ne_zero h2x0 hy30
  simp only [BranchN]
  rw [usigma_mul_of_coprime cAxyz h2xy0 hz30,
    usigma_mul_of_coprime cAxy h2x0 hy30,
    usigma_mul_of_coprime c2x h20 hx40,
    usigma_two_pow_seventeen, usigma_prime_pow_four hx,
    usigma_prime_pow_three hy, usigma_prime_pow_three hz]
  norm_num

theorem A_branch_uncancelled {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x)
    (hA : A (BranchN x y z)) :
    262143 * Phi5N x * ((y + 1) * (y ^ 2 + 1)) * ((z + 1) * (z ^ 2 + 1)) =
      262146 * (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3) := by
  calc
    262143 * Phi5N x * ((y + 1) * (y ^ 2 + 1)) * ((z + 1) * (z ^ 2 + 1)) =
        ArithmeticFunction.sigma 1 (BranchN x y z) :=
      (sigma_branch hx hy hz h2y hyz hzx).symm
    _ = 2 * usigma (BranchN x y z) := hA.2
    _ = 2 * (131073 * (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3)) := by
      rw [usigma_branch hx hy hz h2y hyz hzx]
    _ = 262146 * (1 + x ^ 4) * (1 + y ^ 3) * (1 + z ^ 3) := by ring

theorem A_branch_cross_rat {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x)
    (hA : A (BranchN x y z)) :
    (262143 : ℚ) * D17Round22.Phi5 (x : ℚ) * ((y : ℚ) ^ 2 + 1) * ((z : ℚ) ^ 2 + 1) =
      (262146 : ℚ) * ((x : ℚ) ^ 4 + 1) * D17Round22.Phi6 (y : ℚ) *
        D17Round22.Phi6 (z : ℚ) := by
  have hnat := A_branch_uncancelled hx hy hz h2y hyz hzx hA
  have hq :
      (262143 : ℚ) * (Phi5N x : ℚ) * (((y : ℚ) + 1) * ((y : ℚ) ^ 2 + 1)) *
          (((z : ℚ) + 1) * ((z : ℚ) ^ 2 + 1)) =
        (262146 : ℚ) * (1 + (x : ℚ) ^ 4) * (1 + (y : ℚ) ^ 3) *
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
  let lhs : ℚ := (262143 : ℚ) * D17Round22.Phi5 (x : ℚ) *
    ((y : ℚ) ^ 2 + 1) * ((z : ℚ) ^ 2 + 1)
  let rhs : ℚ := (262146 : ℚ) * ((x : ℚ) ^ 4 + 1) *
    D17Round22.Phi6 (y : ℚ) * D17Round22.Phi6 (z : ℚ)
  have hcommon : c * lhs = c * rhs := by
    dsimp [c, lhs, rhs]
    calc
      (((y : ℚ) + 1) * ((z : ℚ) + 1)) *
          ((262143 : ℚ) * D17Round22.Phi5 (x : ℚ) * ((y : ℚ) ^ 2 + 1) *
            ((z : ℚ) ^ 2 + 1)) =
          (262143 : ℚ) * D17Round22.Phi5 (x : ℚ) *
            (((y : ℚ) + 1) * ((y : ℚ) ^ 2 + 1)) *
            (((z : ℚ) + 1) * ((z : ℚ) ^ 2 + 1)) := by ring
      _ = (262146 : ℚ) * (1 + (x : ℚ) ^ 4) * (1 + (y : ℚ) ^ 3) *
            (1 + (z : ℚ) ^ 3) := hq
      _ = (((y : ℚ) + 1) * ((z : ℚ) + 1)) *
          ((262146 : ℚ) * ((x : ℚ) ^ 4 + 1) * D17Round22.Phi6 (y : ℚ) *
            D17Round22.Phi6 (z : ℚ)) := by
        rw [hyFactor, hzFactor]
        ring
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  exact mul_left_cancel₀ hc0 hcommon

theorem A_branch_ratio {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x)
    (hA : A (BranchN x y z)) :
    D17Round22.R4 (x : ℚ) * D17Round22.R3 (y : ℚ) * D17Round22.R3 (z : ℚ) =
      D17Round22.Target := by
  have hcross := A_branch_cross_rat hx hy hz h2y hyz hzx hA
  have hyQ : (1 : ℚ) < y := by exact_mod_cast (show 1 < y by omega)
  have hzQ : (1 : ℚ) < z := by exact_mod_cast (show 1 < z by omega)
  have hdx : (x : ℚ) ^ 4 + 1 ≠ 0 := by positivity
  have hdy : D17Round22.Phi6 (y : ℚ) ≠ 0 := (D17Round22.phi6_pos hyQ).ne'
  have hdz : D17Round22.Phi6 (z : ℚ) ≠ 0 := (D17Round22.phi6_pos hzQ).ne'
  simp only [D17Round22.R4, D17Round22.R3, D17Round22.Target]
  field_simp [hdx, hdy, hdz]
  ring_nf at hcross ⊢
  exact hcross

theorem A_branch_finite_y {x y z : ℕ}
    (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h2y : 2 < y) (hyz : y < z) (hzx : z < x)
    (hA : A (BranchN x y z)) :
    y < 262145 := by
  have hratio := A_branch_ratio hx hy hz h2y hyz hzx hA
  have hyQ : (1 : ℚ) < y := by exact_mod_cast (show 1 < y by omega)
  have hyzQ : (y : ℚ) ≤ z := by exact_mod_cast hyz.le
  have hzxQ : (z : ℚ) < x := by exact_mod_cast hzx
  have hQ := D17Round22.finite_y_bound_remaining_order hyQ hyzQ hzxQ hratio
  exact_mod_cast hQ

end D17Round24
