import D17RatioBridge

/-!
# D17 Round 29: kernel-checked finite box for the (17,9,3) template

For odd primes `p < q < r`, this file derives the exact ratio equation for

  `n = 2^14 * p^17 * q^9 * r^3`

directly from `OeisA63880.A`. It then proves the exact finite search box

  `10937 ≤ p < 32769` and `q < 17481596`.

No research-open theorem from the upstream A063880 file is used.
-/

namespace D17Round29

open scoped ArithmeticFunction.sigma
open OeisA63880
open D17Round24

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Branch (p q r : ℕ) : ℕ := 2^14 * p^17 * q^9 * r^3

def S17N (x : ℕ) : ℕ :=
  1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9 +
    x^10 + x^11 + x^12 + x^13 + x^14 + x^15 + x^16 + x^17

def S9N (x : ℕ) : ℕ :=
  1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9

def S3N (x : ℕ) : ℕ := 1 + x + x^2 + x^3

def S17 (x : ℚ) : ℚ :=
  1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9 +
    x^10 + x^11 + x^12 + x^13 + x^14 + x^15 + x^16 + x^17

def S9 (x : ℚ) : ℚ :=
  1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9

def S3 (x : ℚ) : ℚ := 1 + x + x^2 + x^3

def R17 (x : ℚ) : ℚ := S17 x / (1 + x^17)
def R9 (x : ℚ) : ℚ := S9 x / (1 + x^9)
def R3 (x : ℚ) : ℚ := S3 x / (1 + x^3)
def Target : ℚ := 32770 / 32767

theorem sigma_prime_pow_seventeen {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p^17) = S17N p := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, S17N]

theorem sigma_prime_pow_nine {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p^9) = S9N p := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, S9N]

theorem sigma_prime_pow_three' {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p^3) = S3N p := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, S3N]

theorem sigma_two_pow_fourteen :
    ArithmeticFunction.sigma 1 (2^14) = 32767 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  norm_num [Finset.sum_range_succ]

theorem usigma_two_pow_fourteen : usigma (2^14) = 16385 := by
  simpa using (usigma_prime_pow Nat.prime_two (show (14 : ℕ) ≠ 0 by decide))

theorem branch_coprimes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r) :
    (2^14).Coprime (p^17) ∧
      ((2^14) * p^17).Coprime (q^9) ∧
      (((2^14) * p^17) * q^9).Coprime (r^3) := by
  have h2pne : 2 ≠ p := by omega
  have h2qne : 2 ≠ q := by omega
  have h2rne : 2 ≠ r := by omega
  have hpqne : p ≠ q := by omega
  have hprne : p ≠ r := by omega
  have hqrne : q ≠ r := by omega
  have c2p : (2^14).Coprime (p^17) :=
    Nat.coprime_pow_primes 14 17 Nat.prime_two hp h2pne
  have c2q : (2^14).Coprime (q^9) :=
    Nat.coprime_pow_primes 14 9 Nat.prime_two hq h2qne
  have c2r : (2^14).Coprime (r^3) :=
    Nat.coprime_pow_primes 14 3 Nat.prime_two hr h2rne
  have cpq : (p^17).Coprime (q^9) :=
    Nat.coprime_pow_primes 17 9 hp hq hpqne
  have cpr : (p^17).Coprime (r^3) :=
    Nat.coprime_pow_primes 17 3 hp hr hprne
  have cqr : (q^9).Coprime (r^3) :=
    Nat.coprime_pow_primes 9 3 hq hr hqrne
  refine ⟨c2p, Nat.Coprime.mul_left c2q cpq, ?_⟩
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_left c2r cpr) cqr

theorem sigma_branch {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r) :
    ArithmeticFunction.sigma 1 (Branch p q r) =
      32767 * S17N p * S9N q * S3N r := by
  rcases branch_coprimes hp hq hr h2p hpq hqr with ⟨c2p, cApq, cApqr⟩
  simp only [Branch]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cApqr,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cApq,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime c2p,
    sigma_two_pow_fourteen, sigma_prime_pow_seventeen hp,
    sigma_prime_pow_nine hq, sigma_prime_pow_three' hr]

theorem usigma_branch {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r) :
    usigma (Branch p q r) =
      16385 * (1 + p^17) * (1 + q^9) * (1 + r^3) := by
  rcases branch_coprimes hp hq hr h2p hpq hqr with ⟨c2p, cApq, cApqr⟩
  have h20 : 2^14 ≠ 0 := by norm_num
  have hp0 : p^17 ≠ 0 := pow_ne_zero 17 hp.ne_zero
  have hq0 : q^9 ≠ 0 := pow_ne_zero 9 hq.ne_zero
  have hr0 : r^3 ≠ 0 := pow_ne_zero 3 hr.ne_zero
  have h2p0 : (2^14) * p^17 ≠ 0 := mul_ne_zero h20 hp0
  have h2pq0 : ((2^14) * p^17) * q^9 ≠ 0 := mul_ne_zero h2p0 hq0
  simp only [Branch]
  rw [usigma_mul_of_coprime cApqr h2pq0 hr0,
    usigma_mul_of_coprime cApq h2p0 hq0,
    usigma_mul_of_coprime c2p h20 hp0,
    usigma_two_pow_fourteen,
    usigma_prime_pow hp (by decide),
    usigma_prime_pow hq (by decide),
    usigma_prime_pow hr (by decide)]

theorem A_branch_uncancelled {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    32767 * S17N p * S9N q * S3N r =
      32770 * (1 + p^17) * (1 + q^9) * (1 + r^3) := by
  calc
    32767 * S17N p * S9N q * S3N r =
        ArithmeticFunction.sigma 1 (Branch p q r) :=
      (sigma_branch hp hq hr h2p hpq hqr).symm
    _ = 2 * usigma (Branch p q r) := hA.2
    _ = 2 * (16385 * (1 + p^17) * (1 + q^9) * (1 + r^3)) := by
      rw [usigma_branch hp hq hr h2p hpq hqr]
    _ = 32770 * (1 + p^17) * (1 + q^9) * (1 + r^3) := by ring

lemma cast_S17N (p : ℕ) : (S17N p : ℚ) = S17 (p : ℚ) := by
  simp [S17N, S17]

lemma cast_S9N (q : ℕ) : (S9N q : ℚ) = S9 (q : ℚ) := by
  simp [S9N, S9]

lemma cast_S3N (r : ℕ) : (S3N r : ℚ) = S3 (r : ℚ) := by
  simp [S3N, S3]

theorem A_branch_ratio {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    R17 (p : ℚ) * R9 (q : ℚ) * R3 (r : ℚ) = Target := by
  have hnat := A_branch_uncancelled hp hq hr h2p hpq hqr hA
  have hqeq :
      (32767 : ℚ) * (S17N p : ℚ) * (S9N q : ℚ) * (S3N r : ℚ) =
        (32770 : ℚ) * (1 + (p : ℚ)^17) * (1 + (q : ℚ)^9) *
          (1 + (r : ℚ)^3) := by
    exact_mod_cast hnat
  rw [cast_S17N, cast_S9N, cast_S3N] at hqeq
  have hdp : (1 : ℚ) + (p : ℚ)^17 ≠ 0 := by positivity
  have hdq : (1 : ℚ) + (q : ℚ)^9 ≠ 0 := by positivity
  have hdr : (1 : ℚ) + (r : ℚ)^3 ≠ 0 := by positivity
  simp only [R17, R9, R3, Target]
  field_simp [hdp, hdq, hdr]
  ring_nf at hqeq ⊢
  exact hqeq

theorem R17_pos {t : ℚ} (ht : 1 < t) : 0 < R17 t := by
  have hnum : 0 < S17 t := by
    simp [S17]
    positivity
  have hden : 0 < (1 : ℚ) + t^17 := by positivity
  exact div_pos hnum hden

theorem R9_pos {t : ℚ} (ht : 1 < t) : 0 < R9 t := by
  have hnum : 0 < S9 t := by
    simp [S9]
    positivity
  have hden : 0 < (1 : ℚ) + t^9 := by positivity
  exact div_pos hnum hden

theorem R3_pos {t : ℚ} (ht : 1 < t) : 0 < R3 t := by
  have hnum : 0 < S3 t := by
    simp [S3]
    positivity
  have hden : 0 < (1 : ℚ) + t^3 := by positivity
  exact div_pos hnum hden

theorem one_lt_R9 {t : ℚ} (ht : 1 < t) : 1 < R9 t := by
  have hden : 0 < (1 : ℚ) + t^9 := by positivity
  simp only [R9]
  rw [lt_div_iff₀ hden]
  have hmid : 0 < t + t^2 + t^3 + t^4 + t^5 + t^6 + t^7 + t^8 := by
    have ht0 : 0 < t := by linarith
    positivity
  simp [S9]
  linarith

theorem one_lt_R3 {t : ℚ} (ht : 1 < t) : 1 < R3 t := by
  have hden : 0 < (1 : ℚ) + t^3 := by positivity
  simp only [R3]
  rw [lt_div_iff₀ hden]
  have hmid : 0 < t + t^2 := by
    have ht0 : 0 < t := by linarith
    positivity
  simp [S3]
  linarith

theorem one_add_inv_lt_R17 {t : ℚ} (ht : 1 < t) :
    1 + 1 / t < R17 t := by
  have ht0 : 0 < t := by linarith
  have hden : 0 < (1 : ℚ) + t^17 := by positivity
  have hrewrite : 1 + 1 / t = (t + 1) / t := by
    field_simp
  rw [hrewrite]
  simp only [R17]
  rw [div_lt_div_iff₀ ht0 hden]
  have hsq : 0 < t^2 - 1 := by
    calc
      0 < (t - 1) * (t + 1) := mul_pos (by linarith) (by linarith)
      _ = t^2 - 1 := by ring
  have hrest : 0 ≤ t^3 + t^4 + t^5 + t^6 + t^7 + t^8 + t^9 +
      t^10 + t^11 + t^12 + t^13 + t^14 + t^15 + t^16 := by
    positivity
  have hrem : 0 < (t^2 - 1) + (t^3 + t^4 + t^5 + t^6 + t^7 + t^8 +
      t^9 + t^10 + t^11 + t^12 + t^13 + t^14 + t^15 + t^16) := by
    linarith
  have hid :
      t * S17 t = (t + 1) * (1 + t^17) +
        ((t^2 - 1) + (t^3 + t^4 + t^5 + t^6 + t^7 + t^8 + t^9 +
          t^10 + t^11 + t^12 + t^13 + t^14 + t^15 + t^16)) := by
    simp [S17]
    ring
  rw [mul_comm (S17 t) t, hid]
  linarith

theorem R17_lt_U {t : ℚ} (ht : 1 < t) : R17 t < D17Round22.U t := by
  have hdenR : 0 < (1 : ℚ) + t^17 := by positivity
  have hdenU : 0 < t - 1 := by linarith
  simp only [R17, D17Round22.U]
  rw [div_lt_div_iff₀ hdenR hdenU]
  have hid : S17 t * (t - 1) = t * (1 + t^17) - (t + 1) := by
    simp [S17]
    ring
  rw [hid]
  linarith

theorem R9_lt_U {t : ℚ} (ht : 1 < t) : R9 t < D17Round22.U t := by
  have hdenR : 0 < (1 : ℚ) + t^9 := by positivity
  have hdenU : 0 < t - 1 := by linarith
  simp only [R9, D17Round22.U]
  rw [div_lt_div_iff₀ hdenR hdenU]
  have hid : S9 t * (t - 1) = t * (1 + t^9) - (t + 1) := by
    simp [S9]
    ring
  rw [hid]
  linarith

theorem R3_lt_U {t : ℚ} (ht : 1 < t) : R3 t < D17Round22.U t := by
  have hdenR : 0 < (1 : ℚ) + t^3 := by positivity
  have hdenU : 0 < t - 1 := by linarith
  simp only [R3, D17Round22.U]
  rw [div_lt_div_iff₀ hdenR hdenU]
  have hid : S3 t * (t - 1) = t * (1 + t^3) - (t + 1) := by
    simp [S3]
    ring
  rw [hid]
  linarith

theorem R17_lt_target_of_ratio {p q r : ℚ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hEq : R17 p * R9 q * R3 r = Target) :
    R17 p < Target := by
  have hpR : 0 < R17 p := R17_pos hp
  have hqR : 1 < R9 q := one_lt_R9 hq
  have hrR : 1 < R3 r := one_lt_R3 hr
  have h1 : R17 p < R17 p * R9 q := by nlinarith
  have h2 : R17 p * R9 q < (R17 p * R9 q) * R3 r := by
    have hpos : 0 < R17 p * R9 q := mul_pos hpR (R9_pos hq)
    nlinarith
  calc
    R17 p < R17 p * R9 q := h1
    _ < (R17 p * R9 q) * R3 r := h2
    _ = Target := by simpa [mul_assoc] using hEq

theorem target_lt_U_cube_of_order {p q r : ℚ}
    (hp : 1 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hEq : R17 p * R9 q * R3 r = Target) :
    Target < D17Round22.U p ^ 3 := by
  have hq : 1 < q := lt_of_lt_of_le hp hpq
  have hr : 1 < r := lt_of_lt_of_le hq hqr
  have hUq : D17Round22.U q ≤ D17Round22.U p :=
    D17Round22.U_antitone hp hpq
  have hUr : D17Round22.U r ≤ D17Round22.U p :=
    D17Round22.U_antitone hp (hpq.trans hqr)
  have h17 : R17 p < D17Round22.U p := R17_lt_U hp
  have h9 : R9 q < D17Round22.U p := lt_of_lt_of_le (R9_lt_U hq) hUq
  have h3 : R3 r < D17Round22.U p := lt_of_lt_of_le (R3_lt_U hr) hUr
  have hUp : 0 ≤ D17Round22.U p := le_of_lt (D17Round22.U_pos hp)
  have h12 : R17 p * R9 q < D17Round22.U p * D17Round22.U p := by
    exact mul_lt_mul h17 (le_of_lt h9) (R9_pos hq) hUp
  have hUU : 0 ≤ D17Round22.U p * D17Round22.U p := mul_nonneg hUp hUp
  have h123 : (R17 p * R9 q) * R3 r <
      (D17Round22.U p * D17Round22.U p) * D17Round22.U p := by
    exact mul_lt_mul h12 (le_of_lt h3) (R3_pos hr) hUU
  calc
    Target = (R17 p * R9 q) * R3 r := by simpa [mul_assoc] using hEq.symm
    _ < (D17Round22.U p * D17Round22.U p) * D17Round22.U p := h123
    _ = D17Round22.U p ^ 3 := by ring

theorem p_boundary :
    D17Round22.U (32769 : ℚ)^3 < Target := by
  norm_num [D17Round22.U, Target]

theorem p_upper_of_ratio {p q r : ℚ}
    (hp : 1 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hEq : R17 p * R9 q * R3 r = Target) :
    p < 32769 := by
  have hprod := target_lt_U_cube_of_order hp hpq hqr hEq
  by_contra hnot
  have hcp : (32769 : ℚ) ≤ p := le_of_not_gt hnot
  have hU : D17Round22.U p ≤ D17Round22.U (32769 : ℚ) :=
    D17Round22.U_antitone (by norm_num) hcp
  have hcube : D17Round22.U p ^ 3 ≤ D17Round22.U (32769 : ℚ)^3 := by
    exact pow_le_pow_left₀ (le_of_lt (D17Round22.U_pos hp)) hU 3
  have hb := p_boundary
  linarith

theorem p_lower_raw_of_ratio {p q r : ℚ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hEq : R17 p * R9 q * R3 r = Target) :
    (10922 : ℚ) < p := by
  have hrt : R17 p < Target := R17_lt_target_of_ratio hp hq hr hEq
  have hlo : 1 + 1 / p < Target := lt_trans (one_add_inv_lt_R17 hp) hrt
  have hp0 : 0 < p := by linarith
  have hre : 1 + 1 / p = (p + 1) / p := by
    field_simp
  rw [hre] at hlo
  have hden : (0 : ℚ) < 32767 := by norm_num
  rw [show Target = (32770 : ℚ) / 32767 by rfl] at hlo
  rw [div_lt_div_iff₀ hp0 hden] at hlo
  norm_num at hlo ⊢
  linarith

theorem prime_gap_10937 {p : ℕ} (hp : p.Prime) (hlo : 10922 < p) :
    10937 ≤ p := by
  by_contra hnot
  have hhi : p ≤ 10936 := by omega
  have hlo' : 10923 ≤ p := by omega
  interval_cases p <;> norm_num at hp

theorem target_lt_U10937_mul_Uq_sq {p q r : ℚ}
    (hp0 : 1 < p) (hq0 : 1 < q) (hr0 : 1 < r)
    (hpmin : (10937 : ℚ) ≤ p) (_hpq : p ≤ q) (hqr : q ≤ r)
    (hEq : R17 p * R9 q * R3 r = Target) :
    Target < D17Round22.U (10937 : ℚ) * D17Round22.U q ^ 2 := by
  have hUp : D17Round22.U p ≤ D17Round22.U (10937 : ℚ) :=
    D17Round22.U_antitone (by norm_num) hpmin
  have hUr : D17Round22.U r ≤ D17Round22.U q :=
    D17Round22.U_antitone hq0 hqr
  have h17 : R17 p < D17Round22.U (10937 : ℚ) :=
    lt_of_lt_of_le (R17_lt_U hp0) hUp
  have h9 : R9 q < D17Round22.U q := R9_lt_U hq0
  have h3 : R3 r < D17Round22.U q := lt_of_lt_of_le (R3_lt_U hr0) hUr
  have hU0 : 0 ≤ D17Round22.U (10937 : ℚ) :=
    le_of_lt (D17Round22.U_pos (by norm_num))
  have hUq0 : 0 ≤ D17Round22.U q := le_of_lt (D17Round22.U_pos hq0)
  have h12 : R17 p * R9 q <
      D17Round22.U (10937 : ℚ) * D17Round22.U q := by
    exact mul_lt_mul h17 (le_of_lt h9) (R9_pos hq0) hU0
  have hright0 : 0 ≤ D17Round22.U (10937 : ℚ) * D17Round22.U q :=
    mul_nonneg hU0 hUq0
  have h123 : (R17 p * R9 q) * R3 r <
      (D17Round22.U (10937 : ℚ) * D17Round22.U q) * D17Round22.U q := by
    exact mul_lt_mul h12 (le_of_lt h3) (R3_pos hr0) hright0
  calc
    Target = (R17 p * R9 q) * R3 r := by simpa [mul_assoc] using hEq.symm
    _ < (D17Round22.U (10937 : ℚ) * D17Round22.U q) *
        D17Round22.U q := h123
    _ = D17Round22.U (10937 : ℚ) * D17Round22.U q ^ 2 := by ring

theorem q_boundary :
    D17Round22.U (10937 : ℚ) *
        D17Round22.U (17481596 : ℚ)^2 < Target := by
  norm_num [D17Round22.U, Target]

theorem q_upper_of_ratio {p q r : ℚ}
    (hp0 : 1 < p) (hq0 : 1 < q) (hr0 : 1 < r)
    (hpmin : (10937 : ℚ) ≤ p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hEq : R17 p * R9 q * R3 r = Target) :
    q < 17481596 := by
  have hprod := target_lt_U10937_mul_Uq_sq hp0 hq0 hr0 hpmin hpq hqr hEq
  by_contra hnot
  have hcq : (17481596 : ℚ) ≤ q := le_of_not_gt hnot
  have hU : D17Round22.U q ≤ D17Round22.U (17481596 : ℚ) :=
    D17Round22.U_antitone (by norm_num) hcq
  have hsq : D17Round22.U q ^ 2 ≤ D17Round22.U (17481596 : ℚ)^2 := by
    exact pow_le_pow_left₀ (le_of_lt (D17Round22.U_pos hq0)) hU 2
  have hconst0 : 0 ≤ D17Round22.U (10937 : ℚ) :=
    le_of_lt (D17Round22.U_pos (by norm_num))
  have hmul : D17Round22.U (10937 : ℚ) * D17Round22.U q ^ 2 ≤
      D17Round22.U (10937 : ℚ) * D17Round22.U (17481596 : ℚ)^2 :=
    mul_le_mul_of_nonneg_left hsq hconst0
  have hb := q_boundary
  linarith

theorem A_branch_finite_box {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    10937 ≤ p ∧ p < 32769 ∧ q < 17481596 := by
  have hratio := A_branch_ratio hp hq hr h2p hpq hqr hA
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hqQ : (1 : ℚ) < q := by exact_mod_cast (show 1 < q by omega)
  have hrQ : (1 : ℚ) < r := by exact_mod_cast (show 1 < r by omega)
  have hpqQ : (p : ℚ) ≤ q := by exact_mod_cast hpq.le
  have hqrQ : (q : ℚ) ≤ r := by exact_mod_cast hqr.le
  have hpLowerRawQ := p_lower_raw_of_ratio hpQ hqQ hrQ hratio
  have hpLowerRaw : 10922 < p := by exact_mod_cast hpLowerRawQ
  have hpMin : 10937 ≤ p := prime_gap_10937 hp hpLowerRaw
  have hpMinQ : (10937 : ℚ) ≤ p := by exact_mod_cast hpMin
  have hpUpperQ := p_upper_of_ratio hpQ hpqQ hqrQ hratio
  have hqUpperQ := q_upper_of_ratio hpQ hqQ hrQ hpMinQ hpqQ hqrQ hratio
  constructor
  · exact hpMin
  constructor
  · exact_mod_cast hpUpperQ
  · exact_mod_cast hqUpperQ

/-- Mutation control: the q cutoff cannot be lowered by one using the same
uniform endpoint argument. -/
theorem q_boundary_previous_fails :
    ¬(D17Round22.U (10937 : ℚ) *
        D17Round22.U (17481595 : ℚ)^2 < Target) := by
  norm_num [D17Round22.U, Target]

#print axioms A_branch_ratio
#print axioms p_lower_raw_of_ratio
#print axioms prime_gap_10937
#print axioms p_upper_of_ratio
#print axioms q_upper_of_ratio
#print axioms A_branch_finite_box
#print axioms q_boundary_previous_fails

end D17Round29
