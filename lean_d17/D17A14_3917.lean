import D17RatioBridge

/-!
# D17 A063880: the `a = 14`, odd exponents `{3,9,17}` bridge

This file connects the concrete predicate `OeisA63880.A` to the cancelled
ratio equation used by the exact finite certificate.  It also kernel-checks
the finite coefficient root tables and the quadratic-discriminant bridge for
a tail of exponent three.
-/

namespace D17A14_3917

open scoped ArithmeticFunction.sigma
open OeisA63880
open D17Round24

set_option maxRecDepth 100000
set_option maxHeartbeats 0

inductive Tag where
  | e3
  | e9
  | e17
  deriving DecidableEq, Repr

namespace Tag

def exponent : Tag → ℕ
  | e3 => 3
  | e9 => 9
  | e17 => 17

end Tag

open Tag

/-- The positive even-power factor in `(1 + t + ... + t^e)`. -/
def PNat : Tag → ℕ → ℕ
  | .e3, t => t^2 + 1
  | .e9, t => t^8 + t^6 + t^4 + t^2 + 1
  | .e17, t => t^16 + t^14 + t^12 + t^10 + t^8 + t^6 + t^4 + t^2 + 1

def P : Tag → ℚ → ℚ
  | .e3, t => t^2 + 1
  | .e9, t => t^8 + t^6 + t^4 + t^2 + 1
  | .e17, t => t^16 + t^14 + t^12 + t^10 + t^8 + t^6 + t^4 + t^2 + 1

/-- The alternating factor in `1 + t^e = (t+1) Q_e(t)`. -/
def Q : Tag → ℚ → ℚ
  | .e3, t => t^2 - t + 1
  | .e9, t => t^8 - t^7 + t^6 - t^5 + t^4 - t^3 + t^2 - t + 1
  | .e17, t =>
      t^16 - t^15 + t^14 - t^13 + t^12 - t^11 + t^10 - t^9 +
      t^8 - t^7 + t^6 - t^5 + t^4 - t^3 + t^2 - t + 1

def R (e : Tag) (t : ℚ) : ℚ := P e t / Q e t

def U (t : ℚ) : ℚ := t / (t - 1)

def Target : ℚ := 32770 / 32767

def Branch14 (eb ec ed : Tag) (p q r : ℕ) : ℕ :=
  2^14 * p^(exponent eb) * q^(exponent ec) * r^(exponent ed)

lemma exponent_ne_zero (e : Tag) : exponent e ≠ 0 := by
  cases e <;> decide

lemma cast_PNat (e : Tag) (t : ℕ) :
    (PNat e t : ℚ) = P e (t : ℚ) := by
  cases e <;> norm_num [PNat, P]

lemma pow_add_one_factor (e : Tag) (t : ℚ) :
    1 + t^(exponent e) = (t + 1) * Q e t := by
  cases e <;> simp [exponent, Q] <;> ring

lemma sum_factor (e : Tag) (t : ℚ) :
    (t + 1) * P e t = ∑ i ∈ Finset.range (exponent e + 1), t^i := by
  cases e <;> simp [exponent, P, Finset.sum_range_succ] <;> ring

lemma Q_pos (e : Tag) {t : ℚ} (ht : 1 < t) : 0 < Q e t := by
  have ht1 : 0 < t + 1 := by linarith
  have hnum : 0 < 1 + t^(exponent e) := by positivity
  have hfac := pow_add_one_factor e t
  nlinarith

lemma P_pos (e : Tag) {t : ℚ} (ht : 1 < t) : 0 < P e t := by
  cases e <;> simp [P] <;> positivity

lemma R_pos (e : Tag) {t : ℚ} (ht : 1 < t) : 0 < R e t :=
  div_pos (P_pos e ht) (Q_pos e ht)

lemma P_sub_Q_pos (e : Tag) {t : ℚ} (ht : 1 < t) : 0 < P e t - Q e t := by
  have ht0 : 0 < t := by linarith
  cases e
  · simp [P, Q]
    linarith
  · have h2 : 0 < t^2 + 1 := by positivity
    have h4 : 0 < t^4 + 1 := by positivity
    simp only [P, Q]
    nlinarith [show
      (t^8 + t^6 + t^4 + t^2 + 1) -
        (t^8 - t^7 + t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) =
          t * (t^2 + 1) * (t^4 + 1) by ring]
  · have h2 : 0 < t^2 + 1 := by positivity
    have h4 : 0 < t^4 + 1 := by positivity
    have h8 : 0 < t^8 + 1 := by positivity
    simp only [P, Q]
    nlinarith [show
      (t^16 + t^14 + t^12 + t^10 + t^8 + t^6 + t^4 + t^2 + 1) -
        (t^16 - t^15 + t^14 - t^13 + t^12 - t^11 + t^10 - t^9 +
          t^8 - t^7 + t^6 - t^5 + t^4 - t^3 + t^2 - t + 1) =
          t * (t^2 + 1) * (t^4 + 1) * (t^8 + 1) by ring]

lemma one_lt_R (e : Tag) {t : ℚ} (ht : 1 < t) : 1 < R e t := by
  have hq := Q_pos e ht
  simp only [R]
  rw [lt_div_iff₀ hq]
  nlinarith [P_sub_Q_pos e ht]

lemma R_lt_U (e : Tag) {t : ℚ} (ht : 1 < t) : R e t < U t := by
  have hq := Q_pos e ht
  have hm : 0 < t - 1 := by linarith
  simp only [R, U]
  rw [div_lt_div_iff₀ hq hm]
  have hid : t * Q e t - P e t * (t - 1) = 1 := by
    cases e <;> simp [P, Q] <;> ring
  nlinarith

lemma U_pos {t : ℚ} (ht : 1 < t) : 0 < U t :=
  div_pos (by linarith) (by linarith)

lemma U_antitone {a b : ℚ} (ha : 1 < a) (hab : a ≤ b) : U b ≤ U a := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hdb : 0 < b - 1 := by linarith
  have hda : 0 < a - 1 := by linarith
  simp only [U]
  rw [div_le_div_iff₀ hdb hda]
  nlinarith

lemma R_gt_one_add_inv (e : Tag) {t : ℚ} (ht : 1 < t) :
    1 + 1 / t < R e t := by
  have ht0 : 0 < t := by linarith
  have hq := Q_pos e ht
  simp only [R]
  rw [lt_div_iff₀ hq]
  rw [add_mul, one_mul, div_mul_eq_mul_div, div_eq_iff ht0.ne']
  have hdiff : 0 < t * P e t - (t + 1) * Q e t := by
    cases e
    · simp [P, Q]
      linarith
    · have h3 : 0 ≤ t^3 := by positivity
      have h5 : 0 ≤ t^5 := by positivity
      have h7 : 0 ≤ t^7 := by positivity
      have hid : t * P .e9 t - (t + 1) * Q .e9 t =
          t^7 + t^5 + t^3 + t - 1 := by simp [P, Q]; ring
      rw [hid]
      nlinarith
    · have h3 : 0 ≤ t^3 := by positivity
      have h5 : 0 ≤ t^5 := by positivity
      have h7 : 0 ≤ t^7 := by positivity
      have h9 : 0 ≤ t^9 := by positivity
      have h11 : 0 ≤ t^11 := by positivity
      have h13 : 0 ≤ t^13 := by positivity
      have h15 : 0 ≤ t^15 := by positivity
      have hid : t * P .e17 t - (t + 1) * Q .e17 t =
          t^15 + t^13 + t^11 + t^9 + t^7 + t^5 + t^3 + t - 1 := by
        simp [P, Q]
        ring
      rw [hid]
      nlinarith
  nlinarith

lemma sigma_two_pow_14 :
    ArithmeticFunction.sigma 1 (2^14) = 32767 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  norm_num [Finset.sum_range_succ]

lemma usigma_two_pow_14 : usigma (2^14) = 16385 := by
  simpa using (usigma_prime_pow Nat.prime_two (show (14 : ℕ) ≠ 0 by decide))

lemma sigma_tag_pow (e : Tag) {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p^(exponent e)) = (p + 1) * PNat e p := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  cases e <;> simp [exponent, PNat, Finset.sum_range_succ] <;> ring

lemma usigma_tag_pow (e : Tag) {p : ℕ} (hp : p.Prime) :
    usigma (p^(exponent e)) = 1 + p^(exponent e) := by
  exact usigma_prime_pow hp (exponent_ne_zero e)

lemma branch_coprimes {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r) :
    (2^14).Coprime (p^(exponent eb)) ∧
      ((2^14) * p^(exponent eb)).Coprime (q^(exponent ec)) ∧
      (((2^14) * p^(exponent eb)) * q^(exponent ec)).Coprime
        (r^(exponent ed)) := by
  have h2pne : 2 ≠ p := by omega
  have h2qne : 2 ≠ q := by omega
  have h2rne : 2 ≠ r := by omega
  have hpqne : p ≠ q := by omega
  have hprne : p ≠ r := by omega
  have hqrne : q ≠ r := by omega
  have c2p := Nat.coprime_pow_primes 14 (exponent eb) Nat.prime_two hp h2pne
  have c2q := Nat.coprime_pow_primes 14 (exponent ec) Nat.prime_two hq h2qne
  have c2r := Nat.coprime_pow_primes 14 (exponent ed) Nat.prime_two hr h2rne
  have cpq := Nat.coprime_pow_primes (exponent eb) (exponent ec) hp hq hpqne
  have cpr := Nat.coprime_pow_primes (exponent eb) (exponent ed) hp hr hprne
  have cqr := Nat.coprime_pow_primes (exponent ec) (exponent ed) hq hr hqrne
  refine ⟨c2p, Nat.Coprime.mul_left c2q cpq, ?_⟩
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_left c2r cpr) cqr

lemma sigma_branch14 {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r) :
    ArithmeticFunction.sigma 1 (Branch14 eb ec ed p q r) =
      32767 * ((p + 1) * PNat eb p) * ((q + 1) * PNat ec q) *
        ((r + 1) * PNat ed r) := by
  rcases branch_coprimes hp hq hr h2p hpq hqr with ⟨c2p, cApq, cApqr⟩
  simp only [Branch14]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cApqr,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cApq,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime c2p,
    sigma_two_pow_14, sigma_tag_pow eb hp, sigma_tag_pow ec hq,
    sigma_tag_pow ed hr]

lemma usigma_branch14 {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r) :
    usigma (Branch14 eb ec ed p q r) =
      16385 * (1 + p^(exponent eb)) * (1 + q^(exponent ec)) *
        (1 + r^(exponent ed)) := by
  rcases branch_coprimes hp hq hr h2p hpq hqr with ⟨c2p, cApq, cApqr⟩
  have h20 : 2^14 ≠ 0 := by norm_num
  have hp0 : p^(exponent eb) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hq0 : q^(exponent ec) ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hr0 : r^(exponent ed) ≠ 0 := pow_ne_zero _ hr.ne_zero
  have h2p0 : (2^14) * p^(exponent eb) ≠ 0 := mul_ne_zero h20 hp0
  have h2pq0 : ((2^14) * p^(exponent eb)) * q^(exponent ec) ≠ 0 :=
    mul_ne_zero h2p0 hq0
  simp only [Branch14]
  rw [usigma_mul_of_coprime cApqr h2pq0 hr0,
    usigma_mul_of_coprime cApq h2p0 hq0,
    usigma_mul_of_coprime c2p h20 hp0,
    usigma_two_pow_14, usigma_tag_pow eb hp, usigma_tag_pow ec hq,
    usigma_tag_pow ed hr]

lemma A_branch14_uncancelled {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch14 eb ec ed p q r)) :
    32767 * ((p + 1) * PNat eb p) * ((q + 1) * PNat ec q) *
        ((r + 1) * PNat ed r) =
      32770 * (1 + p^(exponent eb)) * (1 + q^(exponent ec)) *
        (1 + r^(exponent ed)) := by
  calc
    32767 * ((p + 1) * PNat eb p) * ((q + 1) * PNat ec q) *
        ((r + 1) * PNat ed r) =
        ArithmeticFunction.sigma 1 (Branch14 eb ec ed p q r) :=
      (sigma_branch14 hp hq hr h2p hpq hqr).symm
    _ = 2 * usigma (Branch14 eb ec ed p q r) := hA.2
    _ = 2 * (16385 * (1 + p^(exponent eb)) * (1 + q^(exponent ec)) *
        (1 + r^(exponent ed))) := by
      rw [usigma_branch14 hp hq hr h2p hpq hqr]
    _ = 32770 * (1 + p^(exponent eb)) * (1 + q^(exponent ec)) *
        (1 + r^(exponent ed)) := by ring

lemma A_branch14_cross_rat {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch14 eb ec ed p q r)) :
    (32767 : ℚ) * P eb p * P ec q * P ed r =
      (32770 : ℚ) * Q eb p * Q ec q * Q ed r := by
  have hnat := A_branch14_uncancelled hp hq hr h2p hpq hqr hA
  have hqnat :
      (32767 : ℚ) * (((p : ℚ) + 1) * P eb p) *
          (((q : ℚ) + 1) * P ec q) * (((r : ℚ) + 1) * P ed r) =
        (32770 : ℚ) * (1 + (p : ℚ)^(exponent eb)) *
          (1 + (q : ℚ)^(exponent ec)) * (1 + (r : ℚ)^(exponent ed)) := by
    exact_mod_cast hnat
    all_goals simp [cast_PNat]
  rw [pow_add_one_factor eb, pow_add_one_factor ec, pow_add_one_factor ed] at hqnat
  let c : ℚ := ((p : ℚ) + 1) * ((q : ℚ) + 1) * ((r : ℚ) + 1)
  have hcommon :
      c * ((32767 : ℚ) * P eb p * P ec q * P ed r) =
        c * ((32770 : ℚ) * Q eb p * Q ec q * Q ed r) := by
    dsimp [c]
    calc
      (((p : ℚ) + 1) * ((q : ℚ) + 1) * ((r : ℚ) + 1)) *
          ((32767 : ℚ) * P eb p * P ec q * P ed r) =
        (32767 : ℚ) * (((p : ℚ) + 1) * P eb p) *
          (((q : ℚ) + 1) * P ec q) * (((r : ℚ) + 1) * P ed r) := by ring
      _ = (32770 : ℚ) * (((p : ℚ) + 1) * Q eb p) *
          (((q : ℚ) + 1) * Q ec q) * (((r : ℚ) + 1) * Q ed r) := hqnat
      _ = (((p : ℚ) + 1) * ((q : ℚ) + 1) * ((r : ℚ) + 1)) *
          ((32770 : ℚ) * Q eb p * Q ec q * Q ed r) := by ring
  have hc0 : c ≠ 0 := by
    dsimp [c]
    positivity
  exact mul_left_cancel₀ hc0 hcommon

lemma A_branch14_ratio {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch14 eb ec ed p q r)) :
    R eb p * R ec q * R ed r = Target := by
  have hcross := A_branch14_cross_rat hp hq hr h2p hpq hqr hA
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hqQ : (1 : ℚ) < q := by exact_mod_cast (show 1 < q by omega)
  have hrQ : (1 : ℚ) < r := by exact_mod_cast (show 1 < r by omega)
  have hpb := (Q_pos eb hpQ).ne'
  have hqb := (Q_pos ec hqQ).ne'
  have hrb := (Q_pos ed hrQ).ne'
  simp only [R, Target]
  field_simp [hpb, hqb, hrb]
  ring_nf at hcross ⊢
  exact hcross

lemma target_lt_cube_of_min {eb ec ed : Tag} {p q r : ℚ}
    (hp : 1 < p) (hpq : p ≤ q) (hpr : p ≤ r)
    (hEq : R eb p * R ec q * R ed r = Target) :
    Target < U p ^ 3 := by
  have hq : 1 < q := lt_of_lt_of_le hp hpq
  have hr : 1 < r := lt_of_lt_of_le hp hpr
  have hUq : U q ≤ U p := U_antitone hp hpq
  have hUr : U r ≤ U p := U_antitone hp hpr
  have hb : R eb p < U p := R_lt_U eb hp
  have hc : R ec q < U p := lt_of_lt_of_le (R_lt_U ec hq) hUq
  have hd : R ed r < U p := lt_of_lt_of_le (R_lt_U ed hr) hUr
  have hUp : 0 ≤ U p := le_of_lt (U_pos hp)
  have h12 : R eb p * R ec q < U p * U p :=
    mul_lt_mul hb (le_of_lt hc) (R_pos ec hq) hUp
  have h123 : (R eb p * R ec q) * R ed r < (U p * U p) * U p :=
    mul_lt_mul h12 (le_of_lt hd) (R_pos ed hr) (mul_nonneg hUp hUp)
  calc
    Target = (R eb p * R ec q) * R ed r := by simpa [mul_assoc] using hEq.symm
    _ < (U p * U p) * U p := h123
    _ = U p ^ 3 := by ring

lemma boundary_upper : U (32769 : ℚ) ^ 3 < Target := by
  norm_num [U, Target]

lemma target_lt_lower_boundary : Target < 1 + 1 / (10922 : ℚ) := by
  norm_num [Target]

lemma one_add_inv_antitone {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) :
    1 + 1 / b ≤ 1 + 1 / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have := one_div_le_one_div_of_le ha hab
  linarith

/-- Exact interval used by the finite certificate. -/
theorem A_branch14_p_window {eb ec ed : Tag} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch14 eb ec ed p q r)) :
    10923 ≤ p ∧ p < 32769 := by
  have hratio := A_branch14_ratio hp hq hr h2p hpq hqr hA
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpqQ : (p : ℚ) ≤ q := by exact_mod_cast hpq.le
  have hprQ : (p : ℚ) ≤ r := by exact_mod_cast (hpq.trans hqr).le
  have hupperQ : (p : ℚ) < 32769 := by
    have hc := target_lt_cube_of_min hpQ hpqQ hprQ hratio
    by_contra hn
    have hC : (32769 : ℚ) ≤ p := le_of_not_gt hn
    have hU := U_antitone (by norm_num : (1 : ℚ) < 32769) hC
    have hcube : U p ^ 3 ≤ U (32769 : ℚ) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt (U_pos hpQ)) hU 3
    have hb := boundary_upper
    linarith
  have hlowerQ : (10922 : ℚ) < p := by
    have hq1 : 1 < R ec (q : ℚ) := one_lt_R ec (by exact_mod_cast (show 1 < q by omega))
    have hr1 : 1 < R ed (r : ℚ) := one_lt_R ed (by exact_mod_cast (show 1 < r by omega))
    have hprod : R eb p < Target := by
      have hpR := R_pos eb hpQ
      rw [← hratio]
      nlinarith [mul_pos (sub_pos.mpr hq1) (sub_pos.mpr hr1)]
    have hinv := R_gt_one_add_inv eb hpQ
    by_contra hn
    have hp_le : (p : ℚ) ≤ 10922 := le_of_not_gt hn
    have hmono := one_add_inv_antitone (by norm_num : (0 : ℚ) < p) hp_le
    have hbound := target_lt_lower_boundary
    linarith
  constructor
  · exact_mod_cast hlowerQ
  · exact_mod_cast hupperQ

/-- Cancelled exponent-three tail equation implies a square discriminant. -/
theorem tail3_discriminant_identity (L Rr t : ℤ)
    (h : L * (t^2 + 1) = Rr * (t^2 - t + 1)) :
    (2 * (Rr - L) * t - Rr)^2 = Rr^2 - 4 * (Rr - L)^2 := by
  have hq : (Rr - L) * t^2 - Rr * t + (Rr - L) = 0 := by
    nlinarith [h]
  calc
    (2 * (Rr - L) * t - Rr)^2 =
        Rr^2 - 4 * (Rr - L)^2 +
          4 * (Rr - L) * ((Rr - L) * t^2 - Rr * t + (Rr - L)) := by ring
    _ = Rr^2 - 4 * (Rr - L)^2 := by rw [hq]; ring

/-- Modular versions of the certificate polynomials. -/
def PZ (e : Tag) {m : ℕ} (t : ZMod m) : ZMod m :=
  match e with
  | .e3 => t^2 + 1
  | .e9 => t^8 + t^6 + t^4 + t^2 + 1
  | .e17 => t^16 + t^14 + t^12 + t^10 + t^8 + t^6 + t^4 + t^2 + 1

def QZ (e : Tag) {m : ℕ} (t : ZMod m) : ZMod m :=
  match e with
  | .e3 => t^2 - t + 1
  | .e9 => t^8 - t^7 + t^6 - t^5 + t^4 - t^3 + t^2 - t + 1
  | .e17 =>
      t^16 - t^15 + t^14 - t^13 + t^12 - t^11 + t^10 - t^9 +
      t^8 - t^7 + t^6 - t^5 + t^4 - t^3 + t^2 - t + 1

lemma P3_roots_5 : ∀ t : ZMod 5, PZ .e3 t = 0 ↔ t = 2 ∨ t = 3 := by decide
lemma P9_roots_5 : ∀ t : ZMod 5, PZ .e9 t = 0 ↔ t = 1 ∨ t = 4 := by decide
lemma P17_no_root_5 : ∀ t : ZMod 5, PZ .e17 t ≠ 0 := by decide
lemma P3_roots_29 : ∀ t : ZMod 29, PZ .e3 t = 0 ↔ t = 12 ∨ t = 17 := by decide
lemma P9_no_root_29 : ∀ t : ZMod 29, PZ .e9 t ≠ 0 := by decide
lemma P17_no_root_29 : ∀ t : ZMod 29, PZ .e17 t ≠ 0 := by decide
lemma P3_roots_113 : ∀ t : ZMod 113, PZ .e3 t = 0 ↔ t = 15 ∨ t = 98 := by decide
lemma P9_no_root_113 : ∀ t : ZMod 113, PZ .e9 t ≠ 0 := by decide
lemma P17_no_root_113 : ∀ t : ZMod 113, PZ .e17 t ≠ 0 := by decide
lemma Q3_roots_7 : ∀ t : ZMod 7, QZ .e3 t = 0 ↔ t = 3 ∨ t = 5 := by decide
lemma Q9_roots_7 : ∀ t : ZMod 7, QZ .e9 t = 0 ↔ t = 3 ∨ t = 5 := by decide
lemma Q17_no_root_7 : ∀ t : ZMod 7, QZ .e17 t ≠ 0 := by decide
lemma Q3_roots_31 : ∀ t : ZMod 31, QZ .e3 t = 0 ↔ t = 6 ∨ t = 26 := by decide
lemma Q9_roots_31 : ∀ t : ZMod 31, QZ .e9 t = 0 ↔ t = 6 ∨ t = 26 := by decide
lemma Q17_no_root_31 : ∀ t : ZMod 31, QZ .e17 t ≠ 0 := by decide
lemma Q3_roots_151 : ∀ t : ZMod 151, QZ .e3 t = 0 ↔ t = 33 ∨ t = 119 := by decide
lemma Q9_roots_151 : ∀ t : ZMod 151, QZ .e9 t = 0 ↔ t = 33 ∨ t = 119 := by decide
lemma Q17_no_root_151 : ∀ t : ZMod 151, QZ .e17 t ≠ 0 := by decide

#print axioms A_branch14_cross_rat
#print axioms A_branch14_ratio
#print axioms A_branch14_p_window
#print axioms tail3_discriminant_identity
#print axioms P3_roots_29
#print axioms P3_roots_113
#print axioms Q17_no_root_151

end D17A14_3917
