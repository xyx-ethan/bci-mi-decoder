import FormalConjectures.OEIS.«67599»

namespace OeisA67599

/-- The A067599 encoding of a positive prime power is the decimal concatenation of
its prime base and exponent. -/
lemma a_prime_pow (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) = p * 10 ^ (Nat.digits 10 e).length + e := by
  rw [a]
  rw [if_neg]
  · rw [hp.primeFactorsList_pow]
    rw [List.replicate_dedup he.ne']
    simp [concatenateNats]
  · have hpow : 1 < p ^ e := one_lt_pow₀ hp.one_lt he.ne'
    omega

/-- A convenient elementary growth estimate used in the prime-power exclusion. -/
lemma eleven_mul_lt_two_pow_sub_one (e : ℕ) (he : 8 ≤ e) :
    11 * e < 2 ^ (e - 1) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
      have he1 : 1 ≤ e := by omega
      have hpow : 2 ^ e = 2 * 2 ^ (e - 1) := by
        conv_lhs => rw [show e = (e - 1) + 1 by omega]
        rw [pow_succ]
        omega
      simp only [Nat.add_sub_cancel]
      rw [hpow]
      nlinarith

/-- No positive power of a prime is a fixed point of the A067599 encoding. -/
theorem no_prime_power_fixed_point (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) ≠ p ^ e := by
  rw [a_prime_pow p e hp he]
  intro hfix
  have hpdiv : p ∣ e := by
    exact (Nat.dvd_add_iff_left (Nat.dvd_mul_right p _)).mp (by
      rw [hfix]
      exact dvd_pow_self p he.ne')
  by_cases hsmall : e < 8
  · have hple : p ≤ e := Nat.le_of_dvd he hpdiv
    interval_cases e <;> interval_cases p <;> norm_num at hp hfix
  · have he8 : 8 ≤ e := by omega
    have hdigits :
        10 ^ (Nat.digits 10 e).length ≤ 10 * e :=
      Nat.base_pow_length_digits_le 10 e (by norm_num) he.ne'
    have he_le_pe : e ≤ p * e := by
      simpa using Nat.mul_le_mul_right e hp.one_le
    have henc_le :
        p * 10 ^ (Nat.digits 10 e).length + e ≤ 11 * p * e := by
      calc
        p * 10 ^ (Nat.digits 10 e).length + e
            ≤ p * (10 * e) + e :=
              Nat.add_le_add_right (Nat.mul_le_mul_left p hdigits) e
        _ ≤ 11 * p * e := by nlinarith
    have hgrowth := eleven_mul_lt_two_pow_sub_one e he8
    have henc_lt_two :
        p * 10 ^ (Nat.digits 10 e).length + e < p * 2 ^ (e - 1) := by
      apply lt_of_le_of_lt henc_le
      have hmul := Nat.mul_lt_mul_of_pos_left hgrowth hp.pos
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hbase : 2 ^ (e - 1) ≤ p ^ (e - 1) :=
      pow_le_pow_left' hp.two_le (e - 1)
    have hpowers : p * 2 ^ (e - 1) ≤ p ^ e := by
      calc
        p * 2 ^ (e - 1) ≤ p * p ^ (e - 1) := Nat.mul_le_mul_left p hbase
        _ = p ^ e := by
          conv_rhs => rw [show e = (e - 1) + 1 by omega, pow_succ]
          omega
    have hlt : p * 10 ^ (Nat.digits 10 e).length + e < p ^ e :=
      lt_of_lt_of_le henc_lt_two hpowers
    omega

end OeisA67599
