import FormalConjectures.OEIS.«67599»

namespace OeisA67599

/-- On a positive prime power, the A067599 encoding is just the decimal
concatenation of the prime and the exponent. -/
lemma a_prime_pow (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) = concatenateNats p e := by
  unfold a
  have hpow_ge : 2 ≤ p ^ e := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := by simp
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  rw [if_neg (Nat.not_lt.mpr hpow_ge), hp.primeFactorsList_pow e]
  simp [List.replicate_dedup he.ne', concatenateNats]

/-- The elementary exponential estimate used to eliminate large exponents. -/
lemma eleven_mul_add_eight_lt_two_pow_add_seven (n : ℕ) :
    11 * (n + 8) < 2 ^ (n + 7) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        11 * (Nat.succ n + 8) ≤ 2 * (11 * (n + 8)) := by omega
        _ < 2 * 2 ^ (n + 7) := by omega
        _ = 2 ^ (Nat.succ n + 7) := by
          rw [show Nat.succ n + 7 = (n + 7) + 1 by omega, pow_succ]
          omega

lemma eleven_mul_lt_two_pow_pred (e : ℕ) (he : 8 ≤ e) :
    11 * e < 2 ^ (e - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le he
  have h := eleven_mul_add_eight_lt_two_pow_add_seven n
  convert h using 1 <;> omega

/-- No positive prime power is a fixed point of the A067599 encoding. -/
theorem no_prime_power_fixed_point
    (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    a (p ^ e) ≠ p ^ e := by
  rw [a_prime_pow p e hp he]
  intro hfix
  have hdiv_enc : p ∣ concatenateNats p e := by
    rw [hfix]
    exact dvd_pow_self p he.ne'
  have hdiv_first : p ∣ p * 10 ^ (Nat.digits 10 e).length :=
    ⟨10 ^ (Nat.digits 10 e).length, rfl⟩
  have hp_dvd_e : p ∣ e := by
    apply (Nat.dvd_add_iff_left hdiv_first).mp
    simpa [concatenateNats] using hdiv_enc
  by_cases he8 : 8 ≤ e
  · have hdigits : 10 ^ (Nat.digits 10 e).length ≤ 10 * e :=
      Nat.base_pow_length_digits_le 10 e (by norm_num) he.ne'
    have hmul_digits :
        p * 10 ^ (Nat.digits 10 e).length ≤ p * (10 * e) :=
      Nat.mul_le_mul_left p hdigits
    have he_le : e ≤ p * e := by
      simpa using Nat.mul_le_mul_right e hp.one_lt.le
    have henc_le : concatenateNats p e ≤ 11 * p * e := by
      calc
        concatenateNats p e = p * 10 ^ (Nat.digits 10 e).length + e := rfl
        _ ≤ p * (10 * e) + p * e := Nat.add_le_add hmul_digits he_le
        _ = 11 * p * e := by ring
    have h11 : 11 * e < 2 ^ (e - 1) := eleven_mul_lt_two_pow_pred e he8
    have hbase : 2 ^ (e - 1) ≤ p ^ (e - 1) :=
      Nat.pow_le_pow_left hp.two_le (e - 1)
    have hstrict : 11 * p * e < p ^ e := by
      calc
        11 * p * e = p * (11 * e) := by ring
        _ < p * 2 ^ (e - 1) := (Nat.mul_lt_mul_left hp.pos).2 h11
        _ ≤ p * p ^ (e - 1) := Nat.mul_le_mul_left p hbase
        _ = p ^ e := by
          calc
            p * p ^ (e - 1) = p ^ (e - 1) * p := Nat.mul_comm _ _
            _ = p ^ ((e - 1) + 1) := (pow_succ p (e - 1)).symm
            _ = p ^ e := by rw [Nat.sub_add_cancel he]
    exact (Nat.ne_of_lt (lt_of_le_of_lt henc_le hstrict)) hfix
  · have he7 : e ≤ 7 := by omega
    have hp_le_e : p ≤ e := Nat.le_of_dvd he hp_dvd_e
    interval_cases e <;> interval_cases p <;>
      norm_num [concatenateNats] at hp hfix

#print axioms OeisA67599.no_prime_power_fixed_point

end OeisA67599
