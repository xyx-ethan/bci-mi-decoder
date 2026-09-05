import D13R11
import D13R9Reconstruction

/-! General two-prime encoding, with arbitrary positive exponents. -/
namespace D13.R12

open OeisA67599

theorem factors_two_prime_powers (p q e f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p^e*q^f).primeFactorsList = List.replicate e p ++ List.replicate f q := by
  apply D13.R9.factors_from_sorted
  · simp
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h := List.eq_of_mem_replicate hx
      simpa only [h] using hp
    · have h := List.eq_of_mem_replicate hx
      simpa only [h] using hq
  · rw [List.pairwise_append]
    refine ⟨by simp, by simp, ?_⟩
    intro x hx y hy
    have hx' := List.eq_of_mem_replicate hx
    have hy' := List.eq_of_mem_replicate hy
    simpa only [hx', hy'] using hpq.le

theorem dedup_two_blocks (p q e f : ℕ)
    (hpq : p ≠ q) (he : 0 < e) (hf : 0 < f) :
    (List.replicate e p ++ List.replicate f q).dedup = [p,q] := by
  have hd : List.Disjoint (List.replicate e p) (List.replicate f q) := by
    intro x hx hy
    exact hpq ((List.eq_of_mem_replicate hx).symm.trans (List.eq_of_mem_replicate hy))
  rw [hd.dedup_append, List.replicate_dedup he.ne', List.replicate_dedup hf.ne']
  rfl

theorem encoding_two_prime_powers (p q e f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (he : 0 < e) (hf : 0 < f) :
    OeisA67599.a (p^e*q^f) =
      ((p * 10^(Nat.digits 10 e).length + e) *
        10^(Nat.digits 10 q).length + q) * 10^(Nat.digits 10 f).length + f := by
  have hpe : 1 < p^e := one_lt_pow₀ hp.one_lt he.ne'
  have hqf : 0 < q^f := pow_pos hq.pos f
  have hn : ¬ p^e*q^f < 2 := by nlinarith
  have hne : p ≠ q := ne_of_lt hpq
  have hne' : q ≠ p := ne_of_gt hpq
  unfold OeisA67599.a
  rw [if_neg hn, factors_two_prime_powers p q e f hp hq hpq]
  dsimp only
  rw [dedup_two_blocks p q e f hne he hf]
  simp [OeisA67599.concatenateNats, List.count_append, List.count_replicate, hne, hne']

theorem fixed_two_prime_powers_iff (p q e f : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (he : 0 < e) (hf : 0 < f) :
    OeisA67599.a (p^e*q^f) = p^e*q^f ↔
      ((p * 10^(Nat.digits 10 e).length + e) *
        10^(Nat.digits 10 q).length + q) * 10^(Nat.digits 10 f).length + f = p^e*q^f := by
  rw [encoding_two_prime_powers p q e f hp hq hpq he hf]

theorem f_one_equation (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    10 < p^e ∧
    (p^e-10)*q = 10*(p*10^(Nat.digits 10 e).length+e)*10^(Nat.digits 10 q).length+1 := by
  have hc := encoding_two_prime_powers p q e 1 hp hq hpq he (by decide)
  norm_num at hc
  rw [hc] at hfix
  have hpow : 10 < p^e := by
    by_contra h
    have hm := Nat.mul_le_mul_right q (le_of_not_gt h)
    nlinarith
  have hsub : p^e-10+10=p^e := Nat.sub_add_cancel hpow.le
  constructor
  · exact hpow
  · nlinarith [hfix]

/-- Necessary size window; the exponent is the actual number of decimal digits. -/
theorem quotient_window (c d q : ℕ) (hq : 0 < q) (hc : 0 < c)
    (hd : 0 < d) (heq : d*q = c*10^(Nat.digits 10 q).length+1) :
    c < d ∧ d ≤ 10*c+1 := by
  let k := (Nat.digits 10 q).length
  have hk : 0 < k := by
    apply (Nat.lt_digits_length_iff (by decide : 1 < (10 : ℕ)) q).2
    simpa using hq
  have hu : q < (10 : ℕ)^k :=
    (Nat.digits_length_le_iff (by decide : 1 < (10 : ℕ)) q).1 (le_refl _)
  have hl : (10 : ℕ)^(k-1) ≤ q := by
    apply (Nat.lt_digits_length_iff (by decide : 1 < (10 : ℕ)) q).1
    change k-1 < k
    omega
  have hy : 0 < (10 : ℕ)^(k-1) := by positivity
  have hpow : (10 : ℕ)^k = 10*10^(k-1) := by
    conv_lhs => rw [show k=(k-1)+1 by omega, pow_succ]
    ring
  change d*q=c*10^k+1 at heq
  constructor
  · by_contra h
    have hdc : d ≤ c := le_of_not_gt h
    have hm := Nat.mul_le_mul_right q hdc
    have hm' := Nat.mul_lt_mul_of_pos_left hu hc
    omega
  · by_contra h
    have hdc : 10*c+2 ≤ d := by omega
    have hm := Nat.mul_le_mul_right ((10 : ℕ)^(k-1)) hdc
    have hm' := Nat.mul_le_mul_left d hl
    rw [hpow] at heq
    nlinarith

theorem f_one_reduction (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    let C := 10*(p*10^(Nat.digits 10 e).length+e)
    let D := p^e-10
    0 < D ∧ C < D ∧ D ≤ 10*C+1 ∧
      q = (C*10^(Nat.digits 10 q).length+1)/D := by
  dsimp only
  obtain ⟨hpow, heq⟩ := f_one_equation p q e hp hq hpq he hfix
  have hd : 0 < p^e-10 := by omega
  have hc : 0 < 10*(p*10^(Nat.digits 10 e).length+e) := by positivity
  obtain ⟨hcd, hdc⟩ := quotient_window _ _ _ hq.pos hc hd heq
  refine ⟨hd, hcd, hdc, ?_⟩
  rw [← heq, Nat.mul_div_cancel_left _ hd]

end D13.R12
