import D13R12Encoding

/-! Global exponent and prime bounds for the f=1 branch. -/
namespace D13.R13

/-- Exponential growth used to remove every exponent at least ten. -/
theorem growth_three (e : ℕ) (he : 10 ≤ e) :
    1034*e+4 < (3 : ℕ)^(e-1) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
      have he1 : 1 ≤ e := by omega
      have hh : (3 : ℕ)^e = 3*3^(e-1) := by
        conv_lhs => rw [show e=(e-1)+1 by omega, pow_succ]
        ring
      simp only [Nat.add_sub_cancel]
      rw [hh]
      nlinarith

/-- The last digit rules out the prime two in the f=1 branch. -/
theorem f_one_prime_ge_three (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) : 3 ≤ p := by
  have hp2 := hp.two_le
  by_contra h
  have hp_eq : p=2 := by omega
  subst p
  obtain ⟨_, hEq⟩ := D13.R12.f_one_equation 2 q e hp hq hpq he hfix
  have hv : 2 ∣ (2 : ℕ)^e := dvd_pow_self 2 he.ne'
  have hd : 2 ∣ (2 : ℕ)^e-10 := Nat.dvd_sub hv (by decide)
  have hn : 2 ∣ ((2 : ℕ)^e-10)*q := dvd_mul_of_dvd_left hd q
  rw [hEq] at hn
  have hzero := Nat.mod_eq_zero_of_dvd hn
  norm_num [Nat.add_mod, Nat.mul_mod] at hzero

/-- The quotient window alone gives an exponent bound, once p is at least three. -/
theorem exponent_bound_of_window (p e : ℕ) (hp : 3 ≤ p) (he : 0 < e)
    (hpow : 10 < p^e)
    (hw : p^e-10 ≤ 100*(p*10^(Nat.digits 10 e).length+e)+1) : e ≤ 9 := by
  have hdigit := Nat.base_pow_length_digits_le 10 e (by decide) he.ne'
  have hmul := Nat.mul_le_mul_left (100*p) hdigit
  have hsub : p^e-10+10=p^e := Nat.sub_add_cancel hpow.le
  have hupper : p^e ≤ 1000*p*e+100*e+11 := by nlinarith
  have heq : p^e = p*p^(e-1) := by
    conv_lhs => rw [show e=(e-1)+1 by omega, pow_succ]
    ring
  have hr : p^(e-1) ≤ 1034*e+4 := by
    by_contra h
    have hr' : 1034*e+5 ≤ p^(e-1) := by omega
    have hh := Nat.mul_le_mul_left p hr'
    have hpe := Nat.mul_le_mul_right e hp
    rw [heq] at hupper
    nlinarith
  have hb : (3 : ℕ)^(e-1) ≤ p^(e-1) := pow_le_pow_left' hp (e-1)
  by_contra h
  have he10 : 10 ≤ e := by omega
  have hg := growth_three e he10
  omega

/-- Any actual f=1 fixed point lies in a finite (p,e) box. q stays unbounded. -/
theorem f_one_parameter_box (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    2 ≤ e ∧ e ≤ 9 ∧ 3 ≤ p ∧ p ≤ 1000 := by
  have hp3 := f_one_prime_ge_three p q e hp hq hpq he hfix
  obtain ⟨hpow, hEq⟩ := D13.R12.f_one_equation p q e hp hq hpq he hfix
  have hr := D13.R12.f_one_reduction p q e hp hq hpq he hfix
  dsimp only at hr
  obtain ⟨hD, hCD, hDC, _⟩ := hr
  have hw : p^e-10 ≤ 100*(p*10^(Nat.digits 10 e).length+e)+1 := by
    nlinarith [hDC]
  have he9 := exponent_bound_of_window p e hp3 he hpow hw
  have he2 : 2 ≤ e := by
    by_contra h
    have he1 : e=1 := by omega
    subst e
    norm_num at hCD
    omega
  have hd : (Nat.digits 10 e).length=1 := by
    rw [Nat.digits_of_lt 10 e he.ne' (by omega)]
    rfl
  rw [hd] at hw
  norm_num only [pow_one] at hw
  have hsub : p^e-10+10=p^e := Nat.sub_add_cancel hpow.le
  have hupper : p^e ≤ 1000*p+911 := by nlinarith
  have hsq : p^2 ≤ p^e := Nat.pow_le_pow_right hp.pos he2
  have hpmax : p ≤ 1000 := by
    by_contra h
    have hp1001 : 1001 ≤ p := by omega
    have hm := Nat.mul_le_mul_left p hp1001
    nlinarith
  exact ⟨he2, he9, hp3, hpmax⟩

end D13.R13
