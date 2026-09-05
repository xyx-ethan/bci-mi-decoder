import D13R13Bounds

/-! Finish the finite seven-branch sieve for the actual f=1 encoding. -/
namespace D13.R13

theorem no_prime_square_times_prime (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    OeisA67599.a (p^2*q) ≠ p^2*q := by
  intro hfix
  have hpow := (D13.R12.f_one_equation p q 2 hp hq hpq (by decide) hfix).1
  have hc := D13.R12.encoding_two_prime_powers p q 2 1 hp hq hpq (by decide) (by decide)
  norm_num at hc
  rw [hc] at hfix
  have hmod := congrArg (fun x : ℕ => x % 3) hfix
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hr : p%3=0 ∨ p%3=1 ∨ p%3=2 := by omega
  rcases hr with h | h | h
  · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases hp.eq_one_or_self_of_dvd 3 hd with hbad | heq
    · norm_num at hbad
    · have heqp : p=3 := heq.symm
      subst p
      norm_num at hpow
  · norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h] at hmod
    omega
  · norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h] at hmod
    omega

theorem f_one_prime_ne_five (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) : p ≠ 5 := by
  intro h
  subst p
  obtain ⟨_, hEq⟩ := D13.R12.f_one_equation 5 q e hp hq hpq he hfix
  have hv : 5 ∣ (5 : ℕ)^e := dvd_pow_self 5 he.ne'
  have hd : 5 ∣ (5 : ℕ)^e-10 := Nat.dvd_sub hv (by decide)
  have hn : 5 ∣ ((5 : ℕ)^e-10)*q := dvd_mul_of_dvd_left hd q
  rw [hEq] at hn
  have hzero := Nat.mod_eq_zero_of_dvd hn
  norm_num [Nat.add_mod, Nat.mul_mod] at hzero

theorem f_one_small_box (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    3 ≤ e ∧ e ≤ 9 ∧ 3 ≤ p ∧ p ≤ 32 := by
  obtain ⟨he2, he9, hp3, _⟩ := f_one_parameter_box p q e hp hq hpq he hfix
  have he3 : 3 ≤ e := by
    by_contra h
    have heq : e=2 := by omega
    subst e
    exact no_prime_square_times_prime p q hp hq hpq hfix
  have hd : (Nat.digits 10 e).length=1 := by
    rw [Nat.digits_of_lt 10 e he.ne' (by omega)]
    rfl
  obtain ⟨hpow, _⟩ := D13.R12.f_one_equation p q e hp hq hpq he hfix
  have hr := D13.R12.f_one_reduction p q e hp hq hpq he hfix
  dsimp only at hr
  obtain ⟨_, _, hw, _⟩ := hr
  rw [hd] at hw
  norm_num only [pow_one] at hw
  have hsub : p^e-10+10=p^e := Nat.sub_add_cancel hpow.le
  have hupper : p^e ≤ 1000*p+911 := by nlinarith
  have hcube : p^3 ≤ p^e := Nat.pow_le_pow_right hp.pos he3
  have hp32 : p ≤ 32 := by
    by_contra h
    have hp33 : 33 ≤ p := by omega
    have hs : (33 : ℕ)^2 ≤ p^2 := pow_le_pow_left' hp33 2
    norm_num at hs
    have hm := Nat.mul_le_mul_left p hs
    rw [show p^3=p*p^2 by ring] at hcube
    nlinarith
  exact ⟨he3, he9, hp3, hp32⟩

/-- The finite check is split into small numeral cases; no native evaluator is used. -/
theorem finite_seven_parameters (p q e k : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hp32 : p ≤ 32) (hp5 : p ≠ 5)
    (he3 : 3 ≤ e) (he9 : e ≤ 9)
    (hL : 10*(p*10+e) < p^e-10)
    (hU : p^e-10 ≤ 10*(10*(p*10+e))+1)
    (hEq : (p^e-10)*q=10*(p*10+e)*10^k+1) :
    (p=3 ∧ e=6) ∨ (p=3 ∧ e=7) ∨ (p=7 ∧ e=4) ∨
    (p=11 ∧ e=3) ∨ (p=17 ∧ e=3) ∨ (p=23 ∧ e=3) ∨ (p=29 ∧ e=3) := by
  interval_cases p <;> norm_num at hp
  all_goals interval_cases e <;> norm_num at hp5 hL hU ⊢
  all_goals
    have hz := congrArg (fun x : ℕ => x % 3) hEq
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hz

theorem f_one_seven_branches (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    (p=3 ∧ e=6) ∨ (p=3 ∧ e=7) ∨ (p=7 ∧ e=4) ∨
    (p=11 ∧ e=3) ∨ (p=17 ∧ e=3) ∨ (p=23 ∧ e=3) ∨ (p=29 ∧ e=3) := by
  obtain ⟨he3, he9, hp3, hp32⟩ := f_one_small_box p q e hp hq hpq he hfix
  have hp5 := f_one_prime_ne_five p q e hp hq hpq he hfix
  have hd : (Nat.digits 10 e).length=1 := by
    rw [Nat.digits_of_lt 10 e he.ne' (by omega)]
    rfl
  have hEq := (D13.R12.f_one_equation p q e hp hq hpq he hfix).2
  have hr := D13.R12.f_one_reduction p q e hp hq hpq he hfix
  dsimp only at hr
  obtain ⟨_, hL, hU, _⟩ := hr
  rw [hd] at hEq hL hU
  norm_num only [pow_one] at hEq hL hU
  exact finite_seven_parameters p q e (Nat.digits 10 q).length hp hp3 hp32 hp5 he3 he9 hL hU hEq

end D13.R13
