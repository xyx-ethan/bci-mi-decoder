import D13R13Power
import D13R9Reconstruction

/-! Close the exponent-residue bridge for the whole f=1 two-prime branch. -/
namespace D13.R14

/-- Reduce an exponent modulo a certified multiplicative period. -/
theorem pow_mod_period (M b m k : ℕ) (hm : 0 < m)
    (hper : Nat.ModEq M (b^m) 1) :
    Nat.ModEq M (b^k) (b^(k % m)) := by
  have hdecomp : k % m + m * (k / m) = k := Nat.mod_add_div k m
  have hp : Nat.ModEq M ((b^m)^(k/m)) 1 := by
    simpa only [one_pow] using Nat.ModEq.pow (k/m) hper
  conv_lhs => rw [← hdecomp, pow_add, pow_mul]
  simpa only [mul_one] using (Nat.ModEq.refl (b^(k%m))).mul hp

theorem q1_exponent_residue (k : ℕ)
    (hdiv : 2391 ∣ 740*10^k+1) : k % 199 = 136 := by
  have h797 : 797 ∣ 740*10^k+1 :=
    dvd_trans (by decide : 797 ∣ 2391) hdiv
  have hzero : Nat.ModEq 797 (740*10^k+1) 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using Nat.mod_eq_zero_of_dvd h797
  have hper : Nat.ModEq 797 ((10:ℕ)^199) 1 := by norm_num [Nat.ModEq]
  have hp := pow_mod_period 797 10 199 k (by decide) hper
  have hred : Nat.ModEq 797 (740*10^k+1) (740*10^(k%199)+1) :=
    ((Nat.ModEq.refl 740).mul hp).add (Nat.ModEq.refl 1)
  have hz : Nat.ModEq 797 (740*10^(k%199)+1) 0 := hred.symm.trans hzero
  let s := k % 199
  have hs : s < 199 := Nat.mod_lt _ (by decide)
  change (740 * 10^s + 1) % 797 = 0 at hz
  change s = 136
  interval_cases s <;> norm_num at hz ⊢

theorem q2_exponent_mod_six (k : ℕ)
    (hdiv : 2177 ∣ 370*10^k+1) : k % 6 = 0 := by
  have h7 : 7 ∣ 370*10^k+1 := dvd_trans (by decide : 7 ∣ 2177) hdiv
  have hzero : Nat.ModEq 7 (370*10^k+1) 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using Nat.mod_eq_zero_of_dvd h7
  have hper : Nat.ModEq 7 ((10:ℕ)^6) 1 := by norm_num [Nat.ModEq]
  have hp := pow_mod_period 7 10 6 k (by decide) hper
  have hred : Nat.ModEq 7 (370*10^k+1) (370*10^(k%6)+1) :=
    ((Nat.ModEq.refl 370).mul hp).add (Nat.ModEq.refl 1)
  have hz : Nat.ModEq 7 (370*10^(k%6)+1) 0 := hred.symm.trans hzero
  let s := k % 6
  have hs : s < 6 := Nat.mod_lt _ (by decide)
  change (370 * 10^s + 1) % 7 = 0 at hz
  change s = 0
  interval_cases s <;> norm_num at hz ⊢

theorem q2_exponent_mod_155 (k : ℕ)
    (hdiv : 2177 ∣ 370*10^k+1) : k % 155 = 46 := by
  have h311 : 311 ∣ 370*10^k+1 := dvd_trans (by decide : 311 ∣ 2177) hdiv
  have hzero : Nat.ModEq 311 (370*10^k+1) 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using Nat.mod_eq_zero_of_dvd h311
  have hper : Nat.ModEq 311 ((10:ℕ)^155) 1 := by norm_num [Nat.ModEq]
  have hp := pow_mod_period 311 10 155 k (by decide) hper
  have hred : Nat.ModEq 311 (370*10^k+1) (370*10^(k%155)+1) :=
    ((Nat.ModEq.refl 370).mul hp).add (Nat.ModEq.refl 1)
  have hz : Nat.ModEq 311 (370*10^(k%155)+1) 0 := hred.symm.trans hzero
  let s := k % 155
  have hs : s < 155 := Nat.mod_lt _ (by decide)
  change (370 * 10^s + 1) % 311 = 0 at hz
  change s = 46
  interval_cases s <;> norm_num at hz ⊢

theorem q2_exponent_residue (k : ℕ)
    (hdiv : 2177 ∣ 370*10^k+1) : k % 930 = 666 := by
  have h6 := q2_exponent_mod_six k hdiv
  have h155 := q2_exponent_mod_155 k hdiv
  have hk6 := Nat.mod_add_div k 6
  have hk155 := Nat.mod_add_div k 155
  have hk930 := Nat.mod_add_div k 930
  have hr : k % 930 < 930 := Nat.mod_lt _ (by decide)
  omega

/-- Any fixed point in the f=1 branch is literally one of the two q-families. -/
theorem f_one_fixed_to_residual (p q e : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (he : 0 < e)
    (hfix : OeisA67599.a (p^e*q) = p^e*q) :
    (∃ t, p=7 ∧ e=4 ∧ q=D13.q1 t) ∨
    (∃ t, p=3 ∧ e=7 ∧ q=D13.q2 t) := by
  rcases D13.R13.f_one_two_prime_exponent_pairs p q e hp hq hpq he hfix with h | h
  · rcases h with ⟨rfl,rfl⟩
    have hEq := (D13.R12.f_one_equation 7 q 4 hp hq hpq (by decide) hfix).2
    norm_num at hEq
    have hdiv : 2391 ∣ 740*10^(Nat.digits 10 q).length+1 := ⟨q,hEq.symm⟩
    have hres := q1_exponent_residue (Nat.digits 10 q).length hdiv
    let t := (Nat.digits 10 q).length / 199
    have hdec := Nat.mod_add_div (Nat.digits 10 q).length 199
    have hk : (Nat.digits 10 q).length = 136+199*t := by
      dsimp [t]
      omega
    have hq1 := D13.r9_q1_exact t
    rw [hk] at hEq
    have hm : 2391*q = 2391*D13.q1 t := hEq.trans hq1.symm
    have hqq : q=D13.q1 t := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2391) hm
    exact Or.inl ⟨t,rfl,rfl,hqq⟩
  · rcases h with ⟨rfl,rfl⟩
    have hEq := (D13.R12.f_one_equation 3 q 7 hp hq hpq (by decide) hfix).2
    norm_num at hEq
    have hdiv : 2177 ∣ 370*10^(Nat.digits 10 q).length+1 := ⟨q,hEq.symm⟩
    have hres := q2_exponent_residue (Nat.digits 10 q).length hdiv
    let t := (Nat.digits 10 q).length / 930
    have hdec := Nat.mod_add_div (Nat.digits 10 q).length 930
    have hk : (Nat.digits 10 q).length = 666+930*t := by
      dsimp [t]
      omega
    have hq2 := D13.r9_q2_exact t
    rw [hk] at hEq
    have hm : 2177*q = 2177*D13.q2 t := hEq.trans hq2.symm
    have hqq : q=D13.q2 t := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2177) hm
    exact Or.inr ⟨t,rfl,rfl,hqq⟩

/-- Exact classification of existence in the entire f=1 two-prime branch. -/
theorem f_one_fixed_exists_iff_residual_prime :
    (∃ p q e : ℕ, p.Prime ∧ q.Prime ∧ p<q ∧ 0<e ∧
      OeisA67599.a (p^e*q)=p^e*q) ↔
    (∃ t, (D13.q1 t).Prime) ∨ (∃ t, (D13.q2 t).Prime) := by
  constructor
  · rintro ⟨p,q,e,hp,hq,hpq,he,hfix⟩
    rcases f_one_fixed_to_residual p q e hp hq hpq he hfix with h | h
    · rcases h with ⟨t,rfl,rfl,rfl⟩
      exact Or.inl ⟨t,hq⟩
    · rcases h with ⟨t,rfl,rfl,rfl⟩
      exact Or.inr ⟨t,hq⟩
  · rintro (⟨t,ht⟩ | ⟨t,ht⟩)
    · have h7 : (7:ℕ).Prime := by norm_num
      have hlt : 7 < D13.q1 t := lt_trans (by decide) (D13.q1_large t)
      exact ⟨7,D13.q1 t,4,h7,ht,hlt,by decide,D13.R9.q1_prime_gives_fixed_point t ht⟩
    · have h3 : (3:ℕ).Prime := by norm_num
      have hlt : 3 < D13.q2 t := lt_trans (by decide) (D13.q2_large t)
      exact ⟨3,D13.q2 t,7,h3,ht,hlt,by decide,D13.R9.q2_prime_gives_fixed_point t ht⟩

end D13.R14
