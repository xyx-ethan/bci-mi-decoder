import Mathlib
import FormalConjectures.OEIS.«63880»

/-!
# D17 Round 22: kernel bridge for the a=17 finite-y reduction

This file formalizes the rational-inequality bridge used in the restricted
A063880 branch `n = 2^17 * x^4 * y^3 * z^3` with `y ≤ x ≤ z`.
It does not use either research-open theorem from the upstream file.
-/

namespace D17Round22

def Phi5 (t : ℚ) : ℚ := t^4 + t^3 + t^2 + t + 1

def Phi6 (t : ℚ) : ℚ := t^2 - t + 1

def R4 (t : ℚ) : ℚ := Phi5 t / (t^4 + 1)

def R3 (t : ℚ) : ℚ := (t^2 + 1) / Phi6 t

def U (t : ℚ) : ℚ := t / (t - 1)

def Target : ℚ := 262146 / 262143

theorem phi6_pos {t : ℚ} (ht : 1 < t) : 0 < Phi6 t := by
  have ht0 : 0 < t := by linarith
  have htm1 : 0 < t - 1 := by linarith
  have hm : 0 < t * (t - 1) := mul_pos ht0 htm1
  simp only [Phi6]
  nlinarith

theorem pow4_add_one_pos (t : ℚ) : 0 < t^4 + 1 := by
  have h : 0 ≤ t^4 := by positivity
  linarith

theorem R3_pos {t : ℚ} (ht : 1 < t) : 0 < R3 t := by
  have hnum : 0 < t^2 + 1 := by positivity
  exact div_pos hnum (phi6_pos ht)

theorem R4_pos {t : ℚ} (ht : 1 < t) : 0 < R4 t := by
  have ht0 : 0 < t := by linarith
  have hnum : 0 < Phi5 t := by
    simp only [Phi5]
    positivity
  exact div_pos hnum (pow4_add_one_pos t)

theorem U_pos {t : ℚ} (ht : 1 < t) : 0 < U t := by
  exact div_pos (by linarith) (by linarith)

theorem R3_lt_U {t : ℚ} (ht : 1 < t) : R3 t < U t := by
  have hden3 : 0 < Phi6 t := phi6_pos ht
  have hdenU : 0 < t - 1 := by linarith
  simp only [R3, U]
  rw [div_lt_div_iff₀ hden3 hdenU]
  simp only [Phi6]
  ring_nf
  norm_num

theorem R4_lt_U {t : ℚ} (ht : 1 < t) : R4 t < U t := by
  have hden4 : 0 < t^4 + 1 := pow4_add_one_pos t
  have hdenU : 0 < t - 1 := by linarith
  simp only [R4, U]
  rw [div_lt_div_iff₀ hden4 hdenU]
  have hleft : Phi5 t * (t - 1) = t^5 - 1 := by
    simp only [Phi5]
    ring
  have hright : t * (t^4 + 1) = t^5 + t := by ring
  rw [hleft, hright]
  linarith

theorem U_antitone {a b : ℚ} (ha : 1 < a) (hab : a ≤ b) : U b ≤ U a := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hdenb : 0 < b - 1 := by linarith
  have hdena : 0 < a - 1 := by linarith
  simp only [U]
  rw [div_le_div_iff₀ hdenb hdena]
  nlinarith

theorem ratio_product_lt_cube {x y z : ℚ}
    (hy : 1 < y) (hyx : y ≤ x) (hxz : x ≤ z)
    (hEq : R4 x * R3 y * R3 z = Target) :
    Target < U y ^ 3 := by
  have hx : 1 < x := lt_of_lt_of_le hy hyx
  have hyz : y ≤ z := le_trans hyx hxz
  have hz : 1 < z := lt_of_lt_of_le hy hyz
  have hUx : U x ≤ U y := U_antitone hy hyx
  have hUz : U z ≤ U y := U_antitone hy hyz
  have h4 : R4 x < U y := lt_of_lt_of_le (R4_lt_U hx) hUx
  have h3y : R3 y < U y := R3_lt_U hy
  have h3z : R3 z < U y := lt_of_lt_of_le (R3_lt_U hz) hUz
  have h3yp : 0 ≤ R3 y := le_of_lt (R3_pos hy)
  have h3zp : 0 ≤ R3 z := le_of_lt (R3_pos hz)
  have hUp : 0 ≤ U y := le_of_lt (U_pos hy)
  have h12 : R4 x * R3 y < U y * U y := by
    exact mul_lt_mul h4 h3y h3yp hUp
  have hUU : 0 ≤ U y * U y := mul_nonneg hUp hUp
  have h123 : (R4 x * R3 y) * R3 z < (U y * U y) * U y := by
    exact mul_lt_mul h12 h3z h3zp hUU
  calc
    Target = (R4 x * R3 y) * R3 z := by simpa [mul_assoc] using hEq.symm
    _ < (U y * U y) * U y := h123
    _ = U y ^ 3 := by ring

theorem boundary_cube : U (262145 : ℚ) ^ 3 < Target := by
  norm_num [U, Target]

theorem finite_y_bound {x y z : ℚ}
    (hy : 1 < y) (hyx : y ≤ x) (hxz : x ≤ z)
    (hEq : R4 x * R3 y * R3 z = Target) :
    y < 262145 := by
  have hprod : Target < U y ^ 3 := ratio_product_lt_cube hy hyx hxz hEq
  by_contra hnot
  have hcy : (262145 : ℚ) ≤ y := le_of_not_gt hnot
  have hU : U y ≤ U (262145 : ℚ) := U_antitone (by norm_num) hcy
  have hcube : U y ^ 3 ≤ U (262145 : ℚ) ^ 3 := by
    gcongr
  have hb := boundary_cube
  linarith

end D17Round22
