import D23Round22
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity

namespace D23Round23

open Zsqrtd
open D23Round21 D23Round22

local notation "ℤ[i]" => GaussianInt

/-- A prime `p ≡ 3 (mod 4)` is inert in the Gaussian integers; therefore any
Gaussian integer of norm `p²` lies on a coordinate axis. -/
theorem inertPrime_beta_axis
    (p : ℕ) (A B : ℤ)
    (hp : p.Prime)
    (hmod : p % 4 = 3)
    (hbeta : normSq A B = (p : ℤ) * (p : ℤ)) :
    A = 0 ∨ B = 0 := by
  let z : ℤ[i] := ⟨A, B⟩
  have hpi : Prime (p : ℤ[i]) :=
    @GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p ⟨hp⟩ hmod
  have hnorm : z.norm = (p : ℤ) * (p : ℤ) := by
    simp [z, Zsqrtd.norm, normSq] at hbeta ⊢
    exact hbeta
  have hprod : z * star z = (p : ℤ[i]) * (p : ℤ[i]) := by
    calc
      z * star z = (z.norm : ℤ[i]) := (Zsqrtd.norm_eq_mul_conj z).symm
      _ = (((p : ℤ) * (p : ℤ) : ℤ) : ℤ[i]) := by rw [hnorm]
      _ = (p : ℤ[i]) * (p : ℤ[i]) := by norm_num
  have hpdivprod : (p : ℤ[i]) ∣ z * star z := by
    refine ⟨(p : ℤ[i]), ?_⟩
    exact hprod
  have hpz : (p : ℤ[i]) ∣ z := by
    rcases hpi.dvd_mul.mp hpdivprod with hz | hstarz
    · exact hz
    · rcases hstarz with ⟨w, hw⟩
      refine ⟨star w, ?_⟩
      have hs := congrArg star hw
      simpa using hs
  rcases hpz with ⟨w, hw⟩
  have hA : A = (p : ℤ) * w.re := by
    have hre := congrArg Zsqrtd.re hw
    simpa [z] using hre
  have hB : B = (p : ℤ) * w.im := by
    have him := congrArg Zsqrtd.im hw
    simpa [z] using him
  have hpzpos : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  have hp2pos : 0 < (p : ℤ) * (p : ℤ) := mul_pos hpzpos hpzpos
  have hscaled := hbeta
  rw [hA, hB] at hscaled
  simp only [normSq] at hscaled
  have hfactor :
      ((p : ℤ) * (p : ℤ)) * (w.re * w.re + w.im * w.im - 1) = 0 := by
    nlinarith
  have hsum : w.re * w.re + w.im * w.im = 1 := by
    have hp2ne : (p : ℤ) * (p : ℤ) ≠ 0 := ne_of_gt hp2pos
    have := (mul_eq_zero.mp hfactor).resolve_left hp2ne
    nlinarith
  have hcoord : w.re = 0 ∨ w.im = 0 := by
    by_contra h
    push Not at h
    have hrepos : 0 < w.re * w.re := mul_self_pos.mpr h.1
    have himpos : 0 < w.im * w.im := mul_self_pos.mpr h.2
    have hreone : 1 ≤ w.re * w.re := by omega
    have himone : 1 ≤ w.im * w.im := by omega
    nlinarith
  rcases hcoord with hre | him
  · left
    rw [hA, hre]
    ring
  · right
    rw [hB, him]
    ring

/-- Combining inertness with the Round-22 axis theorem removes the ad hoc axis
hypothesis from the `p ≡ 3 mod 4` prime subclass. -/
theorem inertPrime_fullRank_scalar_norm_cases
    (p : ℕ) (q A B wx wy tx ty rx ry sx sy : ℤ)
    (hp : p.Prime)
    (hmod : p % 4 = 3)
    (hpq : (p : ℤ) ≤ q)
    (hbeta : normSq A B = (p : ℤ) * (p : ℤ))
    (hdet : detZ rx ry sx sy ≠ 0)
    (henergy :
      q * normSq wx wy + normSq tx ty +
          2 * normSq rx ry + 2 * normSq sx sy =
        4 * (A * wx + B * wy)) :
    normSq wx wy = 1 ∨ normSq wx wy = 2 ∨ normSq wx wy = 4 ∨
    normSq wx wy = 5 ∨ normSq wx wy = 9 ∨ normSq wx wy = 10 := by
  have haxis := inertPrime_beta_axis p A B hp hmod hbeta
  have hpInt : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  exact axisBeta_scalar_norm_cases
    (p : ℤ) q A B wx wy tx ty rx ry sx sy
    hpInt hpq hbeta hdet haxis henergy

end D23Round23
