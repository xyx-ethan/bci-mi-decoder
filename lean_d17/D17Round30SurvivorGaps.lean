import D17Round29FiniteBox

/-!
# D17 Round 30: terminal square-gap reflection for the `(14;17,9,3)` template

This file connects `OeisA63880.A (2^14 * p^17 * q^9 * r^3)` to the
reciprocal-quadratic discriminant and kernel-checks the non-square gap
certificates for the final modular survivors.
-/

namespace D17Round30

open OeisA63880
open D17Round29

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def Acoef (p q : ℕ) : ℤ :=
  32770 * ((p : ℤ)^17 + 1) * ((q : ℤ)^9 + 1)

def Bcoef (p q : ℕ) : ℤ :=
  32767 * (S17N p : ℤ) * (S9N q : ℤ)

def Ccoef (p q : ℕ) : ℤ := Acoef p q - Bcoef p q

def discriminant (p q : ℕ) : ℤ :=
  Acoef p q ^ 2 - 4 * Ccoef p q ^ 2

def IsIntSquare (d : ℤ) : Prop := ∃ s : ℤ, d = s^2

theorem reciprocal_quadratic_discriminant
    {a c r : ℤ} (h : c * r^2 - a * r + c = 0) :
    a^2 - 4*c^2 = (2*c*r-a)^2 := by
  calc
    a^2 - 4*c^2 =
        (2*c*r-a)^2 - 4*c*(c*r^2-a*r+c) := by ring
    _ = (2*c*r-a)^2 := by rw [h]; ring

theorem A_branch_reciprocal_quadratic {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    Ccoef p q * (r : ℤ)^2 - Acoef p q * (r : ℤ) + Ccoef p q = 0 := by
  have hnat := A_branch_uncancelled hp hq hr h2p hpq hqr hA
  have hz :
      (32767 : ℤ) * (S17N p : ℤ) * (S9N q : ℤ) * (S3N r : ℤ) =
        (32770 : ℤ) * (1 + (p : ℤ)^17) * (1 + (q : ℤ)^9) *
          (1 + (r : ℤ)^3) := by
    exact_mod_cast hnat
  have hz' :
      Bcoef p q * (S3N r : ℤ) =
        Acoef p q * (1 + (r : ℤ)^3) := by
    simpa [Acoef, Bcoef, add_comm] using hz
  have hfac :
      ((r : ℤ) + 1) * (Bcoef p q * ((r : ℤ)^2 + 1)) =
        ((r : ℤ) + 1) *
          (Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1)) := by
    calc
      ((r : ℤ) + 1) * (Bcoef p q * ((r : ℤ)^2 + 1)) =
          Bcoef p q * (S3N r : ℤ) := by
        simp [S3N]
        ring
      _ = Acoef p q * (1 + (r : ℤ)^3) := hz'
      _ = ((r : ℤ) + 1) *
          (Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1)) := by ring
  have hr1 : (r : ℤ) + 1 ≠ 0 := by positivity
  have hcancel :
      Bcoef p q * ((r : ℤ)^2 + 1) =
        Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1) :=
    mul_left_cancel₀ hr1 hfac
  calc
    Ccoef p q * (r : ℤ)^2 - Acoef p q * (r : ℤ) + Ccoef p q =
        Acoef p q * ((r : ℤ)^2 - (r : ℤ) + 1) -
          Bcoef p q * ((r : ℤ)^2 + 1) := by
      simp [Ccoef]
      ring
    _ = 0 := by rw [← hcancel]; ring

theorem A_branch_discriminant_square {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hA : A (Branch p q r)) :
    IsIntSquare (discriminant p q) := by
  have hquad := A_branch_reciprocal_quadratic hp hq hr h2p hpq hqr hA
  refine ⟨2 * Ccoef p q * (r : ℤ) - Acoef p q, ?_⟩
  exact reciprocal_quadratic_discriminant hquad

theorem not_int_square_of_strict_gap {d root : ℤ}
    (hroot : 0 ≤ root) (hlow : root^2 < d)
    (hhigh : d < (root + 1)^2) :
    ¬ IsIntSquare d := by
  rintro ⟨s, hs⟩
  by_cases hle : |s| ≤ root
  · have hsle : s^2 ≤ root^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hroot] using hle
    rw [hs] at hlow
    exact (not_lt_of_ge hsle) hlow
  · have hlt : root < |s| := lt_of_not_ge hle
    have hnext : root + 1 ≤ |s| := by omega
    have hr1 : 0 ≤ root + 1 := by linarith
    have hsge : (root + 1)^2 ≤ s^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hr1] using hnext
    rw [hs] at hhigh
    exact (not_lt_of_ge hsge) hhigh

theorem first_survivor_discriminant_not_square :
    ¬ IsIntSquare (discriminant 10937 15592301) := by
  apply not_int_square_of_strict_gap
      (root :=
        818347833861125442897845732474389010616735354660377299604036371203836906345440226395147286649879437309723233420586451247084293118039308006)
  · norm_num
  · norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]
  · norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]

theorem no_A_first_survivor {r : ℕ}
    (hp : Nat.Prime 10937) (hq : Nat.Prime 15592301) (hr : r.Prime)
    (hqr : 15592301 < r) :
    ¬ A (Branch 10937 15592301 r) := by
  intro hA
  apply first_survivor_discriminant_not_square
  exact A_branch_discriminant_square hp hq hr (by norm_num) (by norm_num) hqr hA

#print axioms A_branch_reciprocal_quadratic
#print axioms A_branch_discriminant_square
#print axioms not_int_square_of_strict_gap
#print axioms first_survivor_discriminant_not_square
#print axioms no_A_first_survivor

end D17Round30
