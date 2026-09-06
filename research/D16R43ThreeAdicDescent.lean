import FormalConjectures.Research.D16R41ModularNonsquare
import FormalConjectures.Research.D16R42ThreeAdicGate

/-!
# D16 R43: one-step 3-adic descent of the discriminant

After the Round-42 gate has produced an exact quotient
`gateExpression q r m d = 3 * t`, the Round-39 discriminant is nine times a
smaller integer `descendedCore q r m d t`.  This module proves that the original
discriminant is a square if and only if the descended core is a square, and
turns the residue class `2 mod 3` of the descended core into an exact
source-system obstruction.

The result is a strict subproblem of the open A067720 conjecture and does not
assume that conjecture.
-/

namespace D16R43ThreeAdicDescent

open D16R39DiscriminantBridge
open D16R40SourceToQuadratic
open D16R41ModularNonsquare
open D16R42ThreeAdicGate

/-- The discriminant after one exact 3-adic descent. -/
def descendedCore (q r m d t : ℤ) : ℤ :=
  correction q r m d - t

/-- The residue expression controlling the second 3-adic gate. -/
def secondGateExpression (q t : ℤ) : ℤ :=
  q ^ 2 - t

/-- The first gate quotient gives an exact factorization by nine. -/
theorem discriminant_eq_nine_mul_descendedCore
    {q r m d t : ℤ}
    (hgate : gateExpression q r m d = 3 * t) :
    discriminant q r m d = 9 * descendedCore q r m d t := by
  rw [discriminant_eq_three_mul_reduced,
    reduced_eq_neg_gate_add_three_correction, hgate]
  unfold descendedCore
  ring

/-- The descended core is congruent modulo 3 to `q^2-t`. -/
theorem descendedCore_eq_secondGate_add_three_mul
    {q r m d t : ℤ}
    (hgate : gateExpression q r m d = 3 * t) :
    descendedCore q r m d t =
      secondGateExpression q t +
        3 * (6 * q * r ^ 3 + 243 * r ^ 6 - t) := by
  unfold descendedCore secondGateExpression correction gateExpression at *
  linear_combination -hgate

/-- Cast form of the preceding exact congruence. -/
theorem descendedCore_cast_three
    {q r m d t : ℤ}
    (hgate : gateExpression q r m d = 3 * t) :
    (descendedCore q r m d t : ZMod 3) =
      (secondGateExpression q t : ZMod 3) := by
  rw [descendedCore_eq_secondGate_add_three_mul hgate]
  norm_num

/-- Under the first-gate quotient, squarehood descends exactly by a factor 9. -/
theorem square_discriminant_iff_descendedCore_square
    {q r m d t : ℤ}
    (hgate : gateExpression q r m d = 3 * t) :
    (∃ z : ℤ, z ^ 2 = discriminant q r m d) ↔
      ∃ w : ℤ, w ^ 2 = descendedCore q r m d t := by
  constructor
  · rintro ⟨z, hz⟩
    have hzsq : (3 : ℤ) ∣ z ^ 2 := by
      rw [hz, discriminant_eq_three_mul_reduced]
      exact dvd_mul_right 3 (reducedDiscriminant q r m d)
    have hprime : Prime (3 : ℤ) := by norm_num
    have hz3 : (3 : ℤ) ∣ z := hprime.dvd_of_dvd_pow hzsq
    rcases hz3 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hdisc := discriminant_eq_nine_mul_descendedCore hgate
    rw [hw] at hz
    nlinarith [hz, hdisc]
  · rintro ⟨w, hw⟩
    refine ⟨3 * w, ?_⟩
    rw [discriminant_eq_nine_mul_descendedCore hgate, ← hw]
    ring

/-- Residue 2 modulo 3 is a complete finite nonsquare certificate. -/
theorem residue_two_noSquareMod {a : ℤ}
    (ha : (a : ZMod 3) = 2) :
    NoSquareMod 3 a := by
  intro x
  rw [ha]
  fin_cases x <;> decide

/-- The second gate failure excludes every integer root of the Round-38
quadratic, even though the first Round-42 gate has passed. -/
theorem secondGate_failure_no_integer_root
    {q r m d t : ℤ}
    (hgate : gateExpression q r m d = 3 * t)
    (hfail : (secondGateExpression q t : ZMod 3) = 2) :
    ¬ ∃ p : ℤ, quadratic q r m d p = 0 := by
  rintro ⟨p, hp⟩
  have hdiscSquare := root_gives_square hp
  have hcoreSquare :=
    (square_discriminant_iff_descendedCore_square hgate).mp hdiscSquare
  have hcoreResidue :
      (descendedCore q r m d t : ZMod 3) = 2 := by
    rw [descendedCore_cast_three hgate]
    exact hfail
  exact (no_integer_square_of_noSquareMod
    (residue_two_noSquareMod hcoreResidue)) hcoreSquare

/-- Composing with R40: a failed second gate excludes the complete source
system. -/
theorem secondGate_failure_excludes_sourceSystem
    {q r s d m t : ℤ}
    (hd : d ≠ 0)
    (hgate : gateExpression q r m d = 3 * t)
    (hfail : (secondGateExpression q t : ZMod 3) = 2) :
    ¬ ∃ p u : ℤ, SourceSystem p q r s d m u := by
  rintro ⟨p, u, hsource⟩
  exact secondGate_failure_no_integer_root hgate hfail
    ⟨p, sourceSystem_gives_quadratic hsource hd⟩

/-! ## Exact controls -/

/-- The positive R40 source instance passes the first gate with quotient 42. -/
theorem positive_gate_quotient :
    gateExpression (-7) 1 5 4 = 3 * 42 := by
  norm_num [gateExpression]

/-- Its descended core is the genuine square `22^2`. -/
theorem positive_descendedCore :
    descendedCore (-7) 1 5 4 42 = 484 := by
  norm_num [descendedCore, correction]

theorem positive_descendedCore_square :
    ∃ w : ℤ, w ^ 2 = descendedCore (-7) 1 5 4 42 := by
  exact ⟨22, by norm_num [positive_descendedCore]⟩

/-- A row that passes the first gate but fails the second one. -/
theorem negative_gate_quotient :
    gateExpression (-2) 1 0 1 = 3 * 2 := by
  norm_num [gateExpression]

theorem negative_descendedCore :
    descendedCore (-2) 1 0 1 2 = 689 := by
  norm_num [descendedCore, correction]

theorem negative_secondGate_failure :
    (secondGateExpression (-2) 2 : ZMod 3) = 2 := by
  norm_num [secondGateExpression]

/-- The original discriminant is positive and divisible by 9, so this control
is genuinely beyond the Round-42 first gate. -/
theorem negative_discriminant :
    discriminant (-2) 1 0 1 = 6201 := by
  norm_num [discriminant]

theorem negative_firstGate_passes :
    (3 : ℤ) ∣ gateExpression (-2) 1 0 1 := by
  exact ⟨2, negative_gate_quotient⟩

/-- End-to-end second-gate exclusion for every value of the unused source
parameter `s`. -/
theorem negative_sourceSystem_excluded (s : ℤ) :
    ¬ ∃ p u : ℤ, SourceSystem p (-2) 1 s 1 0 u := by
  apply secondGate_failure_excludes_sourceSystem
  · norm_num
  · exact negative_gate_quotient
  · exact negative_secondGate_failure

end D16R43ThreeAdicDescent
