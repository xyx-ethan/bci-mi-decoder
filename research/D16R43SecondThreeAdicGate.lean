import FormalConjectures.Research.D16R42ThreeAdicGate
import FormalConjectures.Research.D16R41ModularNonsquare

/-!
# D16 R43: the second 3-adic lift gate

Round 42 proves that a square discriminant must satisfy the first gate
`3 ∣ q * (q + r*m - r*d^2)`.  This module refines that condition one
3-adic level: among the first-gate residue classes, the lift residue `3 mod 9`
forces the discriminant to be `18 mod 27`, which is not a square.

The module is a strict auxiliary result for the open A067720 conjecture.
It neither assumes that conjecture nor claims that the Round-38 row generator
has already been recovered.
-/

namespace D16R43SecondThreeAdicGate

open D16R39DiscriminantBridge
open D16R40SourceToQuadratic
open D16R41ModularNonsquare
open D16R42ThreeAdicGate

/-- The mod-9 expression controlling the next 3-adic lift. -/
def liftGateExpression (q r m d : ℤ) : ℤ :=
  q * (q + 4 * r * m - 4 * r * d ^ 2)

/-- The correction term in the exact mod-27 discriminant identity. -/
def liftCorrection (q r : ℤ) : ℤ :=
  6 * q * r ^ 3 + 243 * r ^ 6

/-- The unique bad lift class among the three classes that pass the first
3-adic gate: the lift expression is congruent to 3 modulo 9. -/
def BadLiftResidue (q r m d : ℤ) : Prop :=
  ∃ t : ℤ, liftGateExpression q r m d = 9 * t + 3

/-- Exact identity behind the second 3-adic gate. -/
theorem discriminant_eq_neg_three_lift_add_twentyseven
    (q r m d : ℤ) :
    discriminant q r m d =
      -3 * liftGateExpression q r m d + 27 * liftCorrection q r := by
  unfold discriminant liftGateExpression liftCorrection
  ring

/-- The residue 18 is not a square modulo 27. -/
theorem noSquare18Mod27 : NoSquareMod 27 18 := by
  intro x
  fin_cases x <;> decide

/-- A bad lift residue forces the discriminant to be 18 modulo 27. -/
theorem badLiftResidue_discriminant_mod27
    {q r m d : ℤ}
    (hbad : BadLiftResidue q r m d) :
    (discriminant q r m d : ZMod 27) = 18 := by
  rcases hbad with ⟨t, ht⟩
  have hdelta :
      discriminant q r m d =
        27 * (liftCorrection q r - t - 1) + 18 := by
    rw [discriminant_eq_neg_three_lift_add_twentyseven, ht]
    ring
  have hcast := congrArg (fun z : ℤ => (z : ZMod 27)) hdelta
  simpa using hcast

/-- A bad lift residue is a proof-carrying modular nonsquare certificate. -/
theorem badLiftResidue_noSquareMod27
    {q r m d : ℤ}
    (hbad : BadLiftResidue q r m d) :
    NoSquareMod 27 (discriminant q r m d) := by
  intro x hx
  exact noSquare18Mod27 x <| by
    calc
      x ^ 2 = (discriminant q r m d : ZMod 27) := hx
      _ = 18 := badLiftResidue_discriminant_mod27 hbad

/-- Consequently the discriminant cannot be an integer square. -/
theorem badLiftResidue_noIntegerSquare
    {q r m d : ℤ}
    (hbad : BadLiftResidue q r m d) :
    ¬ ∃ z : ℤ, z ^ 2 = discriminant q r m d := by
  exact no_integer_square_of_noSquareMod
    (badLiftResidue_noSquareMod27 hbad)

/-- A bad lift residue excludes every integer root of the Round-38 quadratic. -/
theorem badLiftResidue_noIntegerRoot
    {q r m d : ℤ}
    (hbad : BadLiftResidue q r m d) :
    ¬ ∃ p : ℤ, quadratic q r m d p = 0 := by
  exact nonsquare_no_integer_root
    (badLiftResidue_noIntegerSquare hbad)

/-- Composing with Round 40: a bad lift residue excludes the entire source
system for every pair of integer unknowns `p,u`. -/
theorem badLiftResidue_excludes_sourceSystem
    {q r s d m : ℤ}
    (hd : d ≠ 0)
    (hbad : BadLiftResidue q r m d) :
    ¬ ∃ p u : ℤ, SourceSystem p q r s d m u := by
  exact nonsquare_excludes_sourceSystem hd
    (badLiftResidue_noIntegerSquare hbad)

/-- A genuine square discriminant can never lie in the bad lift class. -/
theorem square_discriminant_not_badLift
    {q r m d : ℤ}
    (hsq : ∃ z : ℤ, z ^ 2 = discriminant q r m d) :
    ¬ BadLiftResidue q r m d := by
  intro hbad
  exact badLiftResidue_noIntegerSquare hbad hsq

/-! ## Exact controls -/

/-- First exact bad lift: `-15 = 9*(-2)+3`. -/
theorem negative_control_badLift :
    BadLiftResidue 1 1 0 2 := by
  refine ⟨-2, ?_⟩
  norm_num [liftGateExpression]

/-- Its discriminant is exactly 6768, hence 18 modulo 27. -/
theorem negative_control_values :
    liftGateExpression 1 1 0 2 = -15 ∧
      discriminant 1 1 0 2 = 6768 := by
  norm_num [liftGateExpression, discriminant]

/-- End-to-end exact exclusion of the synthetic bad-lift source row. -/
theorem negative_control_sourceSystem_excluded (s : ℤ) :
    ¬ ∃ p u : ℤ, SourceSystem p 1 1 s 2 0 u := by
  exact badLiftResidue_excludes_sourceSystem (by norm_num)
    negative_control_badLift

/-- The nondegenerate positive Round-40 source instance lies in the allowed
lift class 6 modulo 9. -/
theorem positive_control_lift_six :
    liftGateExpression (-7) 1 5 4 = 9 * 39 + 6 := by
  norm_num [liftGateExpression]

/-- Its genuine square discriminant is not falsely rejected. -/
theorem positive_control_not_badLift :
    ¬ BadLiftResidue (-7) 1 5 4 := by
  apply square_discriminant_not_badLift
  refine ⟨66, ?_⟩
  norm_num [discriminant]

/-- The other allowed lift class, zero modulo 9, occurs when `q=0`. -/
theorem zero_lift_class :
    liftGateExpression 0 1 0 0 = 0 := by
  norm_num [liftGateExpression]

end D16R43SecondThreeAdicGate
