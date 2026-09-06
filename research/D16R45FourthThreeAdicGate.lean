import FormalConjectures.Research.D16R44ThirdThreeAdicGate

/-!
# D16 R45: normalized fourth 3-adic gate

Round 44 leaves the zero-lift class `27 ∣ liftGateExpression` together with
the unit class `liftGateExpression ≡ 6 (mod 9)`.  In the zero-lift class the
discriminant has a factor `81`.  This module proves an exact square descent:
a square discriminant descends to a square of the normalized quotient.  The
normalized residue `2 (mod 3)` is therefore impossible.

A finite theorem also checks the complete local residue classifier modulo 243:
for the abstract residues `H mod 81` and `J mod 3`, the surviving R42--R45
conditions are exactly the square residues of `-3H + 81J` modulo 243.

The results are strict auxiliary theorems for the open A067720 conjecture.  They
do not assume the conjecture and do not claim recovery of the Round-38 row
generator.
-/

namespace D16R45FourthThreeAdicGate

open D16R39DiscriminantBridge
open D16R40SourceToQuadratic
open D16R41ModularNonsquare
open D16R42ThreeAdicGate
open D16R43SecondThreeAdicGate
open D16R44ThirdThreeAdicGate

/-- In the Round-44 zero branch, the normalized discriminant is `J-u` when
`H=27u`. -/
def fourthNormalized (q r u : ℤ) : ℤ :=
  thirdLiftCorrection q r - u

/-- The unique bad normalized residue class modulo 3 in the Round-44 zero
branch. -/
def BadFourthLiftResidue (q r m d : ℤ) : Prop :=
  ∃ u t : ℤ,
    liftGateExpression q r m d = 27 * u ∧
      fourthNormalized q r u = 3 * t + 2

/-- Exact extraction of the factor 81 in the zero-lift branch. -/
theorem discriminant_eq_eightyone_mul_normalized
    {q r m d u : ℤ}
    (hu : liftGateExpression q r m d = 27 * u) :
    discriminant q r m d = 81 * fourthNormalized q r u := by
  rw [discriminant_eq_neg_three_lift_add_eightyone, hu]
  unfold fourthNormalized
  ring

/-- If the discriminant is an integer square in the zero-lift branch, then its
quotient by 81 is again an integer square. -/
theorem square_discriminant_descends
    {q r m d u : ℤ}
    (hu : liftGateExpression q r m d = 27 * u)
    (hsq : ∃ z : ℤ, z ^ 2 = discriminant q r m d) :
    ∃ w : ℤ, w ^ 2 = fourthNormalized q r u := by
  rcases hsq with ⟨z, hz⟩
  have hz81 : z ^ 2 = 81 * fourthNormalized q r u := by
    calc
      z ^ 2 = discriminant q r m d := hz
      _ = 81 * fourthNormalized q r u :=
        discriminant_eq_eightyone_mul_normalized hu
  have hprime : Prime (3 : ℤ) := by norm_num
  have hthree_sq : (3 : ℤ) ∣ z ^ 2 := by
    refine ⟨27 * fourthNormalized q r u, ?_⟩
    rw [hz81]
    ring
  have hthree_z : (3 : ℤ) ∣ z := hprime.dvd_of_dvd_pow hthree_sq
  rcases hthree_z with ⟨z₁, hz₁⟩
  have hz₁_sq : z₁ ^ 2 = 9 * fourthNormalized q r u := by
    rw [hz₁] at hz81
    nlinarith [hz81]
  have hthree_z₁_sq : (3 : ℤ) ∣ z₁ ^ 2 := by
    refine ⟨3 * fourthNormalized q r u, ?_⟩
    rw [hz₁_sq]
    ring
  have hthree_z₁ : (3 : ℤ) ∣ z₁ := hprime.dvd_of_dvd_pow hthree_z₁_sq
  rcases hthree_z₁ with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  rw [hw] at hz₁_sq
  nlinarith [hz₁_sq]

/-- The only nonsquare residue modulo 3. -/
theorem noSquareTwoModThree : NoSquareMod 3 2 := by
  intro x
  fin_cases x <;> decide

/-- A bad fourth lift cannot have square normalized quotient. -/
theorem badFourthLift_normalized_noIntegerSquare
    {q r m d u t : ℤ}
    (hu : liftGateExpression q r m d = 27 * u)
    (hk : fourthNormalized q r u = 3 * t + 2) :
    ¬ ∃ w : ℤ, w ^ 2 = fourthNormalized q r u := by
  rintro ⟨w, hw⟩
  have hwt : w ^ 2 = 3 * t + 2 := by
    calc
      w ^ 2 = fourthNormalized q r u := hw
      _ = 3 * t + 2 := hk
  have hcast := congrArg (fun y : ℤ => (y : ZMod 3)) hwt
  have hthree : (3 : ZMod 3) = 0 := by decide
  have hcast' : (w : ZMod 3) ^ 2 = 2 := by
    calc
      (w : ZMod 3) ^ 2 = 3 * (t : ZMod 3) + 2 := hcast
      _ = 2 := by rw [hthree]; simp
  exact noSquareTwoModThree (w : ZMod 3) hcast'

/-- The bad normalized class forces residue 162 modulo 243. -/
theorem badFourthLift_discriminant_mod243
    {q r m d : ℤ}
    (hbad : BadFourthLiftResidue q r m d) :
    (discriminant q r m d : ZMod 243) = 162 := by
  rcases hbad with ⟨u, t, hu, hk⟩
  have hdelta :
      discriminant q r m d = 243 * t + 162 := by
    rw [discriminant_eq_eightyone_mul_normalized hu, hk]
    ring
  change (discriminant q r m d : ZMod 243) =
    ((162 : ℤ) : ZMod 243)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨-t, ?_⟩
  rw [hdelta]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- Complete kernel check that 162 is not a square modulo 243. -/
theorem noSquare162Mod243 : NoSquareMod 243 162 := by
  intro x
  fin_cases x <;> decide

/-- The bad normalized class is a modular nonsquare certificate. -/
theorem badFourthLift_noSquareMod243
    {q r m d : ℤ}
    (hbad : BadFourthLiftResidue q r m d) :
    NoSquareMod 243 (discriminant q r m d) := by
  intro x hx
  exact noSquare162Mod243 x <| by
    calc
      x ^ 2 = (discriminant q r m d : ZMod 243) := hx
      _ = 162 := badFourthLift_discriminant_mod243 hbad

/-- The bad normalized class rules out an integer-square discriminant. -/
theorem badFourthLift_noIntegerSquare
    {q r m d : ℤ}
    (hbad : BadFourthLiftResidue q r m d) :
    ¬ ∃ z : ℤ, z ^ 2 = discriminant q r m d := by
  exact no_integer_square_of_noSquareMod
    (badFourthLift_noSquareMod243 hbad)

/-- Independent descent proof of the same integer-square exclusion. -/
theorem badFourthLift_noIntegerSquare_via_descent
    {q r m d : ℤ}
    (hbad : BadFourthLiftResidue q r m d) :
    ¬ ∃ z : ℤ, z ^ 2 = discriminant q r m d := by
  rintro hsq
  rcases hbad with ⟨u, t, hu, hk⟩
  exact badFourthLift_normalized_noIntegerSquare hu hk
    (square_discriminant_descends hu hsq)

/-- A bad fourth lift excludes every integer root of the Round-38 quadratic. -/
theorem badFourthLift_noIntegerRoot
    {q r m d : ℤ}
    (hbad : BadFourthLiftResidue q r m d) :
    ¬ ∃ p : ℤ, quadratic q r m d p = 0 := by
  exact nonsquare_no_integer_root
    (badFourthLift_noIntegerSquare hbad)

/-- Composing with Round 40, a bad fourth lift excludes the complete source
system. -/
theorem badFourthLift_excludes_sourceSystem
    {q r s d m : ℤ}
    (hd : d ≠ 0)
    (hbad : BadFourthLiftResidue q r m d) :
    ¬ ∃ p u : ℤ, SourceSystem p q r s d m u := by
  exact nonsquare_excludes_sourceSystem hd
    (badFourthLift_noIntegerSquare hbad)

/-- A genuine square discriminant cannot lie in the bad fourth-lift class. -/
theorem square_discriminant_not_badFourthLift
    {q r m d : ℤ}
    (hsq : ∃ z : ℤ, z ^ 2 = discriminant q r m d) :
    ¬ BadFourthLiftResidue q r m d := by
  intro hbad
  exact badFourthLift_noIntegerSquare hbad hsq

/-! ## Complete abstract residue classifier -/

/-- The discriminant residue determined by `H mod 81` and `J mod 3`. -/
def localDelta243 (h : Fin 81) (j : Fin 3) : ZMod 243 :=
  ((-3 * (h.1 : ℤ) + 81 * (j.1 : ℤ) : ℤ) : ZMod 243)

/-- The combined R42--R45 compatibility condition on the two local residues.
The subtraction is safe in `Nat`, since `j+3 ≥ 3 > h/27`. -/
def LocalCompatible243 (h : Fin 81) (j : Fin 3) : Prop :=
  h.1 % 9 = 6 ∨
    (h.1 % 27 = 0 ∧ (j.1 + 3 - h.1 / 27) % 3 ≠ 2)

/-- Executable square-root search over the finite ring `ZMod 243`. -/
def hasSquareRoot243 (a : ZMod 243) : Bool :=
  (Finset.univ : Finset (ZMod 243)).toList.any fun x =>
    decide (x ^ 2 = a)

/-- The executable square-root search is propositionally exact. -/
theorem hasSquareRoot243_eq_true_iff (a : ZMod 243) :
    hasSquareRoot243 a = true ↔ ∃ x : ZMod 243, x ^ 2 = a := by
  simp [hasSquareRoot243]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Complete finite Boolean classification of all 81×3 abstract local residue
pairs. -/
theorem completeLocalBooleanClassification :
    ∀ h : Fin 81, ∀ j : Fin 3,
      hasSquareRoot243 (localDelta243 h j) = true ↔
        LocalCompatible243 h j := by
  intro h j
  fin_cases h <;> fin_cases j <;> decide

/-- Complete finite classification of all 81×3 abstract local residue pairs. -/
theorem completeLocalResidueClassification :
    ∀ h : Fin 81, ∀ j : Fin 3,
      (∃ x : ZMod 243, x ^ 2 = localDelta243 h j) ↔
        LocalCompatible243 h j := by
  intro h j
  rw [← hasSquareRoot243_eq_true_iff]
  exact completeLocalBooleanClassification h j

/-! ## Exact controls -/

/-- Synthetic bad normalized lift: `H=0` and `J=89=3*29+2`. -/
theorem bad_control : BadFourthLiftResidue 4 1 0 1 := by
  refine ⟨0, 29, ?_, ?_⟩
  · norm_num [liftGateExpression]
  · norm_num [fourthNormalized, thirdLiftCorrection]

/-- Exact values for the bad control. -/
theorem bad_control_values :
    liftGateExpression 4 1 0 1 = 0 ∧
      fourthNormalized 4 1 0 = 89 ∧
      discriminant 4 1 0 1 = 7209 := by
  norm_num [liftGateExpression, fourthNormalized,
    thirdLiftCorrection, discriminant]

/-- End-to-end source-system exclusion for the bad control. -/
theorem bad_control_sourceSystem_excluded (s : ℤ) :
    ¬ ∃ p u : ℤ, SourceSystem p 4 1 s 1 0 u := by
  exact badFourthLift_excludes_sourceSystem (by norm_num) bad_control

/-- A genuine square zero-lift control descends from `90²` to `10²`. -/
theorem square_control_values :
    liftGateExpression 9 1 (-2) 1 = 27 * (-1) ∧
      fourthNormalized 9 1 (-1) = 10 ^ 2 ∧
      discriminant 9 1 (-2) 1 = 90 ^ 2 := by
  norm_num [liftGateExpression, fourthNormalized,
    thirdLiftCorrection, discriminant]

/-- The square control is not falsely rejected. -/
theorem square_control_not_bad :
    ¬ BadFourthLiftResidue 9 1 (-2) 1 := by
  apply square_discriminant_not_badFourthLift
  refine ⟨90, ?_⟩
  norm_num [discriminant]

/-- The square-control descent is checked independently of the bad predicate. -/
theorem square_control_descends :
    ∃ w : ℤ, w ^ 2 = fourthNormalized 9 1 (-1) := by
  apply square_discriminant_descends
  · norm_num [liftGateExpression]
  · refine ⟨90, ?_⟩
    norm_num [discriminant]

end D16R45FourthThreeAdicGate
