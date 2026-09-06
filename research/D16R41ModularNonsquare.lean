import FormalConjectures.Research.D16R40SourceToQuadratic

/-!
# D16 R41: finite modular nonsquare certificates for the A067720 branch

This module converts a finite `ZMod n` nonsquare check into an integer
nonsquare theorem and then composes that theorem with the Round-40 source
system bridge.  It does not assume the open A067720 conjecture.
-/

namespace D16R41ModularNonsquare

open D16R39DiscriminantBridge
open D16R40SourceToQuadratic

/-- `a` has no square root modulo `n`. -/
def NoSquareMod (n : ℕ) (a : ℤ) : Prop :=
  ∀ x : ZMod n, x ^ 2 ≠ (a : ZMod n)

/-- A nontrivial finite modulus witnessing that `a` is not an integer square. -/
def HasModularNonsquareCertificate (a : ℤ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ NoSquareMod n a

/-- If an integer is a square, its reduction modulo every modulus is a square. -/
theorem no_integer_square_of_noSquareMod {n : ℕ} {a : ℤ}
    (hns : NoSquareMod n a) :
    ¬ ∃ z : ℤ, z ^ 2 = a := by
  rintro ⟨z, hz⟩
  apply hns (z : ZMod n)
  have hcast := congrArg (fun t : ℤ => (t : ZMod n)) hz
  simpa using hcast

/-- A finite modular nonsquare certificate is sound over the integers. -/
theorem no_integer_square_of_certificate {a : ℤ}
    (hcert : HasModularNonsquareCertificate a) :
    ¬ ∃ z : ℤ, z ^ 2 = a := by
  rcases hcert with ⟨n, _, hns⟩
  exact no_integer_square_of_noSquareMod hns

/-- An actual integer square cannot carry a modular nonsquare certificate. -/
theorem square_has_no_modular_certificate (z : ℤ) :
    ¬ HasModularNonsquareCertificate (z ^ 2) := by
  intro hcert
  exact no_integer_square_of_certificate hcert ⟨z, rfl⟩

/-- A finite modular certificate now excludes the complete Round-40 source
system, rather than only the eliminated quadratic. -/
theorem modular_certificate_excludes_sourceSystem
    {q r s d m : ℤ}
    (hd : d ≠ 0)
    (hcert :
      HasModularNonsquareCertificate (discriminant q r m d)) :
    ¬ ∃ p u : ℤ, SourceSystem p q r s d m u := by
  exact nonsquare_excludes_sourceSystem hd
    (no_integer_square_of_certificate hcert)

/-! ## Exact finite controls -/

/-- The concrete test discriminant used below. -/
theorem concrete_discriminant :
    discriminant 1 1 0 1 = 6732 := by
  norm_num [discriminant]

/-- Complete kernel enumeration of the five residues proves that 6732 is not a
square modulo 5. -/
theorem certificate_6732 :
    HasModularNonsquareCertificate 6732 := by
  refine ⟨5, by norm_num, ?_⟩
  intro x
  fin_cases x <;> norm_num

/-- End-to-end control: the modular certificate excludes this exact source
system instance for all integer unknowns `p,u`. -/
theorem concrete_sourceSystem_excluded :
    ¬ ∃ p u : ℤ, SourceSystem p 1 1 2 1 0 u := by
  apply modular_certificate_excludes_sourceSystem
  · norm_num
  · simpa [concrete_discriminant] using certificate_6732

/-- Mutation control: 4 is a square modulo 5, so the corresponding false
certificate is rejected. -/
theorem square_residue_mutation_rejected :
    ¬ NoSquareMod 5 4 := by
  intro h
  exact h (2 : ZMod 5) (by norm_num)

/-- The positive Round-40 source instance has square discriminant `66²`. -/
theorem positive_source_discriminant :
    discriminant (-7) 1 5 4 = 66 ^ 2 := by
  norm_num [discriminant]

/-- Consequently, sound modular certification cannot reject that positive
control. -/
theorem positive_source_not_falsely_certified :
    ¬ HasModularNonsquareCertificate
      (discriminant (-7) 1 5 4) := by
  rw [positive_source_discriminant]
  exact square_has_no_modular_certificate 66

end D16R41ModularNonsquare
