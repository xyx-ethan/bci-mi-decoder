import Mathlib
import FormalConjectures.OEIS.«67599»

/-!
# D13 Round 25: kernel closure of the 21,098-case structural certificate

This file checks the finite two-prime structural domain inherited from D13 Round 19.
It does not invoke `OeisA67599.conjecture` and does not assert the global absence of
fixed points.  The finite domain and the six modular obstructions are evaluated by
ordinary kernel reduction; no native decision procedure is used.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D13Round25

structure Candidate where
  p : ℕ
  q : ℕ
  e : ℕ
  f : ℕ
  deriving DecidableEq, Repr

def decimalDigits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).length

def encoded (c : Candidate) : ℕ :=
  ((c.p * 10 ^ decimalDigits c.e + c.e) * 10 ^ decimalDigits c.q + c.q) * 10 + c.f

def primePowerValue (c : Candidate) : ℕ :=
  c.p ^ c.e * c.q ^ c.f

def qBound : ℕ → ℕ
  | 3 => 216
  | 4 => 39
  | 5 => 16
  | 6 => 9
  | 7 => 6
  | 8 => 5
  | 9 => 4
  | _ => 0

def primesUpTo (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter fun p => decide p.Prime

def exponents : List ℕ :=
  (List.range 14).map fun e => e + 1

def f2Candidates : List Candidate :=
  ((primesUpTo 2240).filter fun q => decide (2 < q)).flatMap fun q =>
    exponents.map fun e => ⟨2, q, e, 2⟩

def candidatesForF (f : ℕ) : List Candidate :=
  let ps := primesUpTo (qBound f)
  ps.flatMap fun q =>
    (ps.filter fun p => decide (p < q)).flatMap fun p =>
      exponents.map fun e => ⟨p, q, e, f⟩

def higherCandidates : List Candidate :=
  (List.range 7).flatMap fun j => candidatesForF (j + 3)

def candidateDomain : List Candidate :=
  f2Candidates ++ higherCandidates

/-- A candidate is eliminated when one of the six fixed moduli separates the
prime-power value from its decimal encoding. -/
def Eliminated (c : Candidate) : Prop :=
  encoded c % 10 ≠ primePowerValue c % 10 ∨
  encoded c % 9 ≠ primePowerValue c % 9 ∨
  encoded c % 13 ≠ primePowerValue c % 13 ∨
  encoded c % 7 ≠ primePowerValue c % 7 ∨
  encoded c % 11 ≠ primePowerValue c % 11 ∨
  encoded c % 37 ≠ primePowerValue c % 37

/-- Equality would force equality modulo every modulus, so any certified modular
separation rules out the exact equation. -/
theorem eliminated_implies_ne (c : Candidate) (h : Eliminated c) :
    encoded c ≠ primePowerValue c := by
  intro heq
  rcases h with h | h | h | h | h | h
  all_goals
    apply h
    rw [heq]

/-- Exact size of the `f = 2` branch. -/
theorem f2_candidate_count : f2Candidates.length = 4648 := by
  decide

/-- Exact size of the `3 ≤ f ≤ 9` branch. -/
theorem higher_candidate_count : higherCandidates.length = 16450 := by
  decide

/-- Exact size of the complete inherited structural domain. -/
theorem candidate_count : candidateDomain.length = 21098 := by
  decide

/-- Kernel-checked six-modulus certificate for every one of the 21,098 cases. -/
theorem all_candidates_eliminated : candidateDomain.Forall Eliminated := by
  decide

/-- Final finite-domain theorem. -/
theorem no_solution_in_candidate_domain (c : Candidate)
    (hc : c ∈ candidateDomain) : encoded c ≠ primePowerValue c := by
  have hElim : Eliminated c :=
    (List.forall_iff_forall_mem.mp all_candidates_eliminated) c hc
  exact eliminated_implies_ne c hElim

def agreesThrough11 (c : Candidate) : Bool :=
  decide (
    encoded c % 10 = primePowerValue c % 10 ∧
    encoded c % 9 = primePowerValue c % 9 ∧
    encoded c % 13 = primePowerValue c % 13 ∧
    encoded c % 7 = primePowerValue c % 7 ∧
    encoded c % 11 = primePowerValue c % 11)

def pre37Survivors : List Candidate :=
  candidateDomain.filter agreesThrough11

/-- The first five moduli leave exactly one tuple. -/
theorem pre37_survivor_exact :
    pre37Survivors = [⟨37, 53, 14, 3⟩] := by
  decide

/-- Modulo 37 the last tuple has residues 29 and 0, respectively. -/
theorem last_survivor_killed :
    encoded ⟨37, 53, 14, 3⟩ % 37 = 29 ∧
    primePowerValue ⟨37, 53, 14, 3⟩ % 37 = 0 := by
  decide

-- Semantic and mutation controls for decimal order and the upstream boundaries.
example : OeisA67599.a 0 = 0 := by decide
example : OeisA67599.a 1 = 0 := by decide
example : encoded ⟨3, 5, 1, 1⟩ = 3151 := by decide
example : encoded ⟨3, 5, 1, 1⟩ ≠ 3511 := by decide
example : qBound 3 = 216 := by decide
example : qBound 2 = 0 := by decide

end D13Round25
