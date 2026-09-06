import D17Round31ModularSoundness

/-!
# D17 Round 32: kernel reflection for the modulus-11 filter

This file turns the first complete modular residue table used by the
`(14;17,9,3)` template search into a kernel-checkable Boolean computation.
It proves the exact 82/121 killed-residue classification modulo 11, proves
periodicity of the discriminant, and connects every killed residue class
directly to `OeisA63880.A`.
-/

namespace D17Round32

open OeisA63880
open D17Round29
open D17Round30
open D17Round31

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The discriminant polynomial evaluated directly in `ZMod 11`. -/
def discPoly11 (p q : ZMod 11) : ZMod 11 :=
  let a : ZMod 11 := 32770 * (p^17 + 1) * (q^9 + 1)
  let b : ZMod 11 :=
    32767 *
      (1 + p + p^2 + p^3 + p^4 + p^5 + p^6 + p^7 + p^8 + p^9 +
        p^10 + p^11 + p^12 + p^13 + p^14 + p^15 + p^16 + p^17) *
      (1 + q + q^2 + q^3 + q^4 + q^5 + q^6 + q^7 + q^8 + q^9)
  let c := a - b
  a^2 - 4*c^2

theorem discZ_eq_discPoly11 (p q : ℕ) :
    discZ 11 p q = discPoly11 (p : ZMod 11) (q : ZMod 11) := by
  simp [discZ, discriminant, Ccoef, Acoef, Bcoef, discPoly11, S17N, S9N]
  ring

theorem discZ_mod_11 (p q : ℕ) :
    discZ 11 p q = discZ 11 (p % 11) (q % 11) := by
  rw [discZ_eq_discPoly11, discZ_eq_discPoly11]
  apply congrArg₂ discPoly11
  · exact (ZMod.natCast_mod p 11).symm
  · exact (ZMod.natCast_mod q 11).symm

/-- Fully executable non-square checker for the fixed modulus 11. -/
def killedB11 (a b : ℕ) : Bool :=
  (List.range 11).all fun x =>
    decide (discZ 11 a b ≠ (x : ZMod 11)^2)

theorem killedB11_sound {a b : ℕ} (h : killedB11 a b = true) :
    KilledBy 11 a b := by
  intro x
  have hxmem : x.val ∈ List.range 11 := by
    simpa using x.val_lt
  unfold killedB11 at h
  have hentry := List.all_eq_true.mp h x.val hxmem
  have hne : discZ 11 a b ≠ ((x.val : ℕ) : ZMod 11)^2 := by
    simpa using hentry
  simpa only [ZMod.natCast_zmod_val] using hne

/-- Compact description of the 82 killed residue pairs modulo 11. -/
def Pattern11 (a b : ℕ) : Prop :=
  (((a = 2 ∨ a = 6) ∧ 1 ≤ b ∧ b ≤ 9) ∨
   (a ≤ 9 ∧ a ≠ 2 ∧ a ≠ 6 ∧ 2 ≤ b ∧ b ≤ 9))

/-- Closed Boolean audit of all 121 residue pairs and all 11 possible square
roots for each pair. -/
def residueTable11Check : Bool :=
  (List.range 11).all fun a =>
    (List.range 11).all fun b =>
      decide (Pattern11 a b ↔ killedB11 a b = true)

theorem residueTable11Check_true : residueTable11Check = true := by
  decide

theorem pattern11_iff_killedB11 {a b : ℕ}
    (ha : a < 11) (hb : b < 11) :
    Pattern11 a b ↔ killedB11 a b = true := by
  have h := residueTable11Check_true
  unfold residueTable11Check at h
  have haMem : a ∈ List.range 11 := by simpa using ha
  have hbMem : b ∈ List.range 11 := by simpa using hb
  have hrow := List.all_eq_true.mp h a haMem
  have hcell := List.all_eq_true.mp hrow b hbMem
  simpa using hcell

def residuePairs11 : List (ℕ × ℕ) :=
  (List.range 11).flatMap fun a =>
    (List.range 11).map fun b => (a, b)

def killedCount11 : ℕ :=
  (residuePairs11.filter fun ab => killedB11 ab.1 ab.2).length

theorem killedCount11_eq_82 : killedCount11 = 82 := by
  decide

theorem killedBy11_of_pattern {p q : ℕ}
    (hpat : Pattern11 (p % 11) (q % 11)) :
    KilledBy 11 p q := by
  have hpLt : p % 11 < 11 := Nat.mod_lt _ (by decide)
  have hqLt : q % 11 < 11 := Nat.mod_lt _ (by decide)
  have hbool : killedB11 (p % 11) (q % 11) = true :=
    (pattern11_iff_killedB11 hpLt hqLt).mp hpat
  have hres : KilledBy 11 (p % 11) (q % 11) := killedB11_sound hbool
  intro x
  rw [discZ_mod_11]
  exact hres x

/-- Every one of the 82 certified congruence classes rules out the original
A063880 equation for all later primes `r`. -/
theorem no_A_of_mod11_pattern {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)
    (hpat : Pattern11 (p % 11) (q % 11)) :
    ¬ A (Branch p q r) := by
  exact no_A_of_killedBy hp hq hr h2p hpq hqr
    (killedBy11_of_pattern hpat)

/-- Mutation control: 39 is the complement count, not the killed count. -/
theorem killedCount11_not_complement : killedCount11 ≠ 39 := by
  rw [killedCount11_eq_82]
  decide

/-- Mutation control: residue `(0,0)` is allowed rather than killed. -/
theorem residue_0_0_allowed : killedB11 0 0 = false := by
  decide

#print axioms discZ_mod_11
#print axioms killedB11_sound
#print axioms residueTable11Check_true
#print axioms killedCount11_eq_82
#print axioms killedBy11_of_pattern
#print axioms no_A_of_mod11_pattern
#print axioms killedCount11_not_complement
#print axioms residue_0_0_allowed

end D17Round32
