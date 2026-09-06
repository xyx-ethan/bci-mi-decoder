#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

CASES = [
    ("q1_3", 740, 733, 2391),
    ("q2_0", 370, 666, 2177),
]

def bit_list(n: int) -> list[bool]:
    assert n >= 0
    if n == 0:
        return []
    return [c == "1" for c in bin(n)[:1:-1]]

def lean_bool_list(bits: list[bool]) -> str:
    vals = ["true" if b else "false" for b in bits]
    lines = []
    for i in range(0, len(vals), 20):
        lines.append("  " + ", ".join(vals[i:i + 20]))
    return "[\n" + ",\n".join(lines) + "\n]"

records = {}
for name, A, E, D in CASES:
    numerator = A * 10 ** E + 1
    assert numerator % D == 0
    n = numerator // D
    assert n > 2 and n % 2 == 1
    residue = pow(2, n - 1, n)
    assert residue != 1
    bits = bit_list(n - 1)
    assert sum((1 if b else 0) << i for i, b in enumerate(bits)) == n - 1
    records[name] = {
        "A": A,
        "E": E,
        "D": D,
        "n": str(n),
        "digits": len(str(n)),
        "exponent_bits_lsb_first": len(bits),
        "fermat_base": 2,
        "fermat_residue": str(residue),
    }

TEMPLATE = "import Mathlib\nimport FormalConjectures.OEIS.«67599»\n\n/-!\n# D13 Round 24: exact Fermat certificates for the two critical residuals\n\nThis file proves that the persistent residual quotients `q1 3` and `q2 0`\nare not prime.  It does not invoke the research-open A067599 conjecture.\nThe modular powers are checked by a kernel-reducible binary algorithm.\n-/\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace D13Round24\n\ndef Q (A a b D t : ℕ) : ℕ := (A * 10 ^ (a + b * t) + 1) / D\n\ndef q1 (t : ℕ) : ℕ := Q 740 136 199 2391 t\n\ndef q2 (t : ℕ) : ℕ := Q 370 666 930 2177 t\n\ndef q1Critical : ℕ := __N1__\n\ndef q2Critical : ℕ := __N2__\n\ndef q1FermatResidue : ℕ := __R1__\n\ndef q2FermatResidue : ℕ := __R2__\n\n/-- Interpret a least-significant-bit-first Boolean list as a natural number. -/\ndef evalBits : List Bool → ℕ\n  | [] => 0\n  | b :: bs => (if b then 1 else 0) + 2 * evalBits bs\n\n/-- Exact modular binary exponentiation over a least-significant-bit-first bit list. -/\ndef powModBits (a n : ℕ) : List Bool → ℕ\n  | [] => 1 % n\n  | b :: bs =>\n      let q := powModBits ((a * a) % n) n bs\n      if b then (a * q) % n else q\n\ntheorem powModBits_sound (a n : ℕ) (bits : List Bool) :\n    a ^ evalBits bits ≡ powModBits a n bits [MOD n] := by\n  induction bits generalizing a with\n  | nil =>\n      simp [evalBits, powModBits, Nat.ModEq]\n  | cons b bs ih =>\n      have hs : a * a ≡ (a * a) % n [MOD n] := by\n        simp [Nat.ModEq]\n      have hrec :\n          ((a * a) % n) ^ evalBits bs ≡\n            powModBits ((a * a) % n) n bs [MOD n] :=\n        ih ((a * a) % n)\n      have hsq :\n          (a * a) ^ evalBits bs ≡\n            powModBits ((a * a) % n) n bs [MOD n] :=\n        (hs.pow (evalBits bs)).trans hrec\n      have heven :\n          a ^ (2 * evalBits bs) ≡\n            powModBits ((a * a) % n) n bs [MOD n] := by\n        simpa [two_mul, pow_add, mul_pow] using hsq\n      cases b with\n      | false =>\n          simpa [evalBits, powModBits] using heven\n      | true =>\n          let q := powModBits ((a * a) % n) n bs\n          have hmul : a * a ^ (2 * evalBits bs) ≡ a * q [MOD n] :=\n            (Nat.ModEq.refl a).mul heven\n          have hred : a * q ≡ (a * q) % n [MOD n] := by\n            simp [Nat.ModEq]\n          have htrue := hmul.trans hred\n          simpa [q, evalBits, powModBits, pow_succ', Nat.add_comm] using htrue\n\ndef q1ExponentBits : List Bool := __BITS1__\n\ndef q2ExponentBits : List Bool := __BITS2__\n\ntheorem q1_formula : q1 3 = q1Critical := by\n  norm_num [q1, Q, q1Critical]\n\ntheorem q2_formula : q2 0 = q2Critical := by\n  norm_num [q2, Q, q2Critical]\n\ntheorem q1_bits_value : evalBits q1ExponentBits = q1Critical - 1 := by\n  decide\n\ntheorem q2_bits_value : evalBits q2ExponentBits = q2Critical - 1 := by\n  decide\n\ntheorem q1_powmod_value :\n    powModBits 2 q1Critical q1ExponentBits = q1FermatResidue := by\n  decide\n\ntheorem q2_powmod_value :\n    powModBits 2 q2Critical q2ExponentBits = q2FermatResidue := by\n  decide\n\ntheorem q1_fermat_modEq :\n    2 ^ (q1Critical - 1) ≡ q1FermatResidue [MOD q1Critical] := by\n  have h := powModBits_sound 2 q1Critical q1ExponentBits\n  rw [q1_bits_value, q1_powmod_value] at h\n  exact h\n\ntheorem q2_fermat_modEq :\n    2 ^ (q2Critical - 1) ≡ q2FermatResidue [MOD q2Critical] := by\n  have h := powModBits_sound 2 q2Critical q2ExponentBits\n  rw [q2_bits_value, q2_powmod_value] at h\n  exact h\n\ntheorem not_prime_of_fermat_failure {n r : ℕ}\n    (hcop : Nat.Coprime 2 n)\n    (hres : 2 ^ (n - 1) ≡ r [MOD n])\n    (hfail : ¬ r ≡ 1 [MOD n]) : ¬ n.Prime := by\n  intro hp\n  have hcopInt : IsCoprime (2 : ℤ) (n : ℤ) := hcop.isCoprime\n  have hfInt : (2 : ℤ) ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] :=\n    Int.ModEq.pow_card_sub_one_eq_one hp hcopInt\n  have hfNat : 2 ^ (n - 1) ≡ 1 [MOD n] := by\n    exact_mod_cast hfInt\n  exact hfail (hres.symm.trans hfNat)\n\ntheorem q1Critical_coprime_two : Nat.Coprime 2 q1Critical := by\n  decide\n\ntheorem q2Critical_coprime_two : Nat.Coprime 2 q2Critical := by\n  decide\n\ntheorem q1_fermat_failure :\n    ¬ q1FermatResidue ≡ 1 [MOD q1Critical] := by\n  norm_num [Nat.ModEq, q1FermatResidue, q1Critical]\n\ntheorem q2_fermat_failure :\n    ¬ q2FermatResidue ≡ 1 [MOD q2Critical] := by\n  norm_num [Nat.ModEq, q2FermatResidue, q2Critical]\n\ntheorem q1Critical_not_prime : ¬ Nat.Prime q1Critical :=\n  not_prime_of_fermat_failure q1Critical_coprime_two q1_fermat_modEq q1_fermat_failure\n\ntheorem q2Critical_not_prime : ¬ Nat.Prime q2Critical :=\n  not_prime_of_fermat_failure q2Critical_coprime_two q2_fermat_modEq q2_fermat_failure\n\ntheorem q1_3_not_prime : ¬ Nat.Prime (q1 3) := by\n  rw [q1_formula]\n  exact q1Critical_not_prime\n\ntheorem q2_0_not_prime : ¬ Nat.Prime (q2 0) := by\n  rw [q2_formula]\n  exact q2Critical_not_prime\n\n-- Positive, negative, and mutation controls for the upstream decimal encoding.\nexample : OeisA67599.a 0 = 0 := by decide\nexample : OeisA67599.a 1 = 0 := by decide\nexample : OeisA67599.concatenateNats 31 51 = 3151 := by\n  norm_num [OeisA67599.concatenateNats]\nexample : OeisA67599.concatenateNats 31 51 ≠ 3511 := by\n  norm_num [OeisA67599.concatenateNats]\n\nend D13Round24\n"
source = TEMPLATE
source = source.replace("__N1__", records["q1_3"]["n"])
source = source.replace("__N2__", records["q2_0"]["n"])
source = source.replace("__R1__", records["q1_3"]["fermat_residue"])
source = source.replace("__R2__", records["q2_0"]["fermat_residue"])
source = source.replace("__BITS1__", lean_bool_list(bit_list(int(records["q1_3"]["n"]) - 1)))
source = source.replace("__BITS2__", lean_bool_list(bit_list(int(records["q2_0"]["n"]) - 1)))

for forbidden in ["sorry", "admit", "native_decide", "Lean.ofReduceBool", "Lean.trustCompiler", "unsafe", "axiom "]:
    assert forbidden not in source, forbidden

(ROOT / "D13CriticalFermat.lean").write_text(source)
records["lean_source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
(ROOT / "certificate.json").write_text(json.dumps(records, indent=2) + "\n")

theorems = [
    "D13Round24.powModBits_sound",
    "D13Round24.q1_formula",
    "D13Round24.q2_formula",
    "D13Round24.q1_bits_value",
    "D13Round24.q2_bits_value",
    "D13Round24.q1_powmod_value",
    "D13Round24.q2_powmod_value",
    "D13Round24.q1_fermat_modEq",
    "D13Round24.q2_fermat_modEq",
    "D13Round24.not_prime_of_fermat_failure",
    "D13Round24.q1Critical_coprime_two",
    "D13Round24.q2Critical_coprime_two",
    "D13Round24.q1_fermat_failure",
    "D13Round24.q2_fermat_failure",
    "D13Round24.q1Critical_not_prime",
    "D13Round24.q2Critical_not_prime",
    "D13Round24.q1_3_not_prime",
    "D13Round24.q2_0_not_prime",
]
audit = "import D13CriticalFermat\n\n" + "\n".join("#print axioms " + t for t in theorems) + "\n"
(ROOT / "AxiomAudit.lean").write_text(audit)
print(json.dumps(records, indent=2))
