#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
path = ROOT / "D13CriticalFermat.lean"
source = path.read_text()

old_true = '''          have htrue := hmul.trans hred
          simpa [q, evalBits, powModBits, pow_succ', Nat.add_comm] using htrue
'''
new_true = '''          have htrue := hmul.trans hred
          change a ^ (1 + 2 * evalBits bs) ≡
            (a * powModBits ((a * a) % n) n bs) % n [MOD n]
          rw [show 1 + 2 * evalBits bs = 2 * evalBits bs + 1 by omega,
            pow_succ']
          simpa only [q] using htrue
'''
assert source.count(old_true) == 1
source = source.replace(old_true, new_true)

old_formula = '''theorem q1_formula : q1 3 = q1Critical := by
  norm_num [q1, Q, q1Critical]

theorem q2_formula : q2 0 = q2Critical := by
  norm_num [q2, Q, q2Critical]
'''
new_formula = '''theorem q1_formula : q1 3 = q1Critical := by
  change (740 * 10 ^ 733 + 1) / 2391 = q1Critical
  have hmul : 740 * 10 ^ 733 + 1 = q1Critical * 2391 := by
    norm_num [q1Critical]
  have hdvd : 2391 ∣ 740 * 10 ^ 733 + 1 := by
    refine ⟨q1Critical, ?_⟩
    simpa [mul_comm] using hmul
  exact (Nat.div_eq_iff_eq_mul_left (by decide) hdvd).2 hmul

theorem q2_formula : q2 0 = q2Critical := by
  change (370 * 10 ^ 666 + 1) / 2177 = q2Critical
  have hmul : 370 * 10 ^ 666 + 1 = q2Critical * 2177 := by
    norm_num [q2Critical]
  have hdvd : 2177 ∣ 370 * 10 ^ 666 + 1 := by
    refine ⟨q2Critical, ?_⟩
    simpa [mul_comm] using hmul
  exact (Nat.div_eq_iff_eq_mul_left (by decide) hdvd).2 hmul
'''
assert source.count(old_formula) == 1
source = source.replace(old_formula, new_formula)

# `norm_num` deliberately evaluates the two decimal-power identities exactly.
# The largest exponent is 733, so raise only this evaluator guard; this is not
# a heartbeat or recursion bypass and the resulting proof terms remain kernel checked.
anchor = "set_option maxHeartbeats 0\n"
assert source.count(anchor) == 1
source = source.replace(anchor, anchor + "set_option exponentiation.threshold 1000\n", 1)

for forbidden in ["sorry", "admit", "native_decide", "Lean.ofReduceBool", "Lean.trustCompiler", "unsafe", "axiom "]:
    assert forbidden not in source, forbidden

path.write_text(source)
cert_path = ROOT / "certificate.json"
cert = json.loads(cert_path.read_text())
cert["lean_source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
cert_path.write_text(json.dumps(cert, indent=2) + "\n")
print("FINALIZE_GENERATED_PASS lean_source_sha256=" + cert["lean_source_sha256"])
