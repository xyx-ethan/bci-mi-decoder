#!/usr/bin/env python3
"""Independent exact checker for the Round-25 bridge equations."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
cert = json.loads((ROOT / "certificate.json").read_text())

cases = [
    ("q1_3", 7, 4, 733, 2391, 740),
    ("q2_0", 3, 7, 666, 2177, 370),
]

for name, p, e, digits, D, C in cases:
    q = int(cert[name]["n"])
    assert p**e - 10 == D
    assert 10 * (10 * p + e) == C
    assert len(str(q)) == digits
    assert D * q == C * 10**digits + 1
    # The linear equation has at most one natural-number solution.
    assert q == (C * 10**digits + 1) // D

# Semantic mutations: wrong digit stratum and reversed prime/exponent block.
q1 = int(cert["q1_3"]["n"])
q2 = int(cert["q2_0"]["n"])
assert 2391 * q1 != 740 * 10**732 + 1
assert 2177 * q2 != 370 * 10**665 + 1
assert 2391 * q1 != 470 * 10**733 + 1
assert 2177 * q2 != 730 * 10**666 + 1

print("PYTHON_BRIDGE_CHECK_PASS cases=2 mutations=4")
