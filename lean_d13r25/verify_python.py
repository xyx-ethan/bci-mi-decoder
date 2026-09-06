#!/usr/bin/env python3
from pathlib import Path
import csv
import hashlib
import json

ROOT = Path(__file__).resolve().parent
MODS = (10, 9, 13, 7, 11, 37)
QBOUND = {3: 216, 4: 39, 5: 16, 6: 9, 7: 6, 8: 5, 9: 4}
EXPECTED_KILLS = {10: 16324, 9: 4257, 13: 480, 7: 32, 11: 4, 37: 1}
EXPECTED_CERT_SHA = "0c2b2379998208e6bae2893593a3735734eadeead8fd17183ecd98f1bdf6ff10"
EXPECTED_TUPLE_SHA = "5a78ef72f26ebe5d8e91f3fdb7d430f5a6ed4879ce5e7a52620603e4347eae65"


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def enc(p: int, q: int, e: int, f: int) -> int:
    return ((p * 10 ** len(str(e)) + e) * 10 ** len(str(q)) + q) * 10 + f


def reconstruct() -> list[tuple[int, int, int, int]]:
    primes = [n for n in range(2, 2241) if is_prime(n)]
    out = [(2, q, e, 2) for q in primes if q > 2 for e in range(1, 15)]
    for f in range(3, 10):
        ps = [p for p in primes if p <= QBOUND[f]]
        out.extend((p, q, e, f) for q in ps for p in ps if p < q for e in range(1, 15))
    return out


def verify_rows(rows: list[dict[str, int]]) -> None:
    domain = reconstruct()
    assert len(domain) == 21098
    assert len(rows) == len(domain)
    assert [(r["p"], r["q"], r["e"], r["f"]) for r in rows] == domain
    seen: set[tuple[int, int, int, int]] = set()
    counts = {m: 0 for m in MODS}
    for r in rows:
        p, q, e, f = r["p"], r["q"], r["e"], r["f"]
        key = (p, q, e, f)
        assert key not in seen
        seen.add(key)
        lhs = p**e * q**f
        rhs = enc(p, q, e, f)
        m = r["killer_mod"]
        assert m in MODS
        assert lhs % m == r["lhs_residue"]
        assert rhs % m == r["rhs_residue"]
        assert r["lhs_residue"] != r["rhs_residue"]
        for earlier in MODS[: MODS.index(m)]:
            assert lhs % earlier == rhs % earlier
        counts[m] += 1
    assert counts == EXPECTED_KILLS


with (ROOT / "elimination_certificate.csv").open(newline="") as fh:
    parsed = [{k: int(v) for k, v in row.items()} for row in csv.DictReader(fh)]
verify_rows(parsed)

assert hashlib.sha256((ROOT / "elimination_certificate.csv").read_bytes()).hexdigest() == EXPECTED_CERT_SHA
assert hashlib.sha256((ROOT / "candidate_tuples.csv").read_bytes()).hexdigest() == EXPECTED_TUPLE_SHA
manifest = json.loads((ROOT / "manifest.json").read_text())
assert manifest["rows"] == 21098
assert manifest["survivor_counts"] == [4774, 517, 37, 5, 1, 0]
assert manifest["last_pre_mod37"] == [37, 53, 14, 3]

# Destructive mutation tests.
mutations = []
mutations.append(parsed[:-1])
mutations.append(parsed + [dict(parsed[-1])])
x = [dict(r) for r in parsed]
x[0]["killer_mod"] = 37
mutations.append(x)
x = [dict(r) for r in parsed]
x[-1]["rhs_residue"] = x[-1]["lhs_residue"]
mutations.append(x)
x = [dict(r) for r in parsed]
x[100]["q"] += 2
mutations.append(x)
rejected = 0
for mutated in mutations:
    try:
        verify_rows(mutated)
    except AssertionError:
        rejected += 1
assert rejected == len(mutations)

print(f"PYTHON_STRUCTURAL_CERTIFICATE_PASS rows={len(parsed)} mutations={rejected}")
print(f"certificate_sha256={EXPECTED_CERT_SHA}")
print(f"tuple_stream_sha256={EXPECTED_TUPLE_SHA}")
