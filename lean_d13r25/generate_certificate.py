#!/usr/bin/env python3
from pathlib import Path
import csv
import hashlib
import json

ROOT = Path(__file__).resolve().parent
MODULI = (10, 9, 13, 7, 11, 37)
QBOUND = {3: 216, 4: 39, 5: 16, 6: 9, 7: 6, 8: 5, 9: 4}
EXPECTED_ROWS = 21098
EXPECTED_CERT_SHA256 = "0c2b2379998208e6bae2893593a3735734eadeead8fd17183ecd98f1bdf6ff10"
EXPECTED_TUPLE_SHA256 = "5a78ef72f26ebe5d8e91f3fdb7d430f5a6ed4879ce5e7a52620603e4347eae65"
EXPECTED_KILLS = {10: 16324, 9: 4257, 13: 480, 7: 32, 11: 4, 37: 1}
EXPECTED_SURVIVORS = [4774, 517, 37, 5, 1, 0]


def primes_up_to(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p : n + 1 : p] = b"\x00" * (((n - p * p) // p) + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def encoded(p: int, q: int, e: int, f: int) -> int:
    return ((p * 10 ** len(str(e)) + e) * 10 ** len(str(q)) + q) * 10 + f


def domain() -> list[tuple[int, int, int, int]]:
    primes = primes_up_to(2240)
    rows: list[tuple[int, int, int, int]] = []
    for q in primes:
        if q > 2:
            for e in range(1, 15):
                rows.append((2, q, e, 2))
    for f in range(3, 10):
        ps = [p for p in primes if p <= QBOUND[f]]
        for q in ps:
            for p in ps:
                if p >= q:
                    break
                for e in range(1, 15):
                    rows.append((p, q, e, f))
    return rows


def first_killer(p: int, q: int, e: int, f: int) -> tuple[int, int, int]:
    lhs = p**e * q**f
    rhs = encoded(p, q, e, f)
    for m in MODULI:
        a, b = lhs % m, rhs % m
        if a != b:
            return m, a, b
    raise AssertionError((p, q, e, f))


cases = domain()
assert len(cases) == EXPECTED_ROWS
rows = []
for p, q, e, f in cases:
    m, a, b = first_killer(p, q, e, f)
    rows.append({
        "p": p,
        "q": q,
        "e": e,
        "f": f,
        "killer_mod": m,
        "lhs_residue": a,
        "rhs_residue": b,
    })

cert = ROOT / "elimination_certificate.csv"
with cert.open("w", newline="") as fh:
    writer = csv.DictWriter(fh, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)

stream = ROOT / "candidate_tuples.csv"
stream.write_text("".join(f"{p},{q},{e},{f}\n" for p, q, e, f in cases))

cert_sha = hashlib.sha256(cert.read_bytes()).hexdigest()
tuple_sha = hashlib.sha256(stream.read_bytes()).hexdigest()
assert cert_sha == EXPECTED_CERT_SHA256, cert_sha
assert tuple_sha == EXPECTED_TUPLE_SHA256, tuple_sha

kills = {m: sum(r["killer_mod"] == m for r in rows) for m in MODULI}
assert kills == EXPECTED_KILLS
current = cases
survivors = []
for m in MODULI:
    current = [c for c in current if (c[0] ** c[2] * c[1] ** c[3]) % m == encoded(*c) % m]
    survivors.append(len(current))
assert survivors == EXPECTED_SURVIVORS
assert current == []

manifest = {
    "rows": len(rows),
    "f2_cases": sum(f == 2 for _, _, _, f in cases),
    "f3_to_9_cases": sum(f >= 3 for _, _, _, f in cases),
    "moduli": list(MODULI),
    "survivor_counts": survivors,
    "killer_counts": {str(k): v for k, v in kills.items()},
    "certificate_sha256": cert_sha,
    "tuple_stream_sha256": tuple_sha,
    "last_pre_mod37": [37, 53, 14, 3],
}
(ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
print("GENERATE_CERTIFICATE_PASS", json.dumps(manifest, sort_keys=True))
