#!/usr/bin/env python3
from __future__ import annotations

from math import isqrt
from pathlib import Path

PAIRS = [
    (10937, 15592301), (10939, 14680951), (10979, 2675419),
    (11093, 871177), (11113, 976271), (11131, 680321),
    (11131, 894527), (11131, 942311), (11353, 458987),
    (11411, 501623), (11437, 290597), (13177, 89113),
    (15259, 73721), (17929, 55603), (18457, 32993),
    (18959, 29567), (19379, 32999), (19961, 33857),
    (20173, 35897), (20233, 46639), (20731, 35023),
    (27791, 35509),
]


def s(n: int, e: int) -> int:
    return sum(n**k for k in range(e + 1))


def certificate(p: int, q: int) -> tuple[int, int]:
    a = 32770 * (p**17 + 1) * (q**9 + 1)
    b = 32767 * s(p, 17) * s(q, 9)
    c = a - b
    d = a*a - 4*c*c
    root = isqrt(d)
    assert root*root < d < (root + 1)*(root + 1)
    return d, root


def theorem_name(i: int, p: int, q: int) -> str:
    return f"survivor_{i:02d}_{p}_{q}_not_square"


def generate(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    marker = "theorem first_survivor_discriminant_not_square"
    if marker not in text:
        raise SystemExit(f"marker not found in {path}")
    prefix = text.split(marker, 1)[0].rstrip() + "\n\n"

    out: list[str] = [prefix]
    out.append("def SurvivorPair (p q : ℕ) : Prop :=\n")
    for i, (p, q) in enumerate(PAIRS):
        suffix = " ∨\n" if i < len(PAIRS) - 1 else "\n"
        out.append(f"  (p = {p} ∧ q = {q}){suffix}")
    out.append("\n")

    for i, (p, q) in enumerate(PAIRS, 1):
        d, root = certificate(p, q)
        name = theorem_name(i, p, q)
        out.append(
            f"theorem {name} :\n"
            f"    ¬ IsIntSquare (discriminant {p} {q}) := by\n"
            f"  rw [show discriminant {p} {q} =\n"
            f"      {d} by\n"
            f"    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]\n"
            f"  apply not_int_square_of_strict_gap (root := {root})\n"
            f"  · norm_num\n"
            f"  · norm_num\n"
            f"  · norm_num\n\n"
        )

    out.append(
        "theorem no_A_of_survivor_pair {p q r : ℕ}\n"
        "    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)\n"
        "    (h2p : 2 < p) (hpq : p < q) (hqr : q < r)\n"
        "    (hpair : SurvivorPair p q) :\n"
        "    ¬ A (Branch p q r) := by\n"
        "  intro hA\n"
        "  have hs := A_branch_discriminant_square hp hq hr h2p hpq hqr hA\n"
        "  unfold SurvivorPair at hpair\n"
    )
    for i, (p, q) in enumerate(PAIRS, 1):
        name = theorem_name(i, p, q)
        if i < len(PAIRS) - 1:
            out.append(
                "  rcases hpair with h | hpair\n"
                "  · rcases h with ⟨rfl, rfl⟩\n"
                f"    exact {name} hs\n"
            )
        elif i == len(PAIRS) - 1:
            out.append(
                "  rcases hpair with h | h\n"
                "  · rcases h with ⟨rfl, rfl⟩\n"
                f"    exact {name} hs\n"
            )
        else:
            out.append(
                "  · rcases h with ⟨rfl, rfl⟩\n"
                f"    exact {name} hs\n\n"
            )

    p0, q0 = PAIRS[0]
    d0, root0 = certificate(p0, q0)
    out.append(
        "/-- Mutation control: increasing the first square-root witness by one\n"
        "destroys the lower strict-gap inequality. -/\n"
        "theorem first_root_successor_mutation_rejected :\n"
        f"    ¬(({root0 + 1} : ℤ)^2 <\n"
        f"      discriminant {p0} {q0}) := by\n"
        f"  rw [show discriminant {p0} {q0} =\n"
        f"      {d0} by\n"
        f"    norm_num [discriminant, Ccoef, Acoef, Bcoef, S17N, S9N]]\n"
        "  norm_num\n\n"
    )

    out.append("#print axioms A_branch_reciprocal_quadratic\n")
    out.append("#print axioms A_branch_discriminant_square\n")
    out.append("#print axioms not_int_square_of_strict_gap\n")
    for i, (p, q) in enumerate(PAIRS, 1):
        out.append(f"#print axioms {theorem_name(i, p, q)}\n")
    out.append("#print axioms no_A_of_survivor_pair\n")
    out.append("#print axioms first_root_successor_mutation_rejected\n\n")
    out.append("end D17Round30\n")

    path.write_text("".join(out), encoding="utf-8")


if __name__ == "__main__":
    generate(Path(__file__).with_name("D17Round30SurvivorGaps.lean"))
