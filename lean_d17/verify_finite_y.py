#!/usr/bin/env python3
from fractions import Fraction

TARGET = Fraction(262146, 262143)

def phi5(t: int) -> int:
    return t**4 + t**3 + t**2 + t + 1

def phi6(t: int) -> int:
    return t**2 - t + 1

def r4(t: int) -> Fraction:
    return Fraction(phi5(t), t**4 + 1)

def r3(t: int) -> Fraction:
    return Fraction(t*t + 1, phi6(t))

def u(t: int) -> Fraction:
    return Fraction(t, t - 1)

def boundary(c: int, target_num: int = 262146) -> bool:
    return c**3 * 262143 < target_num * (c - 1)**3

# Exact controls for the two universal rational bounds at representative integers.
for t in [2, 3, 17, 87383, 262145, 10**6 + 3]:
    assert r3(t) < u(t)
    assert r4(t) < u(t)
    assert r3(t) > 0 and r4(t) > 0

# Exact boundary used by the Lean theorem.
diff = 262146 * 262144**3 - 262143 * 262145**3
assert diff == 524289
assert boundary(262145)

# Mutations that must be rejected: one-lower cutoff and one-lower target numerator.
assert not boundary(262144)
assert not boundary(262145, target_num=262145)

print("PASS exact Fraction checker")
print(f"boundary_cross_difference={diff}")
print("mutations_rejected=2/2")
