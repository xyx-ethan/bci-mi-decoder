#!/usr/bin/env python3
from math import gcd, isqrt

def divisors(n: int):
    out = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
    return sorted(out)

def sigma(n: int) -> int:
    return sum(divisors(n)) if n > 0 else 0

def usigma(n: int) -> int:
    if n <= 0:
        return 0
    return sum(d for d in divisors(n) if gcd(d, n // d) == 1)

def A(n: int) -> bool:
    return n > 0 and sigma(n) == 2 * usigma(n)

# Positive and negative controls matching the formal definition.
assert A(108)
assert A(540)
assert A(756)
assert not A(1)
assert not A(36)

# Mutation: replacing the unitary divisor sum by the ordinary divisor sum
# would incorrectly destroy the known positive control 108.
assert sigma(108) != 2 * sigma(108)

print("PASS semantic controls")
print("positive=108,540,756")
print("negative=1,36")
print("ordinary-divisor mutation rejected")
