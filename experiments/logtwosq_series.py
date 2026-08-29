#!/usr/bin/env python3
"""Refutation probe for the LogTwoSqSeries node (lane-2 target 5).

Claim: log^2 2 = sum_{m>=1} (2*H_{m-1}/m) * 2^-m, with H_0 = 0.
Derivation: integrate sum H_n x^n = -log(1-x)/(1-x) term-by-term on [0, 1/2]:
  sum_{n>=1} H_n x^{n+1}/(n+1) = (1/2) log^2(1-x); at x = 1/2 and reindexing
  m = n+1: sum_{m>=2} (H_{m-1}/m) 2^-m = (1/2) log^2 2.

Also probes the kick bounds used in Lean:
  r(m) = 2*H_{m-1}/m <= 2*(1+log(n+1))/(n+1) for m > n  (cap, n >= 1)
  r(n+1) = 2*H_n/(n+1) > 0 (floor).
"""
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 70

# exact partial sum over m = 1..N as a Fraction
N = 400
H = Fraction(0)
s = Fraction(0)
for m in range(1, N + 1):
    s += Fraction(2, 1) * H / m / Fraction(2) ** m  # H holds H_{m-1}
    H += Fraction(1, m)

series = Decimal(s.numerator) / Decimal(s.denominator)
target = Decimal(2).ln() ** 2
err = abs(series - target)
print("series  =", series)
print("log^2 2 =", target)
print("abs err =", err)
assert err < Decimal(10) ** -60, "SERIES IDENTITY FAILS"

# cap probe: for a few n, check r(m) <= 2*(1+log(n+1))/(n+1) for all m in (n, n+400]
def Hn(k):
    return sum(Fraction(1, i) for i in range(1, k + 1))

for n in [1, 2, 6, 10, 50]:
    cap = 2 * (1 + Decimal(n + 1).ln()) / (n + 1)
    worst = max(Fraction(2) * Hn(m - 1) / m for m in range(n + 1, n + 401))
    worstd = Decimal(worst.numerator) / Decimal(worst.denominator)
    assert worstd <= cap, (n, float(worstd), float(cap))
    print(f"n={n}: cap={float(cap):.6f} worst kick past n={float(worstd):.6f} OK")

print("PROBE PASSES")
