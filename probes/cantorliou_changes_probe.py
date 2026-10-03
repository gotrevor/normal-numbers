#!/usr/bin/env -S uv run --quiet python3
"""Tripwire for CantorLiouville.sum_pow_changes and abs_cos_le_of_tdig_ne.

Checks, in exact rational arithmetic, the identity
  sum_{j < 2*3^M} theta^changes(c*2^j, P) = 2*3^M * ((1+2 theta)/3)^|P|
for P 2-separated inside (v3(c), M-1], against the closed form derived by hand (digits of a
uniform unit mod 3^n above position 0 are i.i.d. uniform, P(change) = 2/3).  The base-3 sibling
(c*3^j in place of c*2^j) must NOT satisfy it.  Then the cos(pi/9) bound at digit changes.
Exit code 1 on any failure.
"""
import math, sys
from fractions import Fraction as F
from itertools import combinations

def tdig(c, i): return (c // 3**i) % 3   # Python floor division = Lean Int ediv for 3^i > 0
def v3(c):
    c, v = abs(c), 0
    while c % 3 == 0: c //= 3; v += 1
    return v
def changes(c, P): return sum(1 for i in P if tdig(c, i + 1) != tdig(c, i))

th = F(2, 7); fails = 0; tot = 0
for c in [1, 2, -1, -5, 3, -6, 9, 18, -27, 63, -12]:
    v = v3(c)
    for M in range(1, 7):
        cand = list(range(v + 1, M))          # v < i, i + 1 <= M
        for r in range(4):
            for P in combinations(cand, r):
                if any(P[k] + 2 > P[k + 1] for k in range(len(P) - 1)): continue
                tot += 1
                lhs = sum(th ** changes(c * 2**j, P) for j in range(2 * 3**M))
                if lhs != 2 * 3**M * ((1 + 2 * th) / 3) ** len(P):
                    fails += 1; print("FAIL", c, M, P)
sib = sum(th ** changes(3**j, (1, 3)) for j in range(2 * 3**4))
if sib == 2 * 3**4 * ((1 + 2 * th) / 3) ** 2:
    fails += 1; print("FAIL: base-3 sibling satisfies the identity")
worst = max(abs(math.cos(2 * math.pi * x / 3**(i + 2)))
            for x in range(-3000, 3000) for i in range(6) if tdig(x, i + 1) != tdig(x, i))
if worst > math.cos(math.pi / 9) + 1e-12:
    fails += 1; print("FAIL cos bound", worst)
print(f"identity cases {tot}, failures {fails}, worst |cos| at a change {worst:.12f}")
sys.exit(1 if fails else 0)
