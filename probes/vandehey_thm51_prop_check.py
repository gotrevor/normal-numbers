#!/usr/bin/env -S uv run --quiet python3
"""Numerical tripwire for `Literature.VandeheyDiff.VandeheyThm51` (LiteratureVandeheyDifferencing.lean).

Recomputes the Prop's recursion exactly as the Lean defs state it (alpha, expPair, constPair, bigM,
cP) and checks the bound against the true Korobov sum |sum_{n=1}^N e(a b^n/m)| on small cases.  A
violation means the Lean transcription is FALSE (a false hypothesis would make the conditional
headline vacuous).  Also checks eq. (15): gamma_k + nu_k = 2 - 2^{-k}.  Exit 0 = no violation.
Usage: vandehey_thm51_prop_check.py   (`--test` runs the hand-computed k=0 case only)
"""
import cmath, math, sys
from math import gcd, log, sqrt

def order(b, q):
    if q == 1: return 1
    x, k = b % q, 1
    while x != 1:
        x, k = x * b % q, k + 1
    return k

def vp(p, n):
    v = 0
    while n % p == 0: n, v = n // p, v + 1
    return v

def bigM(b, P):
    Q = math.prod(P); o = order(b, Q); t = b ** (2 * o) - 1
    return math.prod(p ** vp(p, t) for p in P)

def cP(P, x): return math.prod(p ** x / (p ** x - 1) for p in P)
def alpha(k): return 1 / (2 ** (k + 2) - 2)

def expPair(k):
    g, n = 0.0, 1.0
    for j in range(k):
        a = alpha(j)
        g, n = (1 + g + a * n) / (2 * (1 + a)), (1 + n) / 2 + (1 + g - n) * a / (2 * (1 + a))
    return g, n

def constPair(b, P, k):
    A, B = 1.0, float(bigM(b, P)); s, Q, M = len(P), math.prod(P), bigM(b, P)
    for j in range(k):
        a = alpha(j)
        A, B = (sqrt(2 ** (s + 2) * Q * (A + B) * cP(P, a) + 2 * Q + 2 * A * M * cP(P, 1 + a)),
                sqrt(2 ** (1 + a) * B * M * Q ** a * cP(P, 1 - a)))
    return A, B

def bound(b, P, m, k, N):
    A, B = constPair(b, P, k); g, n = expPair(k); a = alpha(k)
    return (A * m ** a * N ** g + B * m ** (-a) * N ** n) * (1 + log(m)) ** (2.0 ** -k)

def ksum(a, b, m, N):
    return abs(sum(cmath.exp(2j * math.pi * (a * pow(b, n, m) % m) / m) for n in range(1, N + 1)))

def main():
    # hand-computed control: b=2, P={3}, m=3, k=0, N=1: M = 3 (15 = 3*5), bound = (sqrt3 + 3/sqrt3)(1+log 3)
    assert bigM(2, [3]) == 3
    assert abs(bound(2, [3], 3, 0, 1) - 2 * sqrt(3) * (1 + log(3))) < 1e-9
    if "--test" in sys.argv: print("ok"); return 0
    for k in range(12):
        g, n = expPair(k); assert abs(g + n - (2 - 2 ** -k)) < 1e-12, k
    worst, cases = 0.0, 0
    for b in (2, 3, 10):
        for P in ([3], [5], [3, 5], [3, 7], [5, 7], [3, 5, 7], [3, 5, 7, 11]):
            if any(b % p == 0 for p in P): continue
            ms = sorted({p1 ** i * p2 ** j for p1 in P for p2 in P for i in range(5) for j in range(3)
                         if 2 <= p1 ** i * p2 ** j <= 6000})
            for m in ms:
                for a in (1, 2, m - 1):
                    if gcd(a, m) != 1: continue
                    for N in (1, 2, 5, 17, 64, 300, 2000):
                        s = ksum(a, b, m, N)
                        for k in range(6):
                            r = s / bound(b, P, m, k, N); cases += 1
                            if r > worst: worst = r
                            if r > 1 + 1e-9:
                                print("VIOLATION", b, P, m, a, k, N, s, bound(b, P, m, k, N)); return 1
    print(f"no violation in {cases} cases; worst |sum|/bound = {worst:.3f}")
    return 0

sys.exit(main())
