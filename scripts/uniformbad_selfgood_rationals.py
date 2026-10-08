#!/usr/bin/env python3
# Host probe (Ren, 2026-10-08): "self-good" rationals for the c* tower reduction.
# p/q (lowest terms) is self-good at exponent c if ||b^n p/q|| > b^-c for EVERY base 2 <= b < q and
# EVERY n >= 0.  Exact: orbits of b^n p mod q are eventually periodic, so a full orbit is a finite check;
# for b > q^(1/c) only integrality (rad q | b) can fail.
# Tower reduction: Admissible c iff some nonempty F has: forall x in F, eps > 0, B, exists y in F within
# eps of x with ||b^n y|| > b^-c for all b < B, all n.  With F inside the self-good rationals the
# condition is pure arithmetic of rationals.
# Usage: uniformbad_selfgood_rationals.py c QMAX [lo hi]
import math, sys
def rad(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            r *= p
            while n % p == 0: n //= p
        p += 1
    return r * (n if n > 1 else 1)
def selfgood(p, q, c):
    rq = rad(q)
    for b in range(2, q):
        thr = b ** (-c) * q  # need min(r, q-r) > thr for every orbit residue r
        if thr < 1:
            if b % rq == 0: return False
            continue
        r, seen = p % q, set()
        while r not in seen:
            if min(r, q - r) <= thr: return False
            seen.add(r); r = r * b % q
    return True
if __name__ == "__main__":
    c, Q = float(sys.argv[1]), int(sys.argv[2])
    lo, hi = (float(sys.argv[3]), float(sys.argv[4])) if len(sys.argv) > 4 else (0.0, 0.5)
    found = []
    for q in range(2, Q + 1):
        for p in range(max(1, math.ceil(lo * q)), math.floor(hi * q) + 1):
            if math.gcd(p, q) == 1 and selfgood(p, q, c): found.append((p / q, p, q))
    found.sort()
    print(f"c={c} q<={Q} in [{lo},{hi}]: {len(found)} self-good rationals")
    for x, p, q in found: print(f"  {x:.10f} {p}/{q}")
