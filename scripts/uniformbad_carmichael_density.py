#!/usr/bin/env python3
# Host probe (Ren, 2026-10-08): density of self-good numerators p mod Q_L, where
# Q_L = prod of primes p with (p-1) | L, so every base has orbit length <= L mod Q_L (Carmichael
# exponent divides L).  Samples random p coprime to Q_L and checks self-goodness at exponent c
# (||b^n p/Q|| > b^-c for every base 2 <= b < Q and every n; only b <= Q^(1/c) need an orbit scan).
# Usage: uniformbad_carmichael_density.py c L [samples]
import math, random, sys
def primes_dividing_L_plus(L):
    return [d + 1 for d in range(1, L + 1) if L % d == 0 and all((d + 1) % k for k in range(2, int(math.isqrt(d + 1)) + 1))]
def selfgood(p, q, c, bmax):
    for b in range(2, bmax + 1):
        thr = b ** (-c) * q
        r, seen = p % q, set()
        while r not in seen:
            if min(r, q - r) <= thr: return False
            seen.add(r); r = r * b % q
    return True
if __name__ == "__main__":
    c, L = float(sys.argv[1]), int(sys.argv[2]); S = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    ps = primes_dividing_L_plus(L); Q = math.prod(ps)
    bmax = int(Q ** (1 / c)) + 1   # beyond: dnear >= 1/Q > b^-c; integrality needs rad Q | b, b >= Q
    random.seed(1); hits = []
    for _ in range(S):
        p = random.randrange(1, Q)
        if math.gcd(p, Q) == 1 and selfgood(p, Q, c, bmax): hits.append(p)
    print(f"c={c} L={L} primes={ps} Q={Q} bmax={bmax}: {len(hits)}/{S} self-good  e.g. {[f'{p}/{Q}' for p in hits[:3]]}")
