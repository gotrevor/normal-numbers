#!/usr/bin/env python3
"""Joint tree over 3-adic exponent classes: (alpha, beta) mod 3^d with the surviving x mod 3^(d+1).
Survives([4^a, 4^(a+b)], d) depends only on 4^a, 4^(a+b) mod 3^(d+1), i.e. on a, b mod 3^d
(ord of 4 mod 3^(d+1) is 3^d).  alive(d0, D, keep) counts classes alive at each depth,
starting from the classes mod 3^d0 accepted by keep(alpha, beta)."""
import sys

def digits_ok(v, k):            # digit k of v is 0 or 1
    return (v // 3**k) % 3 != 2

def init(d0, keep):
    mod = 3**(d0 + 1)
    out = {}
    for al in range(3**d0):
        for be in range(3**d0):
            if not keep(al, be): continue
            M1 = pow(4, al, mod); M2 = pow(4, al + be, mod)
            xs = [1]
            for k in range(1, d0 + 1):
                xs = [x + e * 3**k for x in xs for e in (0, 1)]
            xs = [x for x in xs if all(digits_ok(x, k) and digits_ok(M1 * x % mod, k) and digits_ok(M2 * x % mod, k)
                                       for k in range(d0 + 1))]
            if xs: out[(al, be)] = xs
    return out

def lift(level, d):
    """level: classes mod 3^d with x mod 3^(d+1); return classes mod 3^(d+1) with x mod 3^(d+2)."""
    mod = 3**(d + 2); out = {}
    for (al, be), xs in level.items():
        for i in range(3):
            for j in range(3):
                a2 = al + i * 3**d; b2 = be + j * 3**d
                M1 = pow(4, a2, mod); M2 = pow(4, a2 + b2, mod)
                ys = [y for x in xs for y in (x, x + 3**(d + 1))
                      if digits_ok(M1 * y % mod, d + 1) and digits_ok(M2 * y % mod, d + 1)]
                if ys: out[(a2, b2)] = ys
    return out

def alive(d0, D, keep, cap=3_000_000):
    lev = init(d0, keep); counts = [(d0, len(lev), 9**0)]
    for d in range(d0, D):
        lev = lift(lev, d)
        counts.append((d + 1, len(lev), sum(len(v) for v in lev.values())))
        if not lev or counts[-1][2] > cap: break
    return counts, lev

if __name__ == "__main__":
    bad = {0, 1, 8}
    keep = lambda a, b: a % 9 not in bad and b % 9 not in bad and (a + b) % 9 not in bad
    counts, _ = alive(2, int(sys.argv[1]), keep)
    for c in counts: print(c, flush=True)
