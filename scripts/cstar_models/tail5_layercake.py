#!/usr/bin/env python3
"""Gate 5 relaunch, refinement (ii): layer-cake comb comparability, EXACT and EXHAUSTIVE.

For beta > 0 a parent's surviving children S satisfy |S| <= beta * sum_S W + sum_{c alive} (1 - beta W_c)^+,
so with e'(beta) = max over core-alive level-k parents p of sum over core-alive children c of p of
(1 - beta W_c)^+  (W = 0 for non-Good; alive = Good or not inside a base-3 window, as tail5_comb.py),
the survivor count obeys N'_m <= beta mass_m + e'(beta) N'_(m-1), hence N' <= K mass with
K(beta, gamma) = beta / (1 - e'(beta)/gamma).  The crude comb bound is the special case
(1 - beta W)^+ <= [W < 1/beta].  Exact rationals (W/maxW); exhaustive over levels KMIN..KMAX, so e'
is a certified LOWER bound on the sup over all levels (sound for a miss, not for a close).
usage: tail5_layercake.py KMIN KMAX
"""
import sys
from fractions import Fraction
from collections import defaultdict
ARGS = sys.argv[1:]
import tail5_comb as C
T = C.T
BETAS = [Fraction(n, 16) for n in range(6, 16)] + [Fraction(n, 8) for n in range(8, 49)]

def main():
    kmin, kmax = int(ARGS[0]), int(ARGS[1])
    tot = {b: Fraction(0) for b in BETAS}
    for k in range(kmin, kmax + 1):
        acc, good, w = C.load(k + 6)
        kids = defaultdict(list)
        for a, g, x in zip(acc, good, w):
            if not g and C.inside3(k + 6, a): continue
            kids[a >> 6].append(x if g else 0)
        accK, goodK, _ = C.load(k)
        par = [a for a, g in zip(accK, goodK) if g or not C.inside3(k, a)]
        best = {}
        for b in BETAS:
            best[b] = max((sum(max(Fraction(0), 1 - b * Fraction(x, T.MAXW)) for x in kids.get(p, [])) for p in par),
                          default=Fraction(0))
            tot[b] = max(tot[b], best[b])
        print(f"k={k}: " + " ".join(f"e'({float(b):g})={float(best[b]):.3f}" for b in BETAS), flush=True)
    print("max: " + " ".join(f"e'({float(b):g})={float(tot[b]):.4f}" for b in BETAS))
    print("exact:", {str(b): str(tot[b]) for b in BETAS})

if __name__ == '__main__':
    main()
