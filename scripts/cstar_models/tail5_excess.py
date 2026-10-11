#!/usr/bin/env python3
"""Gate 5 lap 3: EXCESS profile of the gate-4 weights (two-class totals screen), exact rationals.

For every Good cell c at level k (all of them, no tail), with W = wq(classify), TW = Good child weight
one block down: excess_L(c) = max(TW - L*W, 0).  Reports, per level k and threshold L,
  X_L(k) = sum_c excess_L(c) / sum_c W(c)       (totals excess relative to mass; no tail)
  P_L(k) = sum over bad parents p (excess_L(p) > 0) of sum over bad children of excess_L(child)
           divided by sum over bad parents of excess_L(p)   (bad -> bad persistence, per block)
The two-class route needs X_L bounded and P_L < 34 (mass grows >= 34 per block).
EXHAUSTIVE over the levels shown (no sampling); no tail kills (the tail only removes cells).

usage: tail5_excess.py KTOP
"""
import sys
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, '.')
import tail5_measure as T
from fractions import Fraction
from collections import defaultdict

def main():
    ktop = int(ARGS[0])
    acc = [[0]]
    wts = [{0: Fraction(1)}]
    for k in range(1, ktop + 1):
        lev = [c for a in acc[-1] for c in (2 * a, 2 * a + 1) if T.sft(k, c) != 99]
        acc.append(lev)
        wk = {}
        for a in lev:
            if k >= 5 and T.good(k, a):
                wk[a] = T.weight(k, a)  # may be 0
        wts.append(wk)
    Ls = [40, 50, 60, 100, 200]
    for k in range(5, ktop - 11):
        tw = defaultdict(Fraction)
        for a, w in wts[k + 6].items(): tw[a >> 6] += w
        tw2 = defaultdict(Fraction)
        for a, w in wts[k + 12].items(): tw2[a >> 6] += w   # TW of level-(k+6) cells
        mass = sum(wts[k].values())
        out = []
        for L in Ls:
            ex = Fraction(0); badp = Fraction(0); badc = Fraction(0)
            for a, w in wts[k].items():
                e = tw.get(a, 0) - L * w
                if e > 0:
                    ex += e; badp += e
                    for j in range(64):
                        c = 64 * a + j
                        if c in wts[k + 6]:
                            ec = tw2.get(c, 0) - L * wts[k + 6][c]
                            if ec > 0: badc += ec
            out.append(f"L={L}: X={float(ex / mass):.4g} P={float(badc / badp) if badp else 0:.4g}")
        print(f"k={k}: mass={float(mass):.5g}; " + "; ".join(out), flush=True)

if __name__ == '__main__':
    main()
