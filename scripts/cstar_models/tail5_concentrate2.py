#!/usr/bin/env python3
"""Gate 5 lap 3: exhaustive per-cell potential ratios (bottom-up), exact rationals.

For every level k <= KTOP - 12 and EVERY Acc2 cell (k, a) (Good or not), computes
  d1 = descMass k a (k+6), d2 = descMass k a (k+12), d3 = descMass k a (k+18) (if k+18 <= KTOP)
exactly (Good449 + Coherent.wq o classify via tail5_measure), and reports
  * node 4  (RegularPotential449 R: Good k a -> d2 <= R d1): max d2/d1 over Good cells, zero-d1 hits
  * node 4' (RegularPotential2_449 R: all cells -> d3 <= R d2): max d3/d2, zero-d2 hits
EXHAUSTIVE over the stated levels: the maxima are exact maxima over those levels, so a value above R
is a CERTIFIED counterexample to the node with that R (not a sampled screen).

usage: tail5_concentrate2.py KTOP
"""
import sys
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, '.')
import tail5_measure as T
from fractions import Fraction
from collections import defaultdict

def main():
    ktop = int(ARGS[0])
    acc = [[0]]                  # Acc2 cells per level
    wts = [{0: Fraction(1)}]      # positive weights per level
    good = [{0}]
    for k in range(1, ktop + 1):
        lev = [c for a in acc[-1] for c in (2 * a, 2 * a + 1) if T.sft(k, c) != 99]
        acc.append(lev)
        wk, gk = {}, set()
        for a in lev:
            if k >= 5 and T.good(k, a):
                gk.add(a)
                w = T.weight(k, a)
                if w > 0: wk[a] = w
        wts.append(wk); good.append(gk)
        print(f"level {k}: Acc2 {len(lev)}, Good {len(gk)}, positive {len(wk)}", flush=True)
    def agg(L, d):  # descMass of level-L cells at depth d
        out = defaultdict(Fraction)
        for a, w in wts[L + d].items(): out[a >> d] += w
        return out
    for k in range(0, ktop - 11):
        d1, d2 = agg(k, 6), agg(k, 12)
        d3 = agg(k, 18) if k + 18 <= ktop else None
        best4, arg4, zero4 = Fraction(0), None, []
        best4p, arg4p, zero4p = Fraction(0), None, []
        for a in acc[k]:
            x1, x2 = d1.get(a, 0), d2.get(a, 0)
            if a in good[k] or k == 0:
                if x1 == 0:
                    if x2 > 0: zero4.append(a)
                elif x2 / x1 > best4: best4, arg4 = x2 / x1, a
            if d3 is not None:
                x3 = d3.get(a, 0)
                if x2 == 0:
                    if x3 > 0: zero4p.append(a)
                elif x3 / x2 > best4p: best4p, arg4p = x3 / x2, a
        line = (f"k={k}: node4 max d2/d1 = {float(best4):.5g} at a={arg4}; Good cells with d1=0<d2: "
                f"{len(zero4)} {zero4[:5]}")
        if d3 is not None:
            line += (f" | node4' max d3/d2 = {float(best4p):.5g} at a={arg4p}; cells with d2=0<d3: "
                     f"{len(zero4p)} {zero4p[:5]}")
        print(line, flush=True)

if __name__ == '__main__':
    main()
