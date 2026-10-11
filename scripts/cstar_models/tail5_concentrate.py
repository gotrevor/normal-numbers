#!/usr/bin/env python3
"""Gate 5 lap 3: CONCENTRATED cells (refutation probe for the per-cell nodes).

A cell whose Good descendants all lie in a tiny sub-interval breaks every per-cell RELATIVE bound:
node 4 (`RegularPotential449`), node 4' (`RegularPotential2_449`) and the Frostman AP node
(`APKillFrostman449`).  Mechanism: the binary followers of a cell span a hull [inf, sup] strictly
inside the cell (no 5-runs), and a base-3 window edge can fall just below `sup` (or above `inf`), so
the only Good descendants sit in a sliver next to the hull end.  The cell position `a` moves the edge
on a grid of step about 2^-k (relative), so slivers of every depth occur; no Diophantine luck needed.

Exact integer arithmetic (tail5_measure: Good449, Coherent.wq o classify).  Every hit is a
CERTIFIED finite witness (no sampling claim): the printed descendant masses are exact rationals.

usage: tail5_concentrate.py KMIN KMAX [DEPTH2]
  enumerates EVERY Acc2 cell at levels KMIN..KMAX (Good or not) and reports
  * cells with desc(+6) = 0 < desc(+12)          -> refutes node 4 / RegularPotential449 (Good cells)
  * the largest desc(+12)/desc(+6) and its cell
  * for cells with desc(+12) = 0, desc(+18) (if DEPTH2) -> refutes node 4' / RegularPotential2_449
"""
import sys
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, '.')
import tail5_measure as T
from fractions import Fraction

def desc(k, a, d):
    """Good weighted descendants exactly d levels below (k,a); prune only on the binary SFT."""
    out = Fraction(0)
    stack = [(k, a)]
    kt = k + d
    while stack:
        kk, aa = stack.pop()
        if T.sft(kk, aa) == 99: continue
        if kk == kt:
            out += T.weight(kk, aa)
            continue
        stack.append((kk + 1, 2 * aa)); stack.append((kk + 1, 2 * aa + 1))
    return out

def span(k, a, d):
    """relative hull [lo, hi] (in units of the cell) of positive-weight descendants at depth d."""
    lo = hi = None
    stack = [(k, a)]
    kt = k + d
    while stack:
        kk, aa = stack.pop()
        if T.sft(kk, aa) == 99: continue
        if kk == kt:
            if T.weight(kk, aa) > 0:
                off = aa - (a << d)
                lo = off if lo is None else min(lo, off)
                hi = off + 1 if hi is None else max(hi, off + 1)
            continue
        stack.append((kk + 1, 2 * aa)); stack.append((kk + 1, 2 * aa + 1))
    return lo, hi

def main():
    kmin, kmax = int(ARGS[0]), int(ARGS[1])
    deep = len(ARGS) > 2 and ARGS[2] == '18'
    best = (Fraction(0), None)
    hits4, hits4p = [], []
    level = [0]
    for k in range(1, kmax + 1):
        level = [c for a in level for c in (2 * a, 2 * a + 1) if T.sft(k, c) != 99]
        if k < kmin: continue
        ngood = 0
        for a in level:
            g = T.good(k, a)
            ngood += g
            d1 = desc(k, a, 6)
            if d1 == 0:
                d2 = desc(k, a, 12)
                if d2 > 0:
                    lo, hi = span(k, a, 12)
                    print(f"  ZERO-6 k={k} a={a} good={g} w={float(T.weight(k, a)):.3g} desc12={float(d2):.4g}"
                          f" span12=[{lo},{hi})/4096", flush=True)
                    (hits4 if g else hits4p).append((k, a, d2))
                elif deep:
                    d3 = desc(k, a, 18)
                    if d3 > 0:
                        print(f"  ZERO-12 k={k} a={a} good={g} desc18={float(d3):.4g}", flush=True)
            else:
                if g:
                    d2 = desc(k, a, 12)
                    r = d2 / d1
                    if r > best[0]:
                        best = (r, (k, a))
        print(f"level {k}: Acc2 cells {len(level)}, Good {ngood}; max desc12/desc6 over Good so far "
              f"{float(best[0]):.4g} at {best[1]}; zero-6 Good hits {len(hits4)}, non-Good {len(hits4p)}",
              flush=True)

if __name__ == '__main__':
    main()
