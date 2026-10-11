#!/usr/bin/env python3
"""Gate 5 lap 3: COMB SPREADING screen (count-mass comparability), exact, exhaustive.

Mechanism.  The 64 block-children of a cell sit at base-3 phases x' = frac(x0 + i rho), i < 64,
spaced rho in (2 d3, 6 d3] > 1/128 = the gate-4 x-bin width, so a parent puts at most ceil(64 rho) <= 3
children into any x-bin.  If few (state, x-bin) pairs carry weight below w0, every parent has at most
e(w0) children that are core-alive but "low" (Good with W < w0, or not Good).  Then the count N'_m of
core-alive cells at level 6m obeys N'_m <= mass(m)/w0 + e(w0) N'_(m-1), so N' <= K mass with
K = 1/(w0 (1 - e/(34 - c))) as soon as e(w0) < 34 - c.  This needs NO regularity of the survivor
distribution: it is a per-parent finite statement (a B&B certificate over parent types).

Reports, over EVERY Acc2 cell p at levels KMIN..KMAX (core-alive = Acc2 and not inside a resolved
base-3 window), e(w0) = max over p of #core-alive level-(k+6) descendants that are low, for several
w0 (fractions of maxW).  Reads tail5_out/core (tail5_dump.py).  EXHAUSTIVE over those levels:
a certified maximum over them (a lower bound on the supremum over all levels).
usage: tail5_comb.py KMIN KMAX
"""
import sys, pickle
from pathlib import Path
from collections import defaultdict
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, str(Path(__file__).parent))
import tail5_measure as T
CORE = Path(__file__).parent / 'tail5_out' / 'core'

def load(k):
    with open(CORE / f'core_k{k}.pkl', 'rb') as f: return pickle.load(f)

def inside3(k, a):
    """cell inside some base-3 window (dead in the core); ambiguous -> True (conservative for dead)."""
    n = 0
    while 3 ** n * T.SCALE <= 2 * T.R3[1] * 2 ** k:
        A0 = (a * 3 ** n) >> k
        for A in (A0, A0 + 1):
            if T.inside(k, a, 3, n, A, T.R3): return True
        n += 1
    return False

def main():
    kmin, kmax = int(ARGS[0]), int(ARGS[1])
    fracs = [1, 3, 10, 30, 100, 300, 1000]
    for k in range(kmin, kmax + 1):
        acc, good, w = load(k + 6)
        low = {f: defaultdict(int) for f in fracs}
        alive_kids = defaultdict(int)
        for a, g, x in zip(acc, good, w):
            if not g and inside3(k + 6, a): continue      # dead child
            p = a >> 6
            alive_kids[p] += 1
            for f in fracs:
                if (not g) or x * f < T.MAXW: low[f][p] += 1
        accK, goodK, wK = load(k)
        par = [a for a, g in zip(accK, goodK) if g or not inside3(k, a)]
        out = []
        for f in fracs:
            e = max((low[f].get(p, 0) for p in par), default=0)
            out.append(f"w0=maxW/{f}: e={e}")
        mk = max((alive_kids.get(p, 0) for p in par), default=0)
        print(f"k={k}: core-alive parents {len(par)}, max alive children {mk}; " + "; ".join(out), flush=True)

if __name__ == '__main__':
    main()
