#!/usr/bin/env python3
"""Gate 5 lap 3: relative hull of the positive Good descendants (Frostman-node refutation probe).

APKillFrostman449 s C alpha (UniformBadTailMechanism) says: for ANY cell (k,a), q >= 2^(k+s), any
offset theta and half-width h, the Good level-K descendant weight inside the progression
{(A+theta)/q +- h} is <= C (2hq)^alpha * descMass k a K.  With s = 0, q = 2^k and ONE progression
interval covering the hull [lo, hi] (relative length l) of the positive descendants, the left side
is the whole descMass while 2hq = l, so the node fails whenever C l^alpha < 1, i.e.
l < C^(-1/alpha) (= 0.4424 for C = 2, alpha = 17/20).  For general s one interval covers a hull of
relative length l with 2hq = l 2^s: refutes when l < 2^-s C^(-1/alpha).

Reads the exact core dump (tail5_dump.py).  For every cell (k, a) at levels KMIN..KMAX (Acc2, any
Good status) with positive descMass at level k+D: hull [lo, hi) in units of 2^-(k+D).
Reports the smallest relative hull per level (exact integers; a certified witness, not a sample).
usage: tail5_hull.py KMIN KMAX D
"""
import sys, pickle
from pathlib import Path
CORE = Path(__file__).parent / 'tail5_out' / 'core'

def load(k):
    with open(CORE / f'core_k{k}.pkl', 'rb') as f: return pickle.load(f)

def main():
    kmin, kmax, D = map(int, sys.argv[1:4])
    for k in range(kmin, kmax + 1):
        acc, good, w = load(k + D)
        lo, hi, mass = {}, {}, {}
        for a, x in zip(acc, w):
            if x <= 0: continue
            p = a >> D; off = a - (p << D)
            if p not in lo: lo[p] = off; hi[p] = off + 1; mass[p] = x
            else:
                lo[p] = min(lo[p], off); hi[p] = max(hi[p], off + 1); mass[p] += x
        accK, goodK, wK = load(k)
        gk = {a for a, g in zip(accK, goodK) if g}
        best = sorted(((hi[p] - lo[p]) / 2 ** D, p) for p in lo)[:4]
        bestg = sorted(((hi[p] - lo[p]) / 2 ** D, p) for p in lo if p in gk)[:4]
        print(f"k={k} D={D}: cells with positive desc {len(lo)}; smallest hulls (any) "
              f"{[(round(l, 5), p, p in gk) for l, p in best]}; Good {[(round(l, 5), p) for l, p in bestg]}",
              flush=True)

if __name__ == '__main__':
    main()
