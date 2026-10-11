#!/usr/bin/env python3
"""Gate 5 relaunch, refinement (i): W-weighted run sums, EXACT and EXHAUSTIVE over the dumped core.

f_k(R) = max over level-k parents p and contiguous runs of R of p's 64 block-children (level k+6, in
digit order) of sum W(child)/maxW, W = 0 for non-Good or absent children.  A window kills a
contiguous run of a parent's children, so f(R) replaces the crude 'R children of weight <= 1'.
Exact integers (sums of W, compared to MAXW only at print).  Exhaustive over levels KMIN..KMAX,
so f printed is a certified LOWER bound on sup_k f_k(R) (sound for a refutation, not for a close).
usage: tail5_runsum.py KMIN KMAX
"""
import sys, pickle
from pathlib import Path
CORE = Path(__file__).parent / 'tail5_out' / 'core'
MAXW = 1072633893121
RS = list(range(65))

def main():
    kmin, kmax = int(sys.argv[1]), int(sys.argv[2])
    tot = {R: 0 for R in RS}
    for k in range(kmin, kmax + 1):
        acc, good, w = pickle.load(open(CORE / f'core_k{k + 6}.pkl', 'rb'))
        kids = {}
        for a, g, x in zip(acc, good, w):
            if g: kids.setdefault(a >> 6, [0] * 64)[a & 63] = x
        best = {R: 0 for R in RS}
        for v in kids.values():
            pre = [0]
            for x in v: pre.append(pre[-1] + x)
            for R in RS:
                m = max(pre[i + R] - pre[i] for i in range(65 - R))
                if m > best[R]: best[R] = m
        for R in RS: tot[R] = max(tot[R], best[R])
        print(f"k={k}: " + " ".join(f"f({R})={best[R] / MAXW:.3f}" for R in RS), flush=True)
    print("max: " + " ".join(f"f({R})={tot[R] / MAXW:.4f}" for R in RS))
    print("exact max numerators:", {R: tot[R] for R in RS})

if __name__ == '__main__':
    main()
