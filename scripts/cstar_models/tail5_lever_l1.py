#!/usr/bin/env python3
"""Gate 5 operator lever probe, lever (L1) lag-dependent K: OPTIMISTIC bound (a kill test for the lever).

Any comparability constant, lag-dependent or not, satisfies K_l >= 1: survivor COUNT >= MASS because
every weight is <= maxW.  So the best (L1) can do on top of tail5_refined.py (i)+(ii)+(iii) is
  sum = K(gamma) h_1/gamma + sum_{l>=2} K_l h_l/gamma^l  with K_l >= 1 for l >= 2,
and GAP_L1 >= inf_gamma [K h_1/gamma + sum_{l>=2} h_l/gamma^l] / ((9/5)^6 - gamma).  The h_l are the
refined screen's (certified lower bounds).  If this misses the 0.9 close threshold, L1 cannot close.
Also reports the absolute floor K_l = 1 at EVERY lag (no lever on K can beat it).
usage: tail5_lever_l1.py BMAX GRID
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import tail5_refined as T
G, L = T.G, T.L

def main():
    bmax, grid = int(sys.argv[1]), int(sys.argv[2])
    f = T.load_f()
    F2 = [max(f[a] + f[R - a] for a in range(max(0, R - 63), min(R, 63) + 1)) for R in range(127)]
    bases = [b for b in range(5, bmax) if not T.is_pp(b)]
    H = {}
    for l in range(1, L + 1):
        tot = Fr(0)
        for b in bases:
            r = T.rlo(b); best = Fr(0)
            for t in range(grid):
                s, phi = Fr(0), 1 + Fr((b - 1) * t, grid)
                while phi < 64:
                    R = min(int(128 * r * 2 ** (6 * l) / phi), 126)
                    s += (int(phi + 2 * r) + 1) * F2[R]
                    phi *= b
                best = max(best, s)
            tot += best
        H[l] = tot
    E = T.load_e(); BS = sorted(E)
    def klo(c):
        k = Fr(BS[-1])
        for b0, b1 in zip(BS, BS[1:]):
            if E[b1] < c: k = min(k, b0 / (1 - E[b1] / c))
        return k
    for name, k1 in (("L1-optimistic (K_l=1 for l>=2)", True), ("floor (K_l=1 at every lag)", False)):
        worst, NI = None, 4000
        for j in range(NI):
            a, c = 1 + (G - 1) * Fr(j, NI), 1 + (G - 1) * Fr(j + 1, NI)
            K1 = klo(c) if k1 else 1
            lo = (K1 * H[1] / c + sum(H[l] / c ** l for l in range(2, L + 1))) / (G - a)
            if worst is None or lo < worst[0]: worst = (lo, a, c)
        print(f"{name}: CERTIFIED gap >= {float(worst[0]):.4f} [worst on [{float(worst[1]):.4f}, {float(worst[2]):.4f}]]")

if __name__ == '__main__':
    main()
