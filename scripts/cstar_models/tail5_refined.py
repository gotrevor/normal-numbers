#!/usr/bin/env python3
"""Gate 5 relaunch: REFINED counting screen (DIRECTION.md, operator relaunch 2026-10-11).

Scheme (tail5_countbudget.py): loss(m) <= sum_l h_l mass(m-l),
  h_l = K * sum_b sup_phi0 sum_{i: phi=phi0 b^i < 64} cnt(phi) * F(rho),  rho = 2 r_b 2^(6l)/phi,
and the crux needs sum_l h_l/gamma^l <= (9/5)^6 - gamma.  GAP = min over gamma of sum/(budget).
Refinements (each switchable):
  (i)   F(rho) = max_{R1+R2 <= min(floor(64 rho),126), Ri <= 63} f(R1)+f(R2), f = W-weighted run sums
        (tail5_runsum.py), instead of min(floor(64 rho),126) children of weight 1;
  (ii)  K = min_beta beta/(1 - e'(beta)/gamma) (tail5_layercake.py) instead of (1/w0)/(1 - e/gamma), w0=1/3, e=12;
  (iii) cnt = floor(phi + 2 r_b) + 1 (exact max number of stage-n windows meeting an ancestor) instead of phi+2.
CERTIFIED DIRECTION: every quantity is a certified LOWER bound on what the scheme must use (exact
rationals; r_b lower enclosure; sup over phi0 by a rational grid; f, e' exhaustive maxima over the
dumped levels; bases truncated at BMAX).  So GAP > 1 certifies the scheme MISSES; GAP < 1 is not a close.
usage: tail5_refined.py BMAX GRID [crude|i|ii|iii combos, e.g. i,ii,iii] [drop57] [zero] [killall]
"""
import sys, ast
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
from pathlib import Path
getcontext().prec = 60
OUT = Path(__file__).parent / 'tail5_out'
G = Fr(9, 5) ** 6
MAXW = 1072633893121
L = 10

def rlo(b):
    return Fr(int((Decimal(b).ln() * Decimal("-4.49")).exp() * 10 ** 40) - 1, 10 ** 40)

def is_pp(b):
    return any(round(b ** (1 / e)) ** e == b for e in range(2, b.bit_length() + 1))

def load_f():
    line = [l for l in (OUT / 'runsum_k20.txt').read_text().splitlines() if l.startswith('exact')][0]
    d = ast.literal_eval(line.split(':', 1)[1])
    return [Fr(d[R], MAXW) for R in range(65)]

def load_e():
    line = [l for l in (OUT / 'layercake_k15.txt').read_text().splitlines() if l.startswith('exact')][0]
    d = ast.literal_eval(line.split(':', 1)[1])
    return {Fr(k): Fr(v) for k, v in d.items()}

def main():
    bmax, grid = int(sys.argv[1]), int(sys.argv[2])
    flags = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else set()
    f = load_f()
    if 'i' in flags:
        F2 = [max(f[a] + f[R - a] for a in range(max(0, R - 63), min(R, 63) + 1)) for R in range(127)]
    else:
        F2 = [Fr(R) for R in range(127)]
    if 'zero' in flags: F2 = [Fr(0)] * 127
    bases = [b for b in range(5, bmax) if not is_pp(b) and not ('drop57' in flags and b <= 7)]
    H = {}
    for l in range(1, L + 1):
        tot = Fr(0)
        for b in bases:
            r = rlo(b); best = Fr(0)
            for t in range(grid):
                phi0 = 1 + Fr((b - 1) * t, grid)
                s, phi = Fr(0), phi0
                while phi < 64:
                    R = min(int(128 * r * 2 ** (6 * l) / phi), 126)
                    cnt = (int(phi + 2 * r) + 1) if 'iii' in flags else phi + 2
                    s += cnt * F2[R]
                    phi *= b
                best = max(best, s)
            tot += best
        H[l] = tot
    if 'killall' in flags:   # control: every alive child of every ancestor killed at lag 1
        H = {1: Fr(64), **{l: Fr(0) for l in range(2, L + 1)}}
    E = load_e() if 'ii' in flags else {}
    BS = sorted(E)
    def klo(c):   # certified lower bound on min over ALL beta > 0 of K(beta, gamma) for gamma <= c
        if 'ii' not in flags:
            return Fr(3) / (1 - Fr(12) / c) if c > 12 else None
        k = Fr(BS[-1])                       # beta >= max grid: K >= beta
        for b0, b1 in zip(BS, BS[1:]):       # beta < BS[0]: e' >= E[BS[0]] > G, infeasible
            if E[b1] < c: k = min(k, b0 / (1 - E[b1] / c))
        return k
    assert 'ii' not in flags or E[BS[0]] > G
    # certified sweep over gamma in (1, G): on [a, c], sum >= K(c) sum_l H_l/c^l, budget <= G - a
    worst, NI = None, 4000
    for j in range(NI):
        a, c = 1 + (G - 1) * Fr(j, NI), 1 + (G - 1) * Fr(j + 1, NI)
        k = klo(c)
        if k is None: continue        # crude K undefined (gamma <= e): scheme gives no bound there
        lo = k * sum(H[l] / c ** l for l in H) / (G - a)
        if worst is None or lo < worst[0]: worst = (lo, a, c)
    n = NI
    # point estimate at the best grid gamma (design number)
    res = None
    for gi in range(1, 2000):
        g = 1 + (G - 1) * Fr(gi, 2000)
        k = klo(g)
        if k is None: continue
        S = sum(k * H[l] / g ** l for l in H)
        gap = S / (G - g)
        if res is None or gap < res[0]: res = (gap, g, k, S)
    gap, g, K, S = res
    print(f"flags={sorted(flags)} BMAX={bmax} GRID={grid}: h_l(l=1..5)=" + ", ".join(f"{float(H[l]):.4g}" for l in range(1, 6)))
    print(f"  best gamma~{float(g):.4f} K={float(K):.4f} sum={float(S):.5g} budget={float(G - g):.5g} GAP~{float(gap):.4f}")
    print(f"  CERTIFIED: gap >= {float(worst[0]):.4f} for every gamma in (1, (9/5)^6) [{n} intervals; worst on [{float(worst[1]):.5f}, {float(worst[2]):.5f}]]")

if __name__ == '__main__':
    main()
