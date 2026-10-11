#!/usr/bin/env python3
"""Gate 5 operator lever probe (DIRECTION.md 2026-10-11): lever (L2) MASS charging on top of
tail5_refined.py with (i)+(ii)+(iii).

Refined scheme, per family (b, n) with ancestor level m' and lag l: total kill <= sum over core-alive
ancestors a of s_a, s_a = sum_i cnt_i F2a(R_i) (F2a = per-ancestor descendant run sums,
tail5_lever_data.py).  The refined screen bounds this by N'(m') max_a s_a <= K mass(m') max_a s_a.
(L2) layer-cake against the ancestor's own weight: for any beta >= 0,
    sum_a s_a <= beta sum_a W(a) + sum_a (s_a - beta W(a))^+ <= (beta + K E(beta)) mass(m'),
    E(beta) = max_a (s_a - beta W(a))^+,
a totals bound (beta mass is the TOTAL mass; nothing is normalized by one cell's mass).  Applied to
bases in L2BASES at lags with per-ancestor data; other (b, l) keep K * max (as tail5_refined).
CERTIFIED DIRECTION as tail5_refined: every input is a certified LOWER bound on what the scheme uses
(E: exhaustive max over the dumped levels; min over beta by bracketing), so GAP > 1 certifies a miss;
GAP < 1 is a design number (the maxima are not yet uniform upper bounds).
usage: tail5_lever.py BMAX GRID [L2|beta0] [L1opt]
  beta0 : control, L2 machinery with beta forced to 0 (must reproduce the refined screen up to levels)
  L1opt : optimistic lever L1 (see opt_l1), a NON-certified upper-favourable screen: if it misses, L1 is dead
"""
import sys, pickle
from fractions import Fraction as Fr
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import tail5_refined as T
OUT = Path(__file__).parent / 'tail5_out' / 'lever'
G, MAXW, L = T.G, T.MAXW, T.L
L2BASES = (5, 6, 7)
BETAS = [Fr(0)] + [Fr(n, 8) for n in range(1, 64)] + [Fr(n, 2) for n in range(16, 400)]

def load_anc(l):
    rows = []
    for p in sorted(OUT.glob(f'anc_k*_l{l}.pkl')):
        rows += pickle.load(open(p, 'rb'))
    return rows

def hull(P):   # upper hull of points sorted by x (max of s - beta W over P is attained on it)
    h = []
    for x, y in P:
        while len(h) >= 2 and (h[-1][0] - h[-2][0]) * (y - h[-2][1]) >= (h[-1][1] - h[-2][1]) * (x - h[-2][0]):
            h.pop()
        h.append((x, y))
    return h

def coeffs(b, l, phi0, r):
    c, phi = {}, phi0
    while phi < 64:
        R = min(int(128 * r * 2 ** (6 * l) / phi), 126)
        c[R] = c.get(R, 0) + (int(phi + 2 * r) + 1)
        phi *= b
    return c

def main():
    bmax, grid = int(sys.argv[1]), int(sys.argv[2])
    flags = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else set()
    f = T.load_f()
    F2 = [max(f[a] + f[R - a] for a in range(max(0, R - 63), min(R, 63) + 1)) for R in range(127)]
    bases = [b for b in range(5, bmax) if not T.is_pp(b)]
    lags_data = [l for l in range(1, L + 1) if list(OUT.glob(f'anc_k*_l{l}.pkl'))]
    A = {l: Fr(0) for l in range(1, L + 1)}       # coefficient of K (refined screen part)
    Ez = {}                                        # (b, l) -> max s over weight-0 ancestors: E(beta) >= Ez for all beta
    Ecurve = {}                                    # (b, l) -> [E(beta) for beta in BETAS]
    anc = {l: load_anc(l) for l in lags_data}
    for l in range(1, L + 1):
        for b in bases:
            r = T.rlo(b)
            if b in L2BASES and l in lags_data and ('L2' in flags or 'beta0' in flags):
                for j in range(0, l + 1):          # charge beta * (depth-j mass) to lag l - j
                    E = [Fr(0)] * len(BETAS)
                    for t in range(grid):
                        c = coeffs(b, l, 1 + Fr((b - 1) * t, grid), r)
                        pts = {}
                        for Wt, F2a in anc[l]:
                            v = sum(n * F2a[R] for R, n in c.items())
                            if v > pts.get(Wt[j], -1): pts[Wt[j]] = v
                        H = hull(sorted(pts.items()))
                        Ez[(b, l, j)] = max(Ez.get((b, l, j), Fr(0)), Fr(pts.get(0, 0), MAXW))
                        for i, be in enumerate(BETAS):
                            e = max(0, max(s * be.denominator - be.numerator * W for W, s in H))
                            e = Fr(e, be.denominator * MAXW)
                            if e > E[i]: E[i] = e
                    Ecurve[(b, l, j)] = E
                    print(f"  b={b} l={l} j={j}: E(0)={float(E[0]):.4g} E(1)={float(E[8]):.4g} E(16)={float(E[BETAS.index(16)]):.4g} "
                          f"E(64)={float(E[BETAS.index(64)]):.4g} E(199)={float(E[-1]):.4g} Ez={float(Ez[(b, l, j)]):.4g}", flush=True)
            else:
                best = Fr(0)
                for t in range(grid):
                    c = coeffs(b, l, 1 + Fr((b - 1) * t, grid), r)
                    best = max(best, sum(n * F2[R] for R, n in c.items()))
                A[l] += best
    E2 = T.load_e(); BS = sorted(E2)
    def klo(c):
        k = Fr(BS[-1])
        for b0, b1 in zip(BS, BS[1:]):
            if E2[b1] < c: k = min(k, b0 / (1 - E2[b1] / c))
        return k
    def lever_lo(E, K, c, l, j):   # certified lower bound on min_beta (beta / c^(l-j) + K E(beta) / c^l)
        if 'beta0' in flags: return K * E[0] / c ** l
        d = c ** (l - j)
        best = BETAS[-1] / d + K * E[-1] / c ** l
        for i in range(len(BETAS) - 1):
            best = min(best, BETAS[i] / d + K * E[i + 1] / c ** l)
        return best
    def lever_at(E, K, c, l, j):   # value at the best grid beta (design number)
        if 'beta0' in flags: return K * E[0] / c ** l
        return min(be / c ** (l - j) + K * e / c ** l for be, e in zip(BETAS, E))
    def total(c, K, lev):
        s = sum(K * A[l] / c ** l for l in A)
        for (b, l) in {(b, l) for (b, l, j) in Ecurve}:
            js = [0] if 'beta0' in flags else range(l + 1)
            s += min(max(lev(Ecurve[(b, l, j)], K, c, l, j), K * Ez[(b, l, j)] / c ** l) for j in js)
        return s
    worst, NI = None, 4000
    for j in range(NI):
        a, c = 1 + (G - 1) * Fr(j, NI), 1 + (G - 1) * Fr(j + 1, NI)
        lo = total(c, klo(c), lever_lo) / (G - a)
        if worst is None or lo < worst[0]: worst = (lo, a, c)
    res = None
    for gi in range(1, 2000):
        g = 1 + (G - 1) * Fr(gi, 2000)
        S = total(g, klo(g), lever_at)
        if res is None or S / (G - g) < res[0]: res = (S / (G - g), g, klo(g), S)
    gap, g, K, S = res
    print(f"flags={sorted(flags)} BMAX={bmax} GRID={grid} L2 lags={lags_data}")
    print(f"  best gamma~{float(g):.4f} K={float(K):.4f} sum={float(S):.5g} budget={float(G - g):.5g} GAP~{float(gap):.4f}")
    print(f"  CERTIFIED: gap >= {float(worst[0]):.4f} for every gamma in (1, (9/5)^6) [{NI} intervals; worst on [{float(worst[1]):.5f}, {float(worst[2]):.5f}]]")

if __name__ == '__main__':
    main()
