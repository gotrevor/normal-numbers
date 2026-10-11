#!/usr/bin/env python3
"""Gate 5 lap 3: CRUDE COUNTING budget (no regularity, every step a worst case).

Scheme.  Fix a family (b, n), windows centred A/b^n, radius r_b/b^n, r_b = b^-4.49.  Let m' be the
largest block level with 2^(6m') <= b^n, phi = b^n / 2^(6m') in [1, 64).  A level-6m' cell meets at most
phi + 2 windows of the family.  At block m = m' + l (lag l >= 1) a window kills at most
min(64 rho, 126) Good children (rho = |W| 2^(6m) = 2 r_b 2^(6l)/phi; short windows: cells inside;
long: two straddling parents, 63 each).  Every window that kills meets a core-alive tail-alive
level-6m' cell, so the family kills at most (phi+2) min(64 rho,126) * N'(m') children, each of
weight <= 1, and N'(m') <= K mass(m') (comb comparability).  So loss(m) <= sum_l h_l mass(m-l) with
  h_l = K * sum_b sup_{phi0 in [1,b)} sum_{i: phi0 b^i < 64} (phi0 b^i + 2) min(64 rho, 126),
and the frozen crux needs sum_l h_l / gamma^l <= (9/5)^6 - gamma.  K = (1/w0)/(1 - e/gamma) from the
comb certificate (e = max low children per parent; tail5_comb.py: e = 12 at w0 = 1/3, e = 6 at 1/10).
This is a DESIGN screen (floats, sup over phi0 by a grid); every inequality in it is elementary.
"""
import math

def is_pp(b):
    return any(round(b ** (1 / e)) ** e == b for e in range(2, b.bit_length() + 1))

def kills_per_anc(b, l, grid=400):
    r = b ** -4.49
    best = 0.0
    for t in range(grid):
        phi0 = b ** (t / grid)          # phi0 in [1, b)
        tot, phi = 0.0, phi0
        while phi < 64:
            rho = 2 * r * 2 ** (6 * l) / phi
            k = min(math.floor(64 * rho), 126)
            tot += (phi + 2) * k
            phi *= b
        best = max(best, tot)
    return best

def main():
    G = (9 / 5) ** 6
    bases = [b for b in range(5, 4000) if not is_pp(b)]
    L = 12
    table = {}
    for l in range(1, L + 1):
        table[l] = sum(kills_per_anc(b, l) for b in bases if (2 * b ** -4.49 * 2 ** (6 * l)) * 64 / 64 >= 1 / 64 or True)
    for l in range(1, 6):
        per = [(b, kills_per_anc(b, l)) for b in bases[:6]]
        print(f"lag {l}: total over bases<4000 {table[l]:.4g}; bases 5..: " + ", ".join(f"{b}:{v:.3g}" for b, v in per))
    for (w0, e) in [(1 / 3, 12), (1 / 10, 6), (1 / 5, 9)]:
        best = None
        for gi in range(1, 400):
            g = e + 1e-6 + (G - e) * gi / 400
            if g >= G: break
            K = (1 / w0) / (1 - e / g)
            S = sum(K * table[l] / g ** l for l in table)
            slack = (G - g) - S
            if best is None or slack > best[0]: best = (slack, g, K, S)
        print(f"w0={w0:.3g}, e={e}: best gamma={best[1]:.3f}, K={best[2]:.3g}, sum h/gamma^l={best[3]:.4g} vs budget {G - best[1]:.4g} -> slack {best[0]:.4g}")

if __name__ == '__main__':
    main()
