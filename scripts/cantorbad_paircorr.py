"""Numeric check of CantorBadNormal.ObstaclePairCorrelation.

Enumerates obst L (p/q in [0,1], 3^L <= q^2 3^5 < 3^{L+10}, within 2c0/q^2 of K, c0 = 1/(4 3^16)) by a
pruned Stern-Brocot DFS, then for xi = h b^m (m = least with b^m >= 3^{L+C}) prints, per S, the ratio
|sum_{pairs within 3^-S, distinct} e(xi (x-y))| / #pairs.  b = 3 is the coherent control.
usage: python3 cantorbad_paircorr.py L C
"""
import sys, cmath, math
from fractions import Fraction as F
sys.setrecursionlimit(10000)
c0 = F(1, 4 * 3 ** 16)

def meets(lo, hi, u=F(0), w=F(1)):
    if hi < u or lo > u + w:
        return False
    if lo <= u or hi >= u + w:
        return True
    w3 = w / 3
    return meets(lo, hi, u, w3) or meets(lo, hi, u + 2 * w3, w3)

def enum_obst(L):
    qlo2 = F(3 ** L, 3 ** 5); qhi2 = F(3 ** (L + 10), 3 ** 5)
    Q = math.isqrt(int(qhi2)) + 1
    out = []
    # include endpoints 0/1, 1/1
    for p, q in ((0, 1), (1, 1)):
        if qlo2 <= q * q < qhi2: out.append((p, q))
    stack = [(0, 1, 1, 1)]
    while stack:
        a, b, c, d = stack.pop()
        q = b + d
        if q > Q:
            continue
        r = 2 * c0 / (q * q)
        if not meets(F(a, b) - r, F(c, d) + r):
            continue
        p = a + c
        if qlo2 <= q * q < qhi2 and meets(F(p, q) - r, F(p, q) + r):
            out.append((p, q))
        stack.append((a, b, p, q)); stack.append((p, q, c, d))
    return out

def main():
    L, C = int(sys.argv[1]), int(sys.argv[2])
    ob = sorted(enum_obst(L), key=lambda x: F(x[0], x[1]))
    print(f"L={L} #obst={len(ob)}"); sys.stdout.flush()
    vals = [F(p, q) for p, q in ob]
    for b in (2, 5, 7, 3):
        xi = 1
        while xi < 3 ** (L + C): xi *= b
        ph = [cmath.exp(2j * math.pi * float((xi * v) % 1)) for v in vals]
        row = []
        for S in range(max(L - 12, 0), L + 1, 2):
            win = F(1, 3 ** S); tot = 0j; n = 0; j = 0
            for i in range(len(vals)):
                while vals[i] - vals[j] > win: j += 1
                for k in range(j, i):
                    if vals[k] != vals[i]:
                        tot += ph[i] * ph[k].conjugate(); n += 1
            row.append(f"S={S}:{abs(tot.real*2)/max(2*n,1):.3f}({n})")
        print(f"b={b} " + " ".join(row)); sys.stdout.flush()
main()
