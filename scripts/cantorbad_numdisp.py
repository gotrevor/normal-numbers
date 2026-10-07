"""Numerator-averaging dispersion probe for the preperiodic obstacle families (run directive 2026-10-06 evening).

Family: obstacles p/q in obst L whose 3-free denominator part q' divides 3^l +- 1 (l <= 8).  CRT
(`obstacle_phase_crt`): e(B p/(q'3^j)) = e(B a/q') e(B c/3^j); c = 3-adic numerator.  For each (cell of
width 3^-S, j) group G with numerators c_x, Z_G(a) = sum_x e(a c_x / 3^j) / |G|.
  A  = mean over ALL a mod 3^j of |Z|^2          (numerator dispersion; sqrt-cancellation in a = 1/|G|)
  B  = mean over a = h b^m mod 3^j, m0 <= m < m0+N of |Z|^2   (what AliveOffMix needs)
  LS = 3^j / (N |G|)   large-sieve transfer factor from A to the sparse set {b^m}: <1 needed
Controls: b = 3 (B must be 1) and dyadic centres p/2^k with a = 2^m (B = 1 identically, printed).
usage: python3 cantorbad_numdisp.py L S N
"""
import sys, cmath, math
from fractions import Fraction as F
from collections import defaultdict
L, S, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
exec(open('scripts/cantorbad_paircorr.py').read().split('def main')[0])
ob = set(F(p, q) for p, q in enum_obst(L))
def split(d):
    j = 0
    while d % 3 == 0: d //= 3; j += 1
    return d, j
groups = defaultdict(list)
for v in ob:
    qp, j = split(v.denominator)
    if j < 2 or not any((3**l - 1) % qp == 0 or (3**l + 1) % qp == 0 for l in range(1, 9)): continue
    M = 3**j
    c = (v.numerator * pow(qp, -1, M)) % M
    groups[(math.floor(v * 3**S), j)].append(c)
gs = [(k, cs) for k, cs in groups.items() if len(cs) >= 4]
def Z2(a, cs, M):
    z = sum(cmath.exp(2j * math.pi * (a * c % M) / M) for c in cs) / len(cs)
    return abs(z) ** 2
print(f"L={L} S={S} N={N} groups={len(gs)} sizes={sorted(len(c) for _, c in gs)[-5:]}")
m0 = 10
for b in (2, 5, 7, 3):
    Bs, As, LSs = [], [], []
    for (cell, j), cs in gs:
        M = 3**j
        coll = sum(1 for x in cs for y in cs if (x - y) % M == 0) / len(cs)**2
        As.append(coll)                       # exact full-a mean square (Parseval)
        Bs.append(sum(Z2(pow(b, m, M), cs, M) for m in range(m0, m0 + N)) / N)
        LSs.append(M / (N * len(cs)))
    k = len(gs)
    print(f"b={b}: A={sum(As)/k:.4f}  B={sum(Bs)/k:.4f}  maxB={max(Bs):.3f}  LS median={sorted(LSs)[k//2]:.1f}")
print("dyadic control: centres p/2^k, a=2^m: e(2^m p/2^k)=1 for m>=k, B=1 by construction")
