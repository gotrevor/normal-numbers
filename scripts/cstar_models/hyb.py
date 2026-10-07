#!/usr/bin/env python3
"""Hybrid engine: base 2 exact (Rosenfeld patterns); base 3 windows Lebesgue-precharged (u-weights)
from start level Ls (cells >= KS spacings) until kill level a+m, where the <= 2 boundary cells are
killed (Rosenfeld, charged to cnt(a)) and interior cells are dead for free; bases b >= 5 Rosenfeld
with per-stage optimal depth.
 Phi(L+1) >= 2Phi(L) - sum_l cnt(L+1-l) - drop3(L+1)*2cnt(L) - sum_{3-kills} 2cnt(a) - sum_{b>=5} T cnt(a)
 cnt(L) - Phi(L) <= sum_{pending 3-windows} excess
usage: hyb.py C K BMAX KS MFIX [P]   (MFIX=0: per-stage choice of m by cost estimate)"""
import sys, math
C = float(sys.argv[1]); K = int(sys.argv[2]); BMAX = int(sys.argv[3]); KS = float(sys.argv[4]); MFIX = int(sys.argv[5])
P = int(sys.argv[6]) if len(sys.argv) > 6 else 13
G0 = 1.75
thr = 2 ** -C
digs = []; x = thr
for i in range(P):
    x *= 2; d = int(x); digs.append(d); x -= d
pats = [i + 1 for i in range(P) if digs[i] == 1] + [P]
def ispp(b):
    for a in range(2, b):
        q = a
        while q < b: q *= a
        if q == b: return True
    return False
st3 = []  # (n, Ls, a, kill, w, sp)
rk = [[] for _ in range(K + 2)]
for b in range(3, BMAX):
    if ispp(b): continue
    d = b ** -C * 1.0001
    for n in range(0, 10 ** 6):
        sp = b ** -n; w = 2 * d * sp
        a = math.floor(-math.log2(sp - w)) + 1
        if a > K: break
        if b == 3:
            Ls = max(0, min(a, math.ceil(-math.log2(KS * sp))))
            if MFIX > 0: m = MFIX
            else:
                # choose m minimizing boundary 2/g^(m-1) + pending excess proxy sum_j w 2^(a+j) / g^j * 0.15
                best = None
                for mm in range(3, 16):
                    cst = 2 / G0 ** (mm - 1) + 0.15 * sum(min(2, w * 2 ** (a + j)) / G0 ** j for j in range(mm))
                    if best is None or cst < best[0]: best = (cst, mm)
                m = best[1]
            st3.append((n, Ls, a, a + m, w, sp))
        else:
            best = None
            for m in range(1, 40):
                T = min(math.floor(w * 2 ** (a + m)) + 2, 2 ** m + 1)
                cc = T / G0 ** m
                if best is None or cc < best[0]: best = (cc, m, T)
            if a + best[1] <= K: rk[a + best[1]].append((a, best[2]))
lphi = [0.0] * (K + 2); Cr = [1.0] * (K + 2)
worst = 9.0
for L in range(0, K):
    cell = 2.0 ** -L
    small = 0.0; big = 0.0
    for (n, Ls, a, kl, w, sp) in st3:
        if Ls > L or kl <= L: continue
        if a > L:
            small += (math.ceil(cell / sp) + 1) * min(2.0, w / cell)
        else:
            big += min(2.0, w / cell) * Cr[a] * math.exp(lphi[a] - lphi[L])
    if small >= 1: print('small blowup', L); break
    Cr[L] = (1 + big) / (1 - small)
    s = 2.0
    for l in pats:
        j = L + 1 - l
        if j >= 0: s -= Cr[j] * math.exp(lphi[j] - lphi[L])
    ncell = 2.0 ** -(L + 1)
    for (n, Ls, a, kl, w, sp) in st3:
        if Ls == L + 1:
            s -= min(1.0, (math.ceil(ncell / sp) + 1) * w / ncell) * 2 * Cr[L]
        if kl == L + 1:
            s -= 2 * Cr[a] * math.exp(lphi[a] - lphi[L])
    for (a, T) in rk[L + 1]:
        s -= T * Cr[a] * math.exp(lphi[a] - lphi[L])
    if s <= 0: print('DEAD at', L + 1); break
    lphi[L + 1] = lphi[L] + math.log(s)
    if L > 30: worst = min(worst, s)
print('C=%s KS=%s MFIX=%d: min ratio %.4f mean growth %.4f Cr %.3f' % (C, KS, MFIX, worst, math.exp((lphi[K] - lphi[30]) / (K - 30)), Cr[K - 1]))
