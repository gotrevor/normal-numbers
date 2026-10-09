#!/usr/bin/env python3
"""Lebesgue-precharged counting engine.
alive cell D at level L: binary word avoids base-2 patterns, u(D) > 0, where u(D) = Lebesgue share of D
not covered by pending windows (all b >= 3 non-perfect-power, stages n with start level <= L).
Phi(L) = sum_alive u(D);  cnt(L) = #alive.
 Phi(L+1) >= 2 Phi(L) - sum_l cnt(L+1-l) - sum_{(b,n) starting at L+1} M_{b,n} * 2 cnt(L)
 cnt(L) - Phi(L) <= sum_{(b,n) started} e_{b,n}(L) N_{b,n}(L)
usage: leb.py C K BMAX KS [P]"""
import sys, math
C = float(sys.argv[1]); K = int(sys.argv[2]); BMAX = int(sys.argv[3]); KS = float(sys.argv[4]); PRE = int(sys.argv[8]) if len(sys.argv) > 8 else 3
P = int(sys.argv[5]) if len(sys.argv) > 5 else 13
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
stages = []  # (b, n, Ls, a, w, sp)
rkills = [[] for _ in range(K + 2)]
for b in range(3, BMAX):
    if ispp(b): continue
    d = b ** -C * 1.0001
    for n in range(0, 10 ** 6):
        sp = b ** -n
        w = 2 * d * sp
        a = math.floor(-math.log2(sp - w)) + 1  # 2^-a < sp - w : each level-a cell touches <= 1 window
        Ls = max(0, math.ceil(-math.log2(KS * sp)))  # cells of size >= KS*sp ... (start level)
        Ls = min(Ls, a)
        if Ls > K: break
        if b <= PRE: stages.append((b, n, Ls, a, w, sp))
        else:
            best = None
            for m in range(1, 40):
                T = min(math.floor(w * 2 ** (a + m)) + 2, 2 ** m + 1)
                cc = T / 1.75 ** m
                if best is None or cc < best[0]: best = (cc, m, T)
            if a + best[1] <= K: rkills[a + best[1]].append((a, best[2]))
starts = [[] for _ in range(K + 2)]
for s in stages: starts[s[2]].append(s)
lphi = [0.0] * (K + 2)  # log Phi
Cr = [1.0] * (K + 2)    # cnt/Phi upper bound
def Mshare(s, L):
    b, n, Ls, a, w, sp = s
    cell = 2.0 ** -L
    return min(1.0, (math.ceil(cell / sp) + 1) * w / cell)
def excess(L):
    """returns (small_share, big_sum_over_Phi(L))"""
    small = 0.0; big = 0.0
    cell = 2.0 ** -L
    for s in stages:
        b, n, Ls, a, w, sp = s
        if Ls > L: continue
        e = min(2.0, w / cell)
        # option (i): per-cell count at level L
        opt1 = (math.ceil(cell / sp) + 1) * e  # times cnt(L)
        # option (ii): cnt(a) if a <= L
        if a <= L:
            opt2 = e * Cr[a] * math.exp(lphi[a] - lphi[L])  # times Phi(L)
            # choose the smaller in Phi-units assuming cnt(L) ~ Cr*Phi; use opt2 if a<=L
            if opt2 < opt1 * 1.0: big += opt2
            else: small += opt1
        else:
            small += opt1
    return small, big
# Phi(0) and cnt(0): level-0 cell [0,1]
worst = 9
for L in range(0, K):
    # cnt(L) <= Cr[L] Phi(L)
    sm, bg = excess(L)
    if sm >= 1:
        print('excess blowup at', L, sm); break
    Cr[L] = (1 + bg) / (1 - sm)
    # Phi(L+1) >= 2Phi(L) - sum_l cnt(L+1-l) - drop
    s = 2.0
    for l in pats:
        j = L + 1 - l
        if j >= 0: s -= Cr[j] * math.exp(lphi[j] - lphi[L])
    drop = sum(Mshare(st, L + 1) for st in starts[L + 1]) * 2 * Cr[L]
    for (a, T) in rkills[L + 1]: drop += T * Cr[a] * math.exp(lphi[a] - lphi[L])
    s -= drop
    if s <= 0:
        print('DEAD at', L + 1); break
    lphi[L + 1] = lphi[L] + math.log(s)
    if L > 30: worst = min(worst, s)
    if len(sys.argv) > 6 and int(sys.argv[6]) <= L < int(sys.argv[7]):
        print(L, 'ratio %.4f Cr %.4f small %.4f big %.4f drop %.4f' % (s, Cr[L], sm, bg, drop))
print('C=%s KS=%s min ratio (L>30) %.4f, mean growth %.4f, final Cr %.4f' % (C, KS, worst, math.exp((lphi[K] - lphi[30]) / (K - 30)), Cr[K - 1]))
