#!/usr/bin/env python3
"""Counting engine with per-stage optimal (ancestor, kill depth) for every base.
cnt(k+1) >= 2 cnt(k) - sum_pat cnt(k+1-l) - sum_windows T cnt(a).
usage: eng2.py C K BMAX g0 [P]"""
import sys, math
C = float(sys.argv[1]); K = int(sys.argv[2]); BMAX = int(sys.argv[3]); g0 = float(sys.argv[4])
P = int(sys.argv[5]) if len(sys.argv) > 5 else 13
thr = 2 ** -C
digs = []; x = thr
for i in range(P):
    x *= 2; d = int(x); digs.append(d); x -= d
pats = [i + 1 for i in range(P) if digs[i] == 1] + [P]  # lengths of 0-patterns (exact ones + conservative cut)
print('pattern lengths', pats)
def ispp(b):
    for a in range(2, b):
        q = a
        while q < b: q *= a
        if q == b: return True
    return False
kills = [[] for _ in range(K + 2)]
info3 = []
for b in range(3, BMAX):
    if ispp(b): continue
    d = b ** -C * 1.0001
    for n in range(0, 10 ** 6):
        sp = b ** -n
        a = math.floor(-math.log2(sp * (1 - 2 * d))) + 1  # 2^-a < sp(1-2d)
        if a > K: break
        w = 2 * d * sp
        best = None
        for m in range(1, 40):
            T = math.floor((w * 2 ** (a + m)) if b != 3 else (2 * d * 2 ** m)) + 2
            T = min(T, 2 ** m + 1)
            c = T / g0 ** m
            if best is None or c < best[0]: best = (c, m, T)
        c, m, T = best
        if a + m <= K: kills[a + m].append((a, T, b))
        if b == 3: info3.append((n, a, m, T, round(2 ** -a / sp, 3)))
q = [0.0] * (K + 2)
lp = [0.0] * (K + 2)  # lp[k] = log cnt(k) (normalized cnt(0)=1)
worst = 9
for k in range(0, K):
    s = 2.0
    for l in pats:
        j = k + 1 - l
        if j >= 0: s -= math.exp(lp[j] - lp[k])
    for (a, T, b) in kills[k + 1]:
        s -= T * math.exp(lp[a] - lp[k])
    if s <= 0:
        print('DEAD at', k + 1); break
    q[k] = s
    lp[k + 1] = lp[k] + math.log(s)
    if k > 30: worst = min(worst, s)
print('min ratio (k>30) %.4f, mean growth %.4f' % (worst, math.exp((lp[K] - lp[30]) / (K - 30))))
print('base3 stages (n,a,m,T,theta):', info3[:12])
if len(sys.argv) > 6:
    for k in range(int(sys.argv[6]), int(sys.argv[7])):
        print(k, round(q[k], 4), [(a, T, b) for (a, T, b) in kills[k + 1]][:6])
