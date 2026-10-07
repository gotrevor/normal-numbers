#!/usr/bin/env python3
"""nu-precharge engine.  Phi(L) = nu(E_L), E_L = SFT minus windows of stages started by level L.
N(L) = nu(alive level-L cells).  Positivity of Phi for all L suffices.
 Phi(L+1) >= Phi(L) - sum_{stages starting at L+1} Mdrop * N(L)
 N(L)(1 - sum_{started, a > L} Mdrop) <= Phi(L) + sum_{a <= L} fbar(L-a) * N(a - D)
Mdrop = max_{s0} sum_s P^{DS}(s0,s) G(s),  G(s) = max_x nu_s(cells at depth MD touched by window, rel size rw)
fbar(j) = sum_s max_{s'} P^D(s',s) * max_x min(nu_s(window), nu_s(<=2 boundary cells at depth j)).
usage: nupre.py C BMAX K D DS MD [P]"""
import sys, math
C = float(sys.argv[1]); BMAX = int(sys.argv[2]); K = int(sys.argv[3]); D = int(sys.argv[4]); DS = int(sys.argv[5]); MD = int(sys.argv[6])
P = int(sys.argv[7]) if len(sys.argv) > 7 else 13
thr = 2 ** -C
digs = []; x = thr
for i in range(P):
    x *= 2; dd = int(x); digs.append(dd); x -= dd
F = []
for i in range(P):
    if digs[i] == 1: F.append(''.join(map(str, digs[:i])) + '0')
F.append(''.join(map(str, digs[:P])))
F = sorted(set(F), key=len)
F = F + [''.join('1' if c == '0' else '0' for c in w) for w in F]
pref = set([''])
for w in F:
    for i in range(len(w)): pref.add(w[:i])
def step(s, dd):
    t = s + dd
    if any(t.endswith(w) for w in F): return None
    while t not in pref: t = t[1:]
    return t
states = sorted(pref, key=lambda s: (len(s), s)); n = len(states)
idx = {s: i for i, s in enumerate(states)}
T = [[None if step(s, dd) is None else idx[step(s, dd)] for dd in '01'] for s in states]
r = [1.0] * n
for it in range(5000):
    nr = [sum(r[t] for t in T[i] if t is not None) for i in range(n)]
    lam = max(nr); r = [v / lam for v in nr]
Pm = [[0.0] * n for _ in range(n)]
for i in range(n):
    for t in T[i]:
        if t is not None: Pm[i][t] += r[t] / (lam * r[i])
def matpow(dd):
    R = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    for _ in range(dd):
        R = [[sum(R[i][k] * Pm[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    return R
PD = matpow(D); mxD = [max(PD[i][s] for i in range(n)) for s in range(n)]
PS = matpow(DS)
cache = {}
def condvec(s, m):
    if (s, m) in cache: return cache[(s, m)]
    vec = [(s, 1.0)]
    for k in range(m):
        nv = []
        for (st, p) in vec:
            for dd in (0, 1):
                if st is None: nv.append((None, 0.0)); continue
                t = T[st][dd]
                nv.append((None, 0.0) if t is None else (t, p * r[t] / (r[st] * lam)))
        vec = nv
    out = [p for (_, p) in vec]; cache[(s, m)] = out; return out
def wmass(s, rw, m):
    """max over positions of nu_s(cells at depth m touched by window of rel length rw)"""
    v = condvec(s, m); Nn = 2 ** m
    span = math.floor(rw * Nn) + 2
    pad = [0.0] * span + v + [0.0] * span
    acc = sum(pad[:span]); best = acc
    for i in range(span, len(pad)):
        acc += pad[i] - pad[i - span]
        if acc > best: best = acc
    return best
def emass(s, rw, j):
    """max over positions of min(nu_s(window), nu_s(two boundary cells at depth j)) (approx: window via depth MD)"""
    if j <= 0: return wmass(s, rw, MD)
    two = 2 * maxcell(s, j)
    return min(wmass(s, rw, MD), two)
MC = {}
def maxcell(s, j):
    if (s, j) in MC: return MC[(s, j)]
    if j <= 13: v = max(condvec(s, j))
    else: v = max(condvec(s, 13)) * max(maxcell(t, j - 13) for t in range(n))
    MC[(s, j)] = v; return v
def ispp(b):
    for a in range(2, b):
        q = a
        while q < b: q *= a
        if q == b: return True
    return False
stages = []  # (b, n, Ls, a, rw)
for b in range(3, BMAX):
    if ispp(b): continue
    dl = b ** -C * 1.0001
    for st in range(0, 10 ** 6):
        sp = b ** -st; w = 2 * dl * sp
        a = math.floor(-math.log2(sp - w)) + 1
        if a - DS > K: break
        rw = w * 2 ** a
        stages.append((b, st, max(0, a - DS), a, rw))
G = {}
def Mdrop(rw):
    key = round(rw, 6)
    if key not in G:
        g = [wmass(s, rw, MD) for s in range(n)]
        G[key] = max(sum(PS[s0][s] * g[s] for s in range(n)) for s0 in range(n))
    return G[key]
FB = {}
def fbar(rw, j):
    key = (round(rw, 6), j)
    if key not in FB:
        FB[key] = sum(mxD[s] * emass(s, rw, j) for s in range(n))
    return FB[key]
starts = [[] for _ in range(K + 2)]
for stg in stages:
    if stg[2] <= K: starts[stg[2]].append(stg)
lphi = [0.0] * (K + 2); Cr = [1.0] * (K + 2)
worst = 1.0
for L in range(0, K):
    sm = 0.0; bg = 0.0
    for (b, st, Ls, a, rw) in stages:
        if Ls > L: continue
        if a > L: sm += Mdrop(rw)
        else:
            j = L - a; aa = max(a - D, 0)
            bg += fbar(rw, j) * Cr[aa] * math.exp(lphi[aa] - lphi[L])
    if sm >= 1: print('small blowup', L); break
    Cr[L] = (1 + bg) / (1 - sm)
    drop = sum(Mdrop(stg[4]) for stg in starts[L + 1]) * Cr[L]
    q = 1 - drop
    if q <= 0: print('DEAD at', L + 1, 'Cr', Cr[L], 'drop', drop); break
    lphi[L + 1] = lphi[L] + math.log(q); worst = min(worst, q)
    if len(sys.argv) > 8 and L % int(sys.argv[8]) == 0:
        print(L, 'q %.4f Cr %.3f small %.4f big %.4f drop %.4f' % (q, Cr[L], sm, bg, drop))
print('C=%s D=%d DS=%d MD=%d: min q %.4f  mean decay %.4f  Cr(K-1) %.3f' % (C, D, DS, MD, worst, 1 - math.exp(lphi[K] / K), Cr[K - 1]))
print('base-3 Mdrop samples:', [round(Mdrop(s[4]), 4) for s in stages if s[0] == 3][:8])
