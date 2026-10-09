#!/usr/bin/env python3
"""nu-measure engine with Markov state averaging.
a(L) >= a(L-1) - sum_{stage kills at L} rhobar * a(anc - d),  rhobar = sum_s rho_s max_s' P^d(s',s)
usage: meas2.py C MMAX BMAX K D [P]"""
import sys, math
C = float(sys.argv[1]); MMAX = int(sys.argv[2]); BMAX = int(sys.argv[3]); K = int(sys.argv[4]); D = int(sys.argv[5])
P = int(sys.argv[6]) if len(sys.argv) > 6 else 13
thr = 2 ** -C
digs = []; x = thr
for i in range(P):
    x *= 2; d = int(x); digs.append(d); x -= d
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
T = [[None, None] for _ in states]
for s in states:
    for dd in '01':
        t = step(s, dd); T[idx[s]][int(dd)] = None if t is None else idx[t]
r = [1.0] * n
for it in range(5000):
    nr = [sum(r[t] for t in T[i] if t is not None) for i in range(n)]
    lam = max(nr); r = [v / lam for v in nr]
# transition matrix P(s->t) = r(t)/(lam r(s))
Pm = [[0.0] * n for _ in range(n)]
for i in range(n):
    for t in T[i]:
        if t is not None: Pm[i][t] += r[t] / (lam * r[i])
def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
PD = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
for _ in range(D): PD = matmul(PD, Pm)
mx = [max(PD[i][s] for i in range(n)) for s in range(n)]
# stationary
pi = [1.0 / n] * n
for it in range(2000):
    pi = [sum(pi[i] * Pm[i][j] for i in range(n)) for j in range(n)]
print('lambda %.5f states %d  sum max P^d = %.4f (1 = perfect mixing)' % (lam, n, sum(mx)))
cache = {}
def condvec(s, m):
    vec = [(s, 1.0)]
    for k in range(m):
        nv = []
        for (st, p) in vec:
            for dd in (0, 1):
                if st is None: nv.append((None, 0.0)); continue
                t = T[st][dd]
                nv.append((None, 0.0) if t is None else (t, p * r[t] / (r[st] * lam)))
        vec = nv
    return [p for (_, p) in vec]
def rho_s(s, rw, m):
    N = 2 ** m
    span = math.floor(rw * N) + 2
    key = (s, m)
    if key not in cache: cache[key] = condvec(s, m)
    v = cache[key]
    # windows may hang over the edges: pad
    acc = 0.0; best = 0.0
    pad = [0.0] * span + v + [0.0] * span
    acc = sum(pad[:span]); best = acc
    for i in range(span, len(pad)):
        acc += pad[i] - pad[i - span]
        if acc > best: best = acc
    return best
def rhobar(rw, m):
    return sum(rho_s(s, rw, m) * mx[s] for s in range(n))
def ispp(b):
    for a in range(2, b):
        q = a
        while q < b: q *= a
        if q == b: return True
    return False
kills = [[] for _ in range(K + 2)]
info = {}
for b in range(3, BMAX):
    if ispp(b): continue
    dlt = b ** -C * 1.0001
    for st in range(0, 10 ** 6):
        sp = b ** -st
        w = 2 * dlt * sp
        a = math.floor(-math.log2(sp - w)) + 1
        if a > K: break
        rw = w * 2 ** a
        best = None
        for m in range(1, MMAX + 1):
            if a + m > K: break
            rb = rhobar(rw, m)
            if best is None or rb < best[0] * 0.995: best = (rb, m)
        if best is None: break
        kills[a + best[1]].append((a - D, best[0], b))
        info.setdefault(b, []).append((st, a, best[1], round(best[0], 4), round(rw, 4)))
lp = [0.0] * (K + 2)
worst = 1.0
for L in range(1, K + 1):
    s = 0.0
    for (aa, rr, b) in kills[L]:
        s += rr * math.exp(lp[L - 1] - lp[max(aa, 0)])
    q = 1 - s
    if q <= 0: print('DEAD at level', L); break
    lp[L] = lp[L - 1] + math.log(q); worst = min(worst, q)
print('C=%s D=%d: min q %.4f, mean decay/level %.4f' % (C, D, worst, 1 - math.exp(lp[K] / K)))
for b in (3, 5, 6):
    print(b, info.get(b, [])[:10])
