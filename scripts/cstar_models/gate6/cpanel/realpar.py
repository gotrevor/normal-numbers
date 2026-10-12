# (iii-b) concrete REAL parents: binary cells (n, a), n = 6t, SFT state s from state 0 (MSB first), good under the
# real semantics (true delta_b = b^-4.49; for every base and every stage m' with b^m'/2^n <= 2 delta, the interval
# [b^m' a, b^m' (a+1)]/2^n avoids every closed window [A - delta, A + delta]), signature in the pair's closed bins.
# Exact block value: sum over the 64 children (n+6, 64a+p) that are SFT-alive and good of the frozen joint weight at
# the child's signature (min and max over the closed bin pairs containing it; exception override).  Independent of
# the C evaluator's box semantics.
import sys, random, math
from decimal import Decimal, getcontext
NB3, NB5, M3, M5, N3, N5, S = 128*24, 64*13, 24, 13, 128, 64, 25
E = {}
for l in open('edges.txt'):
    k, v = l.split(); E.setdefault(k, []).append(int(v))
R3, R5, X5 = E['redge3'], E['redge5'], E['xedge5']
src = open('../../scripts/cstar_models/sft449.h').read()
T = eval(src.split('T[S][2] = ')[1].split(';')[0].replace('{', '[').replace('}', ']'))
LS = [[None]*64 for _ in range(S)]
for q in range(S):
    for p in range(64):
        st = q
        for d in range(5, -1, -1):
            if st < 0: break
            st = T[st][(p >> d) & 1]
        LS[q][p] = st
NMAX = 13000
getcontext().prec = 4200
DFL = {}
for b in (3, 5):
    d = (Decimal(b).ln() * Decimal('-4.49')).exp()
    DFL[b] = int(d * (Decimal(2) ** (NMAX + 64)))   # floor(delta * 2^(NMAX+64)) up to < 1e-100 relative
def dfl(b, l):   # floor(delta_b * 2^l), exact unless astronomically close (guarded)
    v = DFL[b] >> (NMAX + 64 - l); fr = DFL[b] - (v << (NMAX + 64 - l))
    assert 1000 < fr < (1 << (NMAX + 64 - l)) - 1000
    return v
def scale(b, n):   # m = first exponent with b^m / 2^n > 2 delta, i.e. b^m > floor(2 delta 2^n) (irrational, exact)
    D2 = dfl(b, n + 1); m = max(0, int((n - 12) / math.log2(b))); p = b ** m
    while m > 0 and p > D2: m -= 1; p //= b
    while p <= D2: m += 1; p *= b
    return m, p
def cell_good_base(b, n, a, m):   # all stages m' < m
    D = dfl(b, n); one = 1 << n; p = 1
    for mp in range(m):
        L = p * a; H = L + p
        A0 = L >> n
        for A in (A0, A0 + 1):
            if H + D >= A * one and L <= A * one + D: return False
        p *= b
    return True
def sft_state(a, n):
    s = 0
    for i in range(n - 1, -1, -1):
        s = T[s][(a >> i) & 1]
        if s < 0: return -1
    return s
def bins_x3(X, n):   # closed x3 bins of X / 2^n
    i = (X * N3) >> n; out = [i % N3]
    if (i << n) == X * N3: out.append((i - 1) % N3)
    return out
def bins_closed(V, n, edges):   # indices j with edges[j] <= V/2^n * 2^90 <= edges[j+1]
    v = V << 90
    return [j for j in range(len(edges) - 1) if (edges[j] << n) <= v <= (edges[j + 1] << n)]
def sig(b, n, a):
    m, p = scale(b, n); X = (p * a) % (1 << n); return m, p, X
def wjoint(t, b3s, b5s, W3, PHI, EX):
    vals = []
    for r3 in b3s:
        for r5 in b5s:
            q5 = t * NB5 + r5; w = W3[t * NB3 + r3] * PHI[q5]; e = EX.get((q5, r3))
            vals.append(min(w, e) if e is not None else w)
    return min(vals), max(vals)
def binsets(n, a):
    m3, p3, X3 = sig(3, n, a); m5, p5, X5_ = sig(5, n, a)
    xs3 = bins_x3(X3, n); rs3 = bins_closed(p3, n, R3)
    xs5 = [i for i in range(N5) if (X5[i] << n) <= (X5_ << 90) <= (X5[i + 1] << n)]
    rs5 = bins_closed(p5, n, R5)
    return [i * M3 + j for i in xs3 for j in rs3], [i * M5 + j for i in xs5 for j in rs5], (m3, m5, X3, X5_, p3, p5)
def good(n, a):
    m3, _ = scale(3, n); m5, _ = scale(5, n)
    return cell_good_base(3, n, a, m3) and cell_good_base(5, n, a, m5)
def block_value(n, a, s, W3, PHI, EX):
    lo = hi = 0
    for p in range(64):
        t = LS[s][p]
        if t < 0: continue
        c = a * 64 + p
        if not good(n + 6, c): continue
        b3s, b5s, _ = binsets(n + 6, c)
        l, h = wjoint(t, b3s, b5s, W3, PHI, EX); lo += l; hi += h
    return lo, hi
