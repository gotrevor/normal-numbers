# Exact entry states for CleanCertificate449 with the exact3.c integer weights.
# Early cells (k <= 4): w(k,a) = min(1, (5/9)^D * sum over good level-(k+D) descendants of w(class)/maxW).
# Descendant goodness: SFT-alive (=> Acc2) and disjoint from every resolved base-3 window, decided with the
# delta3 enclosure [dlo, dhi] (ambiguous => counted as dead, sound).  Class bins use the exact3 edges
# (ambiguous => min over candidate bins).
# usage: python3 entry_exact.py W449.txt exact3_edges449.txt
import sys, json
from fractions import Fraction as Fr
N, M, D = 128, 24, 6
W = [int(l) for l in open(sys.argv[1])]
E = {}; edges = []
for l in open(sys.argv[2]):
    k, v, _ = l.split(); v = Fr(int(v), 2**90)
    if k == 'edge': edges.append(v)
    else: E[k] = v
dlo, dhi = E['dlo'], E['dhi']
sft = json.load(open('sft449.json')); T = sft['T']
mx = max(W)
def state(k, a):
    s = 0
    for i in range(k - 1, -1, -1):
        s = T[s][(a >> i) & 1]
        if s < 0: return -1
    return s
def clean(k, a):  # all stages with 3^n <= 2 delta 2^k resolved and disjoint; None if ambiguous
    n = 0
    while True:
        r = Fr(3**n, 2**k)
        if r > 2 * dhi: return True
        if r > 2 * dlo: return None  # ambiguous resolution
        lo, hi = Fr(3**n * a, 2**k), Fr(3**n * (a + 1), 2**k)
        import math
        for A in range(math.floor(lo) - 1, math.ceil(hi) + 2):
            if hi < A - dhi or lo > A + dhi: continue
            if hi < A - dlo or lo > A + dlo: return None
            return False
        n += 1
def wreg(k, a):
    s = state(k, a)
    if s < 0: return Fr(0)
    c = clean(k, a)
    if c is not True: return Fr(0)
    n = 0
    while Fr(3**n, 2**k) <= 2 * dhi: n += 1
    r = Fr(3**n, 2**k); assert r > 2 * dhi and r <= 6 * dlo, (k, r)
    x = Fr(3**n * a, 2**k); x -= x.numerator // x.denominator
    i = int(x * N)
    js = [j for j in range(M) if edges[j] <= r <= edges[j + 1]]
    return Fr(min(W[s * N * M + i * M + j] for j in js), mx)
memo = {}
def w(k, a):
    if k >= 5: return wreg(k, a)
    if (k, a) in memo: return memo[(k, a)]
    if state(k, a) < 0: memo[(k, a)] = Fr(0); return Fr(0)
    sm = sum(w(k + D, (a << D) + j) for j in range(2 ** D))
    v = min(Fr(1), sm * Fr(5, 9) ** D); memo[(k, a)] = v; return v
root = w(0, 0)
print('root weight', root, float(root))
print('early cells', len(memo), 'positive', sum(1 for v in memo.values() if v > 0))
print('min positive early', float(min(v for v in memo.values() if v > 0)))
