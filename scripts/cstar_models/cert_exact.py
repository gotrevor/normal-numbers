# Exact-rational survivor sweep that records the windows it uses, then extracts a chain cover
# for not_admissible_of_cert.  Usage: cert_exact.py num den B CAP DIGITS
import math, sys, json
from fractions import Fraction as F
num, den, B, cap, dig = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(float(sys.argv[4])), int(sys.argv[5])
ds = {}
for b in range(2, B + 1):
    d = F(math.floor(b ** (-num / den) * 10 ** dig * (1 - 1e-12)), 10 ** dig)
    while d ** den * b ** num > 1: d -= F(1, 10 ** dig)
    ds[b] = d
cons = sorted((b ** n, b, n) for b in range(2, B + 1) for n in range(0, 80) if b ** n <= cap)
iv = [(F(0), F(1))]; used = set()
for s, b, n in cons:
    d = ds[b]; out = []
    for lo, hi in iv:
        k0 = math.floor(lo * s - d); k1 = math.ceil(hi * s + d); cur = lo
        for k in range(k0, k1 + 1):
            a, bb = (k - d) / s, (k + d) / s
            if bb < cur or a > hi: continue
            used.add((b, n, k))
            if a > cur: out.append((cur, min(a, hi)))
            cur = max(cur, bb)
            if cur >= hi: break
        if cur < hi: out.append((cur, hi))
    iv = [x for x in out if x[1] > x[0]]
    if not iv: break
print('survivors', len(iv), file=sys.stderr)
assert not iv
W = sorted(((F(k) - ds[b]) / b ** n, (F(k) + ds[b]) / b ** n, b, n, k) for b, n, k in used)
cur = F(0); out = []; i = 0; best = None
while cur < 1:
    while i < len(W) and W[i][0] <= cur:
        if best is None or W[i][1] > best[1]: best = W[i]
        i += 1
    assert best is not None and best[1] > cur, float(cur)
    out.append(best); cur = best[1]
print(len(out), 'windows; bases', sorted({w[2] for w in out}), 'max n', max(w[3] for w in out), file=sys.stderr)
print(',\n'.join('(%d, %d, %d, %s)' % (b, n, k, ds[b]) for _, _, b, n, k in out))
