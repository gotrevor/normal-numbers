from fractions import Fraction as F
import math, sys, json
num, den, B, prec = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
MINRAD = float(sys.argv[5])
def ispp(b):
    for a in range(2, b):
        q = a
        while q < b: q *= a
        if q == b: return True
    return False
ds = {}
for b in range(2, B + 1):
    if b > 2 and ispp(b): continue
    x = b ** (-num / den)
    if prec > 0:
        d = F(math.floor(x * prec * (1 - 1e-9)), prec)
    else:
        kk = math.ceil(-math.log2(x)) - prec
        d = F(math.floor(x * 2 ** kk * (1 - 1e-12)), 2 ** kk)
    if d == 0: continue
    assert d ** den * b ** num <= 1
    ds[b] = d
pairs = []
for b, d in ds.items():
    n = 0
    while float(d) * b ** -n >= MINRAD:
        pairs.append((b, n)); n += 1
cur = F(0); out = []
while cur < 1:
    best = None
    for (b, n) in pairs:
        d = ds[b]; s = b ** n; k = math.floor(cur * s + d)
        if F(k) - d <= cur * s:
            hi = (k + d) / s
            if best is None or hi > best[0]: best = (hi, b, n, k)
    if best is None or best[0] <= cur:
        print('FAIL at', float(cur)); sys.exit(1)
    out.append((best[1], best[2], best[3], ds[best[1]])); cur = best[0]
print(len(out), 'windows; bases used', sorted(set(w[0] for w in out)), 'max n', max(w[1] for w in out))
json.dump([(b, n, k, [d.numerator, d.denominator]) for (b, n, k, d) in out], open('cert_%d_%d.json' % (num, den), 'w'))
