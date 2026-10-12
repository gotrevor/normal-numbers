import json, math
from fractions import Fraction as Fr
T = json.load(open('/Users/gotrevor/src/nn-cstar/scripts/cstar_models/sft449.json'))['T']
def enc(b):  # same dyadic enclosure as the C code: round(b^-4.49 * 2^60)/2^60 +- 2^-50
    m = Fr(round(b ** -4.49 * 2 ** 60), 2 ** 60); return m - Fr(1, 2 ** 50), m + Fr(1, 2 ** 50)
def clean(b, a, k=12):
    dlo, dhi = enc(b); n = 0
    while True:
        r = Fr(b ** n, 2 ** k)
        if r > 2 * dhi: return True
        if r > 2 * dlo: return False
        lo, hi = Fr(b ** n * a, 2 ** k), Fr(b ** n * (a + 1), 2 ** k)
        for A in range(math.floor(lo) - 1, math.floor(hi) + 3):
            if hi < A - dhi or lo > A + dhi: continue
            return False
        n += 1
g = 0
for a in range(4096):
    s = 0
    for i in range(11, -1, -1):
        s = T[s][(a >> i) & 1]
        if s < 0: break
    if s >= 0 and clean(3, a) and clean(5, a): g += 1
print('good level-12 cells', g)
