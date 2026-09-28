"""C4 probe: which sets of window lengths does a PERIODIC binary sequence realize exactly?

A sequence of period D has, at window length L, the uniform law over its D cyclic L-windows.
It is abelian at L iff that weight law is exactly Binomial(L,1/2), which forces
D * C(L,j) / 2^L to be an integer for every j; and for L >= D it is impossible (only D
windows, but L+1 weights must have positive mass).  So G(v) = {L>=1 : abelian at L} is a
subset of [1, D-1], automatically finite.

Known-answer check: the de Bruijn word of order 3 (D=8) must have G = {1,2,3}.
"""
from itertools import product
from math import comb

def good_lengths(v):
    D = len(v)
    G = []
    for L in range(1, D):
        num = [comb(L, j) * D for j in range(L + 1)]
        if any(n % (2 ** L) for n in num):
            continue
        tgt = [n // 2 ** L for n in num]
        cnt = [0] * (L + 1)
        for r in range(D):
            cnt[sum(v[(r + i) % D] for i in range(L))] += 1
        if cnt == tgt:
            G.append(L)
    return tuple(G)

# known-answer check: de Bruijn B(2,3)
db3 = [0,0,0,1,0,1,1,1]
assert good_lengths(db3) == (1,2,3), good_lengths(db3)
db2 = [0,0,1,1]
assert good_lengths(db2) == (1,2), good_lengths(db2)

for D in (4, 8, 16):
    seen = {}
    for v in product((0,1), repeat=D):
        G = good_lengths(list(v))
        seen.setdefault(G, v)
    print("D =", D, "realizable exact sets:")
    for G in sorted(seen, key=lambda g: (len(g), g)):
        print("   ", G, "  e.g.", "".join(map(str, seen[G])))
