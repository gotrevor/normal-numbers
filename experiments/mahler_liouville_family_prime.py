import sys
from itertools import product

def digits(n, g):
    if n == 0: return [0]
    d = []
    while n: d.append(n % g); n //= g
    return d[::-1]

def fmax(B, g, k):
    # for each block W of length k, first m with W in 0^k digits(mB) 0^k; return max over W and argmax
    seen = {}
    total = g**k
    m = 0
    while len(seen) < total:
        m += 1
        s = [0]*k + digits(m*B, g) + [0]*k
        for i in range(len(s)-k+1):
            W = tuple(s[i:i+k])
            if W not in seen: seen[W] = m
    best = max(seen.items(), key=lambda kv: kv[1])
    return best[1], best[0]

for g in [2,3,5,7]:
    for k in [1,2,3]:
        if g**k > 400: continue
        Bmax = {1:200000, 2:200000, 3:60000}[k]
        if g == 7 and k == 3: Bmax = 20000
        best = (0, None, None)
        for B in range(1, Bmax):
            if B % g == 0: continue
            v, W = fmax(B, g, k)
            if v > best[0]: best = (v, B, W)
        print(f"g={g} k={k}: L_fam >= {best[0]} at B={best[1]} ({digits(best[1],g)}) W={best[2]}   g^k-1={g**k-1}  g^(k+1)={g**(k+1)}", flush=True)
