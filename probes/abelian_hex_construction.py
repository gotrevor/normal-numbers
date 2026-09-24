#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Exact check of the hex-swap construction (2->3, 5->4, B->A, C->D): abelian at every offset for L<=9, word frequencies (0011 -> 5/64).  See DESIGN-2026-09-23-binary-abelian-nonnormal.md."""
import itertools
from fractions import Fraction as F
from math import comb
k=4
phi={2:3,5:4,11:10,12:13}
mu={}
for d in range(16):
    e=phi.get(d,d); w=tuple((e>>(3-i))&1 for i in range(4))
    mu[w]=mu.get(w,0)+F(1,16)
# exact law of bits r..r+L-1 in concatenation of iid mu-blocks
def seg_law(r,L):
    nb=(r+L+k-1)//k
    law={}
    for blocks in itertools.product(mu.items(),repeat=nb):
        p=F(1)
        bits=[]
        for w,q in blocks: p*=q; bits+=w
        seg=tuple(bits[r:r+L]); law[seg]=law.get(seg,0)+p
    return law
bad=[]
for L in range(1,10):
    for r in range(k):
        law=seg_law(r,L); cnt={}
        for s,p in law.items(): cnt[sum(s)]=cnt.get(sum(s),0)+p
        for j in range(L+1):
            if cnt.get(j,0)!=F(comb(L,j),2**L): bad.append((L,r,j))
print("abelian violations (L<=9, every offset):", bad)
# limiting word frequencies = average over the k offsets
for L in (2,3,4,5):
    avg={}
    for r in range(k):
        for s,p in seg_law(r,L).items(): avg[s]=avg.get(s,0)+p/k
    dev={''.join(map(str,s)):v for s,v in avg.items() if v!=F(1,2**L)}
    missing=[''.join(map(str,s)) for s in itertools.product((0,1),repeat=L) if s not in avg]
    print(f"L={L}: {len(dev)} words off 2^-{L}; missing {missing}; e.g.", dict(list(dev.items())[:4]))
