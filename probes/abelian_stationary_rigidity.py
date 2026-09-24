#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Stationary word measures with abelian balance at every length <= L: solution-space dimension (base 2: 0,0,1,5,16,42 for L=2..7).  See papers/campbell-2026-abelian-normal.md."""
import itertools, sympy as sp, sys
def probe(b,L):
    W=list(itertools.product(range(b),repeat=L)); idx={w:i for i,w in enumerate(W)}
    rows=[]; rhs=[]
    rows.append([1]*len(W)); rhs.append(1)
    # stationarity: marginal on first L-1 == marginal on last L-1
    for u in itertools.product(range(b),repeat=L-1):
        r=[0]*len(W)
        for a in range(b):
            r[idx[u+(a,)]]+=1; r[idx[(a,)+u]]-=1
        rows.append(r); rhs.append(0)
    # abelian constraints for every k<=L on the prefix k-marginal (stationary so any position)
    for k in range(1,L+1):
        for parikh in set(tuple(sorted(w)) for w in itertools.product(range(b),repeat=k)):
            cls=[w for w in itertools.product(range(b),repeat=k) if tuple(sorted(w))==parikh]
            r=[0]*len(W)
            for w in W:
                if w[:k] in cls: r[idx[w]]+=1
            rows.append(r); rhs.append(sp.Rational(len(cls),b**k))
    A=sp.Matrix(rows); bb=sp.Matrix(rhs)
    rank=A.rank(); aug=A.row_join(bb).rank()
    return len(W), rank, aug
for b,Ls in ((2,range(2,8)),(3,range(2,5))):
    for L in Ls:
        n,r,ra=probe(b,L); print(f"base {b} L={L}: vars {n}, rank {r}, consistent {r==ra}, free dims (ignoring positivity) {n-r}")
