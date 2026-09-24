#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Block laws mu on {0,1}^k with every contiguous interval one-count Binomial: free directions per k (k=4: 1).  See DESIGN-2026-09-23-binary-abelian-nonnormal.md."""
import itertools, sympy as sp
def system(k):
    W=list(itertools.product((0,1),repeat=k)); rows=[]
    for a in range(k):
        for b in range(a+1,k+1):
            for j in range(b-a+1):
                rows.append([1 if sum(w[a:b])==j else 0 for w in W])
    return W, sp.Matrix(rows)
for k in range(2,9):
    W,A=system(k); ns=A.nullspace()
    print(f"k={k}: words {len(W)}, free directions {len(ns)}")
    if ns and k<=6:
        v=ns[0]; v=v/max(abs(x) for x in v)
        print('  ', {''.join(map(str,w)):v[i] for i,w in enumerate(W) if v[i]!=0})
