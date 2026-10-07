#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""dim_H C(1,M) = log_3 rho, rho = max Perron root over SCCs reachable from carry 0
in the automaton: state = carry s in [0,M), input x_i in {0,1}, v = s + M*x_i,
need v % 3 in {0,1}, next carry v // 3."""
import sys, math
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

def s3(M):
    d=[]; m=M
    while m: d.append(m%3); m//=3
    return 1+sum(1 for i in range(1,len(d)) if d[i]!=d[i-1])

def cdim(M, iters=400):
    s = np.arange(M, dtype=np.int64)
    rows=[]; cols=[]
    for b in (0,1):
        v = s + M*b
        ok = (v % 3) != 2
        rows.append(s[ok]); cols.append((v[ok]//3))
    r=np.concatenate(rows); c=np.concatenate(cols)
    A = csr_matrix((np.ones_like(r,dtype=np.float64),(r,c)),shape=(M,M))
    # reachable from 0
    reach = np.zeros(M,bool); reach[0]=True; frontier=np.array([0])
    while frontier.size:
        nxt = A[frontier].indices
        nxt = nxt[~reach[nxt]]
        nxt = np.unique(nxt)
        reach[nxt]=True; frontier=nxt
    idx = np.nonzero(reach)[0]
    B = A[idx][:,idx]
    n, lab = connected_components(B, directed=True, connection='strong')
    best=0.0
    for comp in range(n):
        mem = np.nonzero(lab==comp)[0]
        if mem.size==1 and B[mem[0],mem[0]]==0: continue
        C = B[mem][:,mem]
        x = np.ones(mem.size)/mem.size
        lam=0.0
        # power iteration with averaging to handle periodicity
        for _ in range(iters):
            y = C@x + x  # (C+I) has rho+1, aperiodic
            ny = y.sum()
            lam = ny/x.sum()-1
            x = y/ny
        best=max(best,lam)
    return math.log(best,3) if best>1+1e-9 else 0.0, best

if __name__=="__main__":
    for M in map(int,sys.argv[1:]):
        d,rho=cdim(M); print(M, s3(M), f"{rho:.6f}", f"{d:.6f}")
