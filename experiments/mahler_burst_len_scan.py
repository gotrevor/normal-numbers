"""Max M reachable with a burst of exactly <= K base-p digits (default 3), background a=2, W=p-1.
Exact digit-DFS: digit i of m*B depends on B mod p^(i+1); we stop at length K and
fully check (finish). Descend M from Q^2-1 until some B works."""
import sys
sys.path.insert(0, 'experiments')
from mahler_burst_tower import primes, finish, search

def maxM(p, K):
    Q=(p-1)//2
    lo, hi = 1, Q*Q-1     # find max M with a solution (monotone in M)
    best=None
    while lo <= hi:
        mid=(lo+hi)//2
        k, sols = search(p, mid, Kmax=K, cap=20000)
        if sols: best=(mid, sols[0]); lo=mid+1
        else: hi=mid-1
    return best

K=int(sys.argv[1]) if len(sys.argv)>1 else 3
for p in primes(int(sys.argv[2]) if len(sys.argv)>2 else 60):
    if p<7: continue
    Q=(p-1)//2
    b=maxM(p,K)
    if b:
        M,B=b; d=[]; x=B
        while x: d.append(x%p); x//=p
        print(f"p={p:3d} Q={Q:3d} K<={K} M={M:5d} M/Q^2={M/Q/Q:.3f} B={B} digits={d}", flush=True)
    else:
        print(f"p={p:3d} none", flush=True)
