"""Signed-even-digit tower: B = sum 2 e_i g^i. F_i = (2+2e_i) r + (e_{i-1}-e_i) u + floor(F_{i-1}/g).
Certificate holds for m=Qu+r iff all F_i mod g != g-1 (i up to K where e_K=0, then tail).
Max M = largest M with all 1<=m<=M safe.  Cross-check vs direct long addition."""
import itertools, sys
sys.path.insert(0,'experiments')
from mahler_burst_tower import primes, finish

def maxM_seq(g, es):
    Q=(g-1)//2
    seq=list(es)+[0,0,0]
    for m in range(1,Q*Q):
        u,r=divmod(m,Q); prev_e=0; delta=0
        for e in seq:
            F=(2+2*e)*r+(prev_e-e)*u+delta
            if F%g==g-1: return m-1
            delta=F//g; prev_e=e
    return Q*Q-1

def Bof(g,es): return sum(2*e*g**i for i,e in enumerate(es))

if __name__=="__main__":
    K=int(sys.argv[1]); R=int(sys.argv[2]); gmax=int(sys.argv[3])
    ps=[p for p in primes(gmax) if p>=7]
    rng=range(-R,R+1)
    res={}
    for es in itertools.product(rng,repeat=K):
        if es[-1]<=0: continue
        if Bof(ps[0],es)<=0: continue
        cs=[]
        for p in ps:
            Q=(p-1)//2
            cs.append(maxM_seq(p,es)/(Q*Q))
        res[es]=(min(cs),cs)
    best=sorted(res.items(), key=lambda kv:-kv[1][0])[:12]
    for es,(mn,cs) in best:
        print(es, f"min c={mn:.3f}", " ".join(f"{c:.2f}" for c in cs))
    # sanity cross-check one
    es=best[0][0]; p=ps[3]; Q=(p-1)//2; M=maxM_seq(p,es); B=Bof(p,es)
    print("check", p, es, B, M, finish(p,Q,B,M), finish(p,Q,B,M+1))
