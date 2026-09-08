import itertools, sys
sys.path.insert(0,'experiments'); sys.path.insert(0,'scratch')
from mahler_burst_tower import primes
from signed_digits import maxM_seq
K=int(sys.argv[1]); c=float(sys.argv[2]); gmax=int(sys.argv[3])
ps=[p for p in primes(gmax) if p>=11]
def cand(Q):
    S=set(range(-4,5))
    for s in range(-3,4):
        S|={Q+s,-Q+s,2*Q+s,-2*Q+s}
    return sorted(S)
def label(e,Q):
    for a in (-2,-1,0,1,2):
        s=e-a*Q
        if abs(s)<=4 and (a==0 or abs(s)<=3): return f"{a}Q{s:+d}" if a else f"{s:+d}"
    return str(e)
good={}
for p in ps:
    Q=(p-1)//2; M=int(c*Q*Q)
    S=cand(Q); ok=set()
    for es in itertools.product(S,repeat=K):
        if sum(2*e*p**i for i,e in enumerate(es))<=0: continue
        # quick check: use maxM_seq but early exit
        if maxM_seq(p,es)>=M:
            ok.add(tuple(label(e,Q) for e in es))
    good[p]=ok
    print(p, len(ok), sorted(ok)[:8], flush=True)
common=set.intersection(*good.values())
print("COMMON:", sorted(common))
