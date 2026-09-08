import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M, orbit
for p in [13,29,37,53,59,61,67,71,73]:
    Q=(p-1)//2; D=Q+2; cap=Q*Q
    o1=orbit(p,D,1); om=orbit(p,D,D-1)
    safe=[]
    for c0 in range(1,D):
        for ck in range(1,D):
            for k in (1,):
                for J in range(p**k):
                    M=max_M(p,D,c0,ck,k,J,cap)
                    if M>=cap-2: safe.append((c0,ck,k,J,M))
    # classify edges by orbit
    def lab(c): return 'A' if c in o1 else ('B' if c in om else 'other')
    edges=sorted(set((lab(c0),lab(ck)) for c0,ck,k,J,M in safe))
    print(p,D,"orbit sizes",len(o1),len(om),"safe k=1:",len(safe),"edges",edges, safe[:8],flush=True)
