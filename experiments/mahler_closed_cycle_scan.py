import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M, orbit
from math import gcd
for p in [int(a) for a in sys.argv[1:]]:
    Q=(p-1)//2; cap=Q*Q
    found=[]
    for t in range(-4,7):
        D=Q+t
        if D<2 or gcd(p,D)!=1: continue
        for c0 in range(1,D):
            if gcd(c0,D)!=1: continue
            for ck in range(1,D):
                if c0 not in orbit(p,D,ck): continue   # closure
                for J in range(p):
                    M=max_M(p,D,c0,ck,1,J,cap)
                    if M>=cap-8: found.append((M,t,D,c0,ck,J,len(orbit(p,D,ck))))
    found.sort(reverse=True)
    print(p,Q,cap,found[:10],flush=True)
