import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M, orbit
from mahler_burst_tower import primes
for p in primes(int(sys.argv[1])):
    if p<11: continue
    Q=(p-1)//2; cap=Q*Q
    res=[]
    for D in (Q-1,Q,Q+1,Q+2):
        for c0 in range(1,D):
            for ck in orbit(p,D,c0):
                for k in (1,2):
                    for J in range(p**k):
                        M=max_M(p,D,c0,ck,k,J,cap)
                        if M>0: res.append((M,D,c0,ck,k,J))
    res.sort(reverse=True)
    print(p,Q,cap,[(M,f"D={D}",c0,ck,k,f"J={J}={[J//p,J%p] if k==2 else J}") for (M,D,c0,ck,k,J) in res[:6]],flush=True)
