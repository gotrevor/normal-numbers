import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M, orbit
from mahler_burst_tower import primes
for p in primes(200):
    if p<11: continue
    Q=(p-1)//2; D=Q+2; cap=Q*Q
    orb=orbit(p,D,1)
    M=max_M(p,D,1,D-1,1,1,cap) if (D-1) in orb else None
    # also try all c0 in orbit form with ck = c0*(D-1)?? just scan k=1 all c0,ck,J for D=Q+2
    alt=[]
    if M is None or M<cap-2:
        for c0 in range(1,D):
            for ck in orbit(p,D,c0):
                for J in range(p):
                    MM=max_M(p,D,c0,ck,1,J,cap)
                    if MM>=cap-4: alt.append((MM,c0,ck,J))
    print(p,Q,D,cap,"p mod 4 =",p%4,"Q mod 4 =",Q%4,"M=",M,"alt:",alt[:5],flush=True)
