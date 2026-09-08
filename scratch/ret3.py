import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M
from mahler_burst_tower import primes
for p in primes(80):
    if p<11: continue
    Q=(p-1)//2; cap=Q*Q
    best=(0,None)
    for J in range(p*p):
        M=max_M(p,Q,1,Q-1,2,J,cap)
        if M>best[0]: best=(M,[J//p,J%p])
    print(p,Q,cap,"best 1->Q-1 (k=2):",best,f"{best[0]/cap:.2f}",flush=True)
