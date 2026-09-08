import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M
from mahler_burst_tower import primes
for p in primes(120):
    if p<11: continue
    Q=(p-1)//2; cap=Q*Q
    row=[]
    for c in range(1,Q):
        ck=(c+2)%Q
        J=2*c+((c+2)//Q)
        row.append((c,max_M(p,Q,c,ck,1,J,cap)))
    mn=min(M for c,M in row)
    print(p,Q,cap,"min",mn,f"{mn/cap:.2f}",[(c,M) for c,M in row if M<cap-8][:10],flush=True)
