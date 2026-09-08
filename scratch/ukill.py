import sys
sys.path.insert(0,'experiments')
from mahler_burst_tower import primes
def maxM(p,Q,B,cap):
    for m in range(1,cap+1):
        b=2*(m%Q); N=m*B; c=0
        while N>0 or c>0:
            t=b+N%p+c; N//=p
            if t%p==p-1: return m-1
            c=t//p
    return cap
def S(p,j): return (p**j-1)//(p-1)
for p in primes(int(sys.argv[1])):
    if p<7: continue
    Q=(p-1)//2; cap=Q*Q
    best=(0,None)
    rows=[]
    for K in range(1,7):
        lam0=(-2*pow(p,-K,Q))%Q
        for L in range(0,6):
            for tL in range(0,3):
                t=2*lam0*S(p,L)+p**L*tL
                num=2+p**K*(Q*t+lam0)
                assert num%Q==0
                B=num//Q
                M=maxM(p,Q,B,cap)
                rows.append((M,K,L,tL,lam0))
    rows.sort(reverse=True)
    print(p,Q,cap,[(M,f"{M/cap:.2f}",K,L,tL,lam0) for (M,K,L,tL,lam0) in rows[:5]],flush=True)
