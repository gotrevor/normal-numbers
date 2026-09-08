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
for p in primes(80):
    if p<7: continue
    Q=(p-1)//2; cap=Q*Q
    out=[]
    for t in (1,2,3,4):
        for k in (1,2,3):
            j=k*Q
            num=t*S(p,j)
            if num%Q: continue
            B=num//Q
            out.append((t,k,maxM(p,Q,B,cap)))
    print(p,Q,cap,out,flush=True)
