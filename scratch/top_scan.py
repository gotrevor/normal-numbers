import sys
sys.path.insert(0,'experiments')
from mahler_burst_tower import primes
from fractions import Fraction
def safe_upto(p,Q,B,M):
    for m in range(1,M+1):
        b=2*(m%Q); N=m*B; c=0
        while N>0 or c>0:
            t=b+N%p+c; N//=p
            if t%p==p-1: return m-1
            c=t//p
    return M
c=Fraction(1,8)
for p in primes(int(sys.argv[1])):
    if p<11: continue
    Q=(p-1)//2; M=int(c*Q*Q)
    hits=[]
    for t in range(1,13):
        for d1 in range(p):
            B=t*p*p+d1*p+(p-4)
            if safe_upto(p,Q,B,M)>=M: hits.append((t,d1))
    # describe d1 relative to Q and as inverse-ish
    desc=[(t,d1,f"{(d1-Q):+d}", f"inv{(pow(d1,-1,p) if d1%p else 0)}") for t,d1 in hits]
    print(p,Q,len(hits),desc[:14],flush=True)
