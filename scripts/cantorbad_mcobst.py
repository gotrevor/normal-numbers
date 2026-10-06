"""Monte Carlo over mu_K: for x ~ mu_K (D ternary digits), list obstacles p/q (convergents) with
3^L <= q^2 3^5 < 3^{L+10}, |x-p/q| < 2c0/q^2; report per-L hit rate and in-K share.  usage: samples seed"""
import sys, random
from fractions import Fraction as F
from collections import Counter
c0=F(1,4*3**16); D=140; T=3**D
def inK(x):
    seen=set()
    while x not in seen:
        seen.add(x)
        if x<=F(1,3): x=3*x
        elif x>=F(2,3): x=3*x-2
        else: return False
    return True
n=int(sys.argv[1]); random.seed(int(sys.argv[2]))
hits=Counter(); ink=Counter()
for _ in range(n):
    X=0
    for i in range(D): X=3*X+2*random.getrandbits(1)
    a,b=X,T; p0,q0,p1,q1=0,1,1,0
    while b:
        t=a//b; a,b=b,a-t*b
        p0,q0,p1,q1=p1,q1,t*p1+p0,t*q1+q0
        q=q1
        if q*q*3**5>=3**(D-12): break
        if abs(F(X,T)-F(p1,q))<2*c0/(q*q):
            # all L with 3^L<=q^2 3^5<3^{L+10}
            v=q*q*243; L=0
            while 3**(L+1)<=v: L+=1
            for LL in range(L-9,L+1):
                if LL>=0: hits[LL]+=1; ink[LL]+=inK(F(p1,q))
for L in sorted(hits):
    if L%2==0: print(L, hits[L], round(hits[L]/n,8), round(ink[L]/hits[L],3))
