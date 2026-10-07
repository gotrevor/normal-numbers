# Base-b digit statistics of the copy stretch W/(3^l-1) (W a {0,2} ternary block of length l).
# Usage: rep_probe.py b l M trials.  Prints max |freq-1/b| over single digits and the chi2/len for pairs,
# for random W and for the control b=9 (must fail: digits avoid {1,...}).
import random, sys
from fractions import Fraction
def digits(num, den, b, N):
    out=[]; r=num%den
    for _ in range(N):
        r*=b; out.append(r//den); r%=den
    return out
def stats(ds,b):
    N=len(ds); c=[0]*b
    for d in ds: c[d]+=1
    m1=max(abs(x/N-1/b) for x in c)
    p={}
    for i in range(N-1): p[(ds[i],ds[i+1])]=p.get((ds[i],ds[i+1]),0)+1
    m2=max(abs(p.get((i,j),0)/(N-1)-1/b**2) for i in range(b) for j in range(b))
    return m1,m2
b,l,M,T=map(int,sys.argv[1:5])
import math
for t in range(T):
    W=sum(2*random.randint(0,1)*3**i for i in range(l))
    q=3**l-1
    N=int(M*l*math.log(3)/math.log(b))
    print('W random', stats(digits(W,q,b,N),b))
q=3**l-1
N=int(M*l*math.log(3)/math.log(b))
print('W=2', stats(digits(2,q,b,N),b))
print('uniform-random digit control', stats([random.randrange(b) for _ in range(N)],b))
