from fractions import Fraction as F
import math, sys
pat=[5,7,8,10,12,13]
def nlog2(x):  # Nat.log 2 x
    return x.bit_length()-1 if x>0 else 0
def anc3(n): return nlog2(140*3**n//138)+1
def cells3(n,m): return 2**(anc3(n)+m+1)//(140*3**n)+2
def depth3(n):
    best=None
    for m in range(1,21):
        v=F(cells3(n,m)*4**m,7**m)
        if best is None or v<best[0]: best=(v,m)
    return best[1]
def kl(n): return anc3(n)+depth3(n)
K0=int(sys.argv[1]); K=int(sys.argv[2]); ROUND=2**40
N=0
while anc3(N)<K: N+=1
kills={}
for n in range(N):
    kills.setdefault(kl(n),[]).append((anc3(n),cells3(n,depth3(n))))
# check: each level has at most one base-3 kill?
print('levels with >1 kill:', [k for k,v in kills.items() if len(v)>1][:10])
Q=[F(2)]*K
for k in range(K0,K):
    s=F(2)
    def P(i,k):
        p=F(1)
        for j in range(i,k): p*=Q[j]
        return p
    for l in pat:
        if k+1-l>=0: s-=1/P(k+1-l,k)
    for (a,T) in kills.get(k+1,[]):
        s-=F(T)/P(a,k)
    q=F(math.ceil(s*ROUND),ROUND)
    Q[k]=q
    if q<1:
        print('dies: Q[%d]=%.4f'%(k,float(q))); break
else:
    print('survives to',K,'min',float(min(Q[K0:])))
print([ (n,anc3(n),depth3(n),cells3(n,depth3(n))) for n in range(12)])
