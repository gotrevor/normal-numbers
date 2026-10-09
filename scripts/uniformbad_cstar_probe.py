# Host probe (Ren, 2026-10-06) for UniformBadThreshold: bisect the exponent c at which the finite system
# ||b^n xi|| > b^-c (b<=B, n<=N) has no survivors in [0,1].  Floating point; a Lean certificate must be exact.
# Exact interval propagation: survivors of ||b^n xi|| > b^-c, b<=B, n<=N, as a union of intervals.
from fractions import Fraction as F
import math
def forbidden(b,n,d):
    s=b**n; return [((k-d)/s,(k+d)/s) for k in range(0,s+1)]
def survivors(c,B,N):
    iv=[(0.0,1.0)]
    for n in range(N+1):
        for b in range(2,B+1):
            d=b**(-c); s=b**n; out=[]
            for lo,hi in iv:
                k0=math.floor(lo*s-d); k1=math.ceil(hi*s+d)
                cur=lo
                for k in range(k0,k1+1):
                    a,bb=(k-d)/s,(k+d)/s
                    if bb<=cur or a>=hi: continue
                    if a>cur: out.append((cur,min(a,hi)))
                    cur=max(cur,bb)
                    if cur>=hi: break
                if cur<hi: out.append((cur,hi))
            iv=[x for x in out if x[1]>x[0]]
            if not iv: return 0,[]
    return sum(h-l for l,h in iv), iv[:2]
for B,N in ((3,14),(5,10),(8,8),(16,6)):
    lo,hi=1.585,3.0
    for _ in range(25):
        mid=(lo+hi)/2
        if survivors(mid,B,N)[0]>0: hi=mid
        else: lo=mid
    print(B,N,'threshold ~',round(hi,4), survivors(hi+1e-4,B,N)[1])
