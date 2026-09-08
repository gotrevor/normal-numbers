#!/usr/bin/env python3
"""Direct simulation at record bases found by the EXHAUSTIVE scan (not hand-picked).
Builds B = c from delta* mechanically, then scans m with no closed form used."""
import time
from fractions import Fraction as F
def fac(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def first_hit(B,g,w,cap):
    for m in range(1,cap+1):
        N=m*B
        while N:
            if N%g==w: return m
            N//=g
    return None
def build(g, num, den):
    """c = g^(j-1) * (num/den), j minimal making all exponents >= 0."""
    gf=fac(g); nf=fac(num); df=fac(den)
    ps=set(gf)|set(nf)|set(df)
    j1=max([ (df.get(p,0)-nf.get(p,0)+gf.get(p,0)-1)//gf[p] +1 if gf.get(p) else 0
             for p in ps], default=1)
    j1=max(j1,1)
    c=1
    for p in ps:
        c*= p**(gf.get(p,0)*j1 + nf.get(p,0) - df.get(p,0))
    return c, j1+1
for g,num,den in [(66,33,32),(130,65,64),(2310,385,384)]:
    c,j = build(g,num,den)
    assert (g**j) % c == 0 and c > g**(j-1), "c must divide g^j and exceed g^(j-1)"
    t0=time.time(); m=first_hit(c,g,g-1,int(1.02*g*g))
    pred=int((g-1)*g/F(num,den))
    print(f"g={g:<6} delta*={num}/{den}  j={j}  first m = {m:>9}  ratio {m/(g*g):.6f}  "
          f"predicted {pred:>9}  {'MATCH' if m==pred else 'MISMATCH'}  [{time.time()-t0:.0f}s]")
