# worst-case fraction (Parry-weighted ~ counted) of run-free binary children D of U killed by base-3 obstacles
# with radius in [eta|D|, eta|U|)  (eta: obstacle must be avoided once radius >= eta * cell)
import math,sys
from fractions import Fraction as Fr
c=4; R=3
def runfree_words(L,last,run):
    out=[]
    def rec(w,l,r):
        if len(w)==L: out.append(w);return
        for d in (0,1):
            if d==l:
                if r+1<=R: rec(w+[d],d,r+1)
            else: rec(w+[d],d,1)
    rec([],last,run); return out
def obst3(lo,hi,rmin,rmax):
    res=[]; n=0
    while True:
        r=3.0**(-n-c)
        if r<rmin: break
        if r<rmax:
            s=3**n
            for k in range(math.floor((lo-r)*s), math.ceil((hi+r)*s)+1):
                res.append((k/s-r,k/s+r))
        n+=1
    return res
L=int(sys.argv[1]); eta=float(sys.argv[2]); J=int(sys.argv[3])
worst=1;cnt=0
for w in runfree_words(J,-1,0):
    # state
    last=w[-1]; run=1
    while run<len(w) and w[-1-run]==last: run+=1
    a=sum(d*2.0**-(i+1) for i,d in enumerate(w)); size=2.0**-J
    ch=runfree_words(L,last,run)
    obs=obst3(a,a+size,eta*size/2**L,eta*size)
    dsz=size/2**L
    good=0
    for v in ch:
        x=a+sum(d*2.0**-(J+i+1) for i,d in enumerate(v))
        if not any(o[0]<x+dsz and o[1]>x for o in obs): good+=1
    f=good/len(ch); worst=min(worst,f); cnt+=1
print(L,eta,J,cnt,'worst good fraction',round(worst,3))
