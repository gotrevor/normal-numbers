import sys, time; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
from fractions import Fraction as F
K=24
t=time.time(); cells=[]
def dfs(k,a):
    if T.sft(k,a)==99: return
    if k==K:
        if T.good(k,a):
            w=T.weight(k,a)
            if w>0: cells.append((a,w))
        return
    dfs(k+1,2*a); dfs(k+1,2*a+1)
dfs(0,0)
tot=sum(w for _,w in cells)
print("good cells",len(cells),"mass",float(tot),"t",time.time()-t,flush=True)
import math
for b,n in ((12,2),(6,3),(6,4),(10,2),(5,4)):
    p=b**n  # spacing 1/p ; cell [a,a+1]/2^K inside [(A+th-r)/p,(A+th+r)/p]
    r=b**-4.49
    # cell inside window iff frac(a*p/2^K - th) and frac((a+1)p/2^K - th) both within [-r, r] around integer
    # positions u = a*p/2^K mod 1, cell span s=p/2^K; contained iff u-th in [-r, r-s] mod 1
    s=p/2**K
    if s>2*r: print(b,n,"no containment"); continue
    ev=[]
    for a,w in cells:
        u=(a*p/2**K)%1.0
        # th in [u-r+s, u+r]  (mod 1)
        lo=(u-r+s)%1.0; ev.append((lo,float(w))); ev.append(((u+r)%1.0+ (1.0 if (u+r)%1.0<lo else 0),-float(w)))
    # sweep with wraparound: duplicate
    ev2=ev+[(x+1.0,dw) for x,dw in ev]
    ev2.sort(key=lambda e:(e[0],-e[1]))
    cur=0; best=0; besth=0
    for x,dw in ev2:
        cur+=dw
        if cur>best: best=cur; besth=x
    act=sum(float(w) for a,w in cells if ((a*p/2**K)%1.0<=r-s+1e-15) or ((a*p/2**K)%1.0>=1-r))
    print(b,n,"actual",act/float(tot),"maxoffset",best/float(tot),"(upper w/ wrap double count)", "ratio",best/max(act,1e-30),flush=True)
