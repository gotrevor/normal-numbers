import sys, cmath, math
sys.argv=['x','12','0']
exec(open('/Users/gotrevor/src/nn-kbad/scripts/cantorbad_paircorr.py').read().split('def main')[0])
from fractions import Fraction as F
L=int(sys.argv[1]) if False else 12
ob=sorted(enum_obst(L),key=lambda x:F(x[0],x[1]))
vals=[F(p,q) for p,q in ob]
def tri(q):
    while q%3==0: q//=3
    return q==1
istri=[tri(F(p,q).denominator) for p,q in ob]
print(len(ob), sum(istri))
b=int(sys.argv[2]) if len(sys.argv)>2 else 2
for S in (4,8):
  res=[]
  for m in range(5,200):
    xi=2**m
    ph=[cmath.exp(2j*math.pi*float((xi*v)%1)) for v in vals]
    win=F(1,3**S); tot=0j; n=0; tt=0j; j=0
    for i in range(len(vals)):
        while vals[i]-vals[j]>win: j+=1
        for k in range(j,i):
            if vals[k]!=vals[i]:
                z=ph[i]*ph[k].conjugate(); tot+=z; n+=1
                if istri[i] and istri[k]: tt+=z
    res.append((abs(tot)/n, abs(tt)/n, m))
  res.sort(reverse=True)
  print(S, [ (round(a,3),round(c,3),m) for a,c,m in res[:8]], 'median', round(sorted(r[0] for r in res)[len(res)//2],4))
