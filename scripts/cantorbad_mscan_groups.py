import sys, cmath, math
exec(open('/Users/gotrevor/src/nn-kbad/scripts/cantorbad_paircorr.py').read().split('def main')[0])
from fractions import Fraction as F
from collections import Counter
ob=sorted(enum_obst(12),key=lambda x:F(x[0],x[1]))
vals=[F(p,q) for p,q in ob]
def qf(v):
    q=v.denominator
    while q%3==0: q//=3
    return q
for m in (184,185,111,60):
  xi=2**m
  ph=[cmath.exp(2j*math.pi*float((xi*v)%1)) for v in vals]
  win=F(1,3**4); j=0; byq=Counter(); n=0; tot=0
  for i in range(len(vals)):
    while vals[i]-vals[j]>win: j+=1
    for k in range(j,i):
      if vals[k]!=vals[i]:
        z=ph[i]*ph[k].conjugate(); n+=1; tot+=z
        byq[min(qf(vals[i]),qf(vals[k]))]+=z.real
  print(m, abs(tot)/n, [(q,round(c/n,3)) for q,c in sorted(byq.items(),key=lambda x:-abs(x[1]))[:6]])
