"""Pair share of period-l obstacle families (PeriodicFamilyShare). usage: L S"""
import sys
from fractions import Fraction as F
L,S=int(sys.argv[1]),int(sys.argv[2])
exec(open('scripts/cantorbad_paircorr.py').read().split('def main')[0])
vals=sorted(set(F(p,q) for p,q in enum_obst(L)))
def fam(v):
    d=v.denominator
    while d%3==0: d//=3
    return [l for l in range(1,9) if (3**l-1)%d==0 or (3**l+1)%d==0]
fs=[set(fam(v)) for v in vals]
from collections import Counter
c=Counter(); n=0; j=0; win=F(1,3**S)
for i in range(len(vals)):
    while vals[i]-vals[j]>win: j+=1
    for k in range(j,i):
        n+=1
        for l in fs[i]|fs[k]: c[l]+=1
print(L,S,n,{l:round(c[l]/n,4) for l in sorted(c)})
