"""mu_K-mass share of dead balls B(p/q, 2c0/q^2) around preperiodic obstacles (3-free denom | 3^l±1, l<=8). usage: L"""
import sys
from fractions import Fraction as F
exec(open('scripts/cantorbad_paircorr.py').read().split('def main')[0])
def mass(lo,hi,u=F(0),w=F(1),d=0):
    if hi<=u or lo>=u+w: return F(0)
    if lo<=u and hi>=u+w: return F(1,2**d)
    if d>60: return F(0)
    w3=w/3
    return mass(lo,hi,u,w3,d+1)+mass(lo,hi,u+2*w3,w3,d+1)
def inK(x):
    seen=set()
    while x not in seen:
        seen.add(x)
        if x<=F(1,3): x=3*x
        elif x>=F(2,3): x=3*x-2
        else: return False
    return True
L=int(sys.argv[1]); MODE=sys.argv[2] if len(sys.argv)>2 else "fam"; tot=F(0); fam=F(0)
for p,q in enum_obst(L):
    r=2*c0/(q*q); v=F(p,q); m=mass(v-r,v+r); tot+=m
    d=v.denominator
    while d%3==0: d//=3
    if (inK(v) if MODE=="inK" else any((3**l-1)%d==0 or (3**l+1)%d==0 for l in range(1,9))): fam+=m
print(L, float(tot), float(fam/tot) if tot else 0)
