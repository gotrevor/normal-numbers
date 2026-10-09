import math,sys
from fractions import Fraction as Fr
def ispp(b):
    for m in range(2,b):
        a=m*m
        while a<b: a*=m
        if a==b: return True
    return False
CUT=int(sys.argv[1]); NUM=int(sys.argv[2]); DEN=int(sys.argv[3]); TAIL=sys.argv[4]
PL=[int(x) for x in sys.argv[5].split(',')]
def Kb(b):
    if b<CUT:
        K=int(b**(NUM/DEN))
        while K**DEN>b**NUM: K-=1
        while (K+1)**DEN<=b**NUM: K+=1
        return K
    return b**4 if TAIL=='4' else b**4*math.isqrt(b)
LAG={}
for b in range(3,3000):
    if b>3 and ispp(b): continue
    K=Kb(b); LAG[b]=((3*(K-2))//4).bit_length()-1
def slack(gA,gB):
    F=lambda l:(gA*gB*gB)**(l//3)*gB**(l%3)
    Ts=sum(4/F(LAG[b]-1) for b in LAG if 3<b<CUT)
    Tt=sum(4/F(LAG[b]-1) for b in LAG if b>=CUT)
    off=sum(1/F(p-1) for p in PL)
    return (2-gA-off-Ts-Tt, 2-gB-off-4/F(LAG[3]-1)-Ts-Tt, Ts, Tt)
best=None
for i in range(int(sys.argv[6]),int(sys.argv[7]),5):
  for j in range(1600,1750,5):
    s=slack(i/1000,j/1000); m=min(s[0],s[1])
    if best is None or m>best[0]: best=(m,i/1000,j/1000,s)
print(best, "K3",Kb(3),"lag3",LAG[3])
