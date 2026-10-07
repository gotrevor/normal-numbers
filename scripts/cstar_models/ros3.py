import math
def ispp(b):
    for m in range(2,b):
        a=m
        while a<b: a*=m
        if a==b: return True
    return False
def slack(c,lam,R,excl=True,B=3000,C=5):
    s=2-lam**(1-R)-lam
    tot=0
    for b in range(3,B):
        if excl and ispp(b): continue
        D=math.floor(math.log2(b**c-2))
        tot+=C*lam**(-(D-1))
    return s,tot
for c,R in [(4,4),(5,5),(5.5,5),(6,6),(6,5),(7,7),(7,6)]:
  for excl in [True,False]:
    best=None
    for i in range(1,95):
        lam=1+i/100
        s,t=slack(c,lam,R,excl)
        if best is None or s-t>best[0]: best=(round(s-t,4),lam,round(s,4),round(t,4))
    print(c,R,excl,best)
