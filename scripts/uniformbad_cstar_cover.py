from fractions import Fraction as F
import math,sys
def delta(b,num,den,prec=10**6):
    # rational d <= b^(-num/den), check d^den * b^num <= 1
    d=F(math.floor(b**(-num/den)*prec*(1-1e-9)),prec)
    assert d**den*b**num<=1
    return d
def cover(num,den,B,N):
    ds={b:delta(b,num,den) for b in range(2,B+1)}
    cur=F(0); out=[]
    while cur<1:
        best=None
        for b in range(2,B+1):
            d=ds[b]
            for n in range(N+1):
                s=b**n; k=math.floor(cur*s+d)
                if F(k)-d<=cur*s:
                    hi=(k+d)/s
                    if best is None or hi>best[0]: best=(hi,b,n,k)
        if best is None or best[0]<=cur: return None,cur
        out.append(best[1:]); cur=best[0]
    return out,ds
num,den,B,N=map(int,sys.argv[1:])
o,ds=cover(num,den,B,N)
if o is None: print("fail at",float(ds))
else: print(len(o)); print(o[:10])

def run(num,den,B,N,prec):
    global delta
    ds={b:F(math.floor(b**(-num/den)*prec*(1-1e-9)),prec) for b in range(2,B+1)}
    for b,d in ds.items(): assert d**den*b**num<=1
    cur=F(0); out=[]
    while cur<1:
        best=None
        for b in range(2,B+1):
            d=ds[b]
            for n in range(N+1):
                s=b**n; k=math.floor(cur*s+d)
                if F(k)-d<=cur*s:
                    hi=(k+d)/s
                    if best is None or hi>best[0]: best=(hi,b,n,k)
        if best[0]<=cur: return None
        out.append((best[1],best[2],best[3],ds[best[1]])); cur=best[0]
    return out
