import math
def ispp(b):
    for m in range(2,b):
        a=m
        while a<b: a*=m
        if a==b: return True
    return False
def costf(b,c,lam,j,f):
    L=math.log2(b**c-2)
    C=math.ceil(2**(1+f+j)-1e-12)+1
    e=j-1+math.floor(f+L)
    return C*lam**(-e)
def cost(b,c,lam,mode):
    fs=[(i+.5)/400 for i in range(400)]
    vals=[min(costf(b,c,lam,j,f) for j in (-2,-1,0,1,2)) for f in fs]
    return max(vals) if mode=='max' else sum(vals)/len(vals)
def slack(c,lam,mode,B=400):
    R=math.floor(c)
    s=2-lam**(1-R)-lam
    tot=0
    for b in range(3,B):
        if ispp(b): continue
        cb=cost(b,c,lam,mode)
        if mode=='avg': cb/=math.log2(b)
        tot+=cb
    return s,tot
for mode in ['max','avg']:
  for c in [3.5,4,4.5,5,6]:
    best=None
    for i in range(1,84):
        lam=1+i/100
        s,t=slack(c,lam,mode)
        if best is None or s-t>best[0]: best=(round(s-t,4),lam,round(s,4),round(t,4))
    print(mode,c,best)
