import random, math
SQ5=math.sqrt(5); PHI=(1+SQ5)/2
def mul(x,y):
    u1,v1=x; u2,v2=y
    return (u1*u2+v1*v2, u1*v2+v1*u2+v1*v2)
def add(x,y): return (x[0]+y[0], x[1]+y[1])
def sub(x,y): return (x[0]-y[0], x[1]-y[1])
def smul(k,x): return (k*x[0], k*x[1])
def sign(x):
    A=2*x[0]+x[1]; B=x[1]
    if A>=0 and B>=0: return 0 if (A==0 and B==0) else 1
    if A<=0 and B<=0: return 0 if (A==0 and B==0) else -1
    d=A*A-5*B*B
    if d==0: return 0
    return 1 if (A>0)==(d>0) else -1
def cmp(x,y): return sign(sub(x,y))
from decimal import Decimal, getcontext
getcontext().prec=120
D5=Decimal(5).sqrt()
_D5={}
def dval(x):
    A=2*x[0]+x[1]; B=x[1]
    n=max(abs(A),abs(B),1).bit_length()
    p=int(n*0.302)+60
    getcontext().prec=p
    d5=_D5.get(p)
    if d5 is None:
        d5=Decimal(5).sqrt(); _D5[p]=d5
    return (Decimal(A)+Decimal(B)*d5)/2
def logd(x):
    v=dval(x)
    if v<=0: return None
    return float(v.ln())
def fl(x):
    # (mantissa float, shift) with value = mant * 2^shift ; x assumed nonneg-ish
    A=2*x[0]+x[1]; B=x[1]
    t=max(abs(A),abs(B),1)
    sh=max(0,t.bit_length()-52)
    return ((A>>sh)+(B>>sh)*SQ5)/2.0, sh
def ratio(n,d):
    mn,sn=fl(n); md,sd=fl(d)
    if md==0: return float('nan')
    return (mn/md)*2.0**(sn-sd)
class St:
    __slots__=('a','b','c','d')
    def __init__(s,a,b,c,d): s.a,s.b,s.c,s.d=a,b,c,d
def comp(s,t):
    return St(add(mul(s.a,t.a),mul(s.b,t.c)), add(mul(s.a,t.b),mul(s.b,t.d)),
              add(mul(s.c,t.a),mul(s.d,t.c)), add(mul(s.c,t.b),mul(s.d,t.d)))
def readMap(k): return St((0,0),(1,0),(1,0),(k,0))
def floor_inv(n,d):
    # largest k>=0 with k*n <= d  (n>0, d>0)  == floor(d/n)
    if sign(n)<=0: return None
    lo,hi=0,1
    while cmp(smul(hi,n),d)<=0:
        lo=hi; hi*=2
        if hi>10**9: return lo
    while hi-lo>1:
        mid=(lo+hi)//2
        if cmp(smul(mid,n),d)<=0: lo=mid
        else: hi=mid
    return lo
def emit_digit(t):
    n0,d0=t.b,t.d
    n1,d1=add(t.a,t.b),add(t.c,t.d)
    if sign(n0)<=0 or sign(n1)<=0: return None
    k0=floor_inv(n0,d0); k1=floor_inv(n1,d1)
    if k0 is None or k1 is None: return None
    for k in sorted(set([k0,k1])):
        if k<1: continue
        ok=True
        for (n,d) in ((n0,d0),(n1,d1)):
            if cmp(d, smul(k+1,n))>0: ok=False;break
            if cmp(smul(k,n), d)>0: ok=False;break
        if ok: return k
    return None
def logwidth(t):
    det=sub(mul(t.a,t.d),mul(t.b,t.c))
    ld=logd(det) if sign(det)>0 else logd(smul(-1,det))
    return ld - logd(t.d) - logd(add(t.c,t.d))
def bits(t):
    return max(abs(2*z[0]+z[1]).bit_length() for z in (t.a,t.b,t.c,t.d))
def gauss_digit(rng):
    t=rng.random(); u=2**t-1
    return max(1,int(1/u))
def run(Phi,digits,report=None,label=""):
    s=Phi; stalls=0; emits=0; runs=[]; cur=0; lws=[]
    for i,a in enumerate(digits):
        t=comp(s,readMap(a))
        k=emit_digit(t)
        if k is None:
            s=t; stalls+=1; cur+=1
        else:
            s=St(sub(t.c,smul(k,t.a)), sub(t.d,smul(k,t.b)), t.a, t.b); emits+=1
            if cur: runs.append(cur)
            cur=0
        if report and (i+1)%report==0:
            print(f"  {label} n={i+1:6d} emits={emits:6d} stalls={stalls:5d} dens={stalls/(i+1):.4f} logwidth={logwidth(s):9.3f} bits={bits(s):6d} maxrun={max(runs+[cur],default=0)}")
    return emits,stalls,[0.0],runs
rng=random.Random(12345)
N=20000
digits=[gauss_digit(rng) for _ in range(N)]
for label,Phi in [("z/phi", St((1,0),(0,0),(0,0),(0,1))),
                  ("(z+1)/3", St((1,0),(1,0),(0,0),(3,0))),
                  ("phi*z/(z+phi)", St((0,1),(0,0),(1,0),(0,1)))]:
    print("== Phi:",label,"==")
    e,st,lws,runs=run(Phi,digits,report=500,label=label)
    print("   density",st/N,"median logwidth",sorted(lws)[len(lws)//2],
          "run hist",{l:runs.count(l) for l in sorted(set(runs))})

