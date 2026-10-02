# Validate the simulated transducer output against the true CF of x/phi.
import random
from decimal import Decimal, getcontext
exec(open('experiments/scripts/probe-lap91-transducer.py').read().split('rng=random.Random')[0])
getcontext().prec=2000
PHI=(1+Decimal(5).sqrt())/2
def cf_of(v,n):
    out=[]
    for _ in range(n):
        iv=int(v)
        out.append(iv)
        v=v-iv
        if v==0: break
        v=1/v
    return out
rng=random.Random(12345)
N=400
digits=[gauss_digit(rng) for _ in range(N)]
# x = [0; a0,a1,...]
x=Decimal(0)
for a in reversed(digits):
    x=1/(Decimal(a)+x)
y=x/PHI
true_cf=cf_of(1/y if y<1 else y,120)  # digits of y in (0,1): 1/y first
# emitted
s=St((1,0),(0,0),(0,0),(0,1)); out=[]
for a in digits:
    t=comp(s,readMap(a))
    k=emit_digit(t)
    if k is None: s=t
    else:
        s=St(sub(t.c,smul(k,t.a)), sub(t.d,smul(k,t.b)), t.a, t.b); out.append(k)
print("input digits  :",digits[:20])
print("emitted (40)  :",out[:40])
print("true CF of y  :",true_cf[:40])
print("agree first   :",next((i for i,(p,q) in enumerate(zip(out,true_cf)) if p!=q), min(len(out),len(true_cf))))
print("len emitted",len(out),"of",N)
