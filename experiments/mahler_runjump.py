"""Validate the run+jump cycle:  D = p-b, p-b-1, ..., b+1, b, then jump b -> p-b.
Check every vertex orbit condition and the bottleneck cost = b(p-b-1)."""
from math import gcd

def sieve(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]

def emin(p,D,A,C):
    if gcd(A,D)!=1 or gcd(C,D)!=1: return None
    tgt=(-A)%D; x=C%D; seen=set(); e=0
    while x not in seen:
        if x==tgt: return e
        seen.add(x); x=(x*p)%D; e+=1
    return None

def minus_one(p,b):
    if gcd(p,b)!=1: return None
    tgt=(b-1)%b; x=p%b; e=1; seen=set()
    while x not in seen:
        if x==tgt: return e
        seen.add(x); x=(x*p)%b; e+=1
    return None

def check(p,b,verbose=False):
    assert 3<=b<p/2
    cyc=list(range(p-b, b-1, -1))    # p-b, ..., b
    n=len(cyc)
    bad=[]; costs=[]
    for i in range(n):
        A=cyc[(i-1)%n]; B=cyc[i]; C=cyc[(i+1)%n]
        if gcd(B,C)!=1: bad.append(("gcd",B,C)); continue
        e=emin(p,B,A,C)
        if e is None: bad.append(("orbit",A,B,C))
        costs.append(C*(p-B))
    return (min(costs) if costs else 0), bad, cyc

primes=[p for p in sieve(400) if p>=11]
fails=0; checked=0
for p in primes:
    for b in range(3,(p-1)//2+1):
        if minus_one(p,b) is None: continue
        m,bad,cyc = check(p,b)
        checked+=1
        pred = b*(p-b-1)
        if bad or m!=pred:
            fails+=1
            if fails<=8:
                print(f"MISMATCH p={p} b={b}: model min={m} predicted={pred} bad={bad[:3]}")
print(f"checked {checked} (p,b) pairs, {fails} mismatches")
# best per prime, worst ratio
worst=(1,None)
for p in [q for q in sieve(3000) if q>=11]:
    best=0; bb=0
    for b in range((p-1)//2,2,-1):
        if b*(p-b-1)<=best: break
        if minus_one(p,b) is not None:
            best=b*(p-b-1); bb=b
    r=best/p**2
    if r<worst[0]: worst=(r,(p,bb,best))
print("worst run+jump ratio, primes 11..3000:", worst)
