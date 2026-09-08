"""The run+jump family:  M(p,1) >= b(p-b-1)  whenever -1 in <p> (mod b), 3<=b<p/2.
Measure the best b per prime and the worst ratio over a range."""
import sys
from math import gcd

def sieve(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]

def minus_one_in_orbit(p, b):
    if gcd(p,b)!=1: return False
    tgt=(b-1)%b; x=p%b; seen=set()
    while x not in seen:
        if x==tgt: return True
        seen.add(x); x=(x*p)%b
    return False

def bestb(p):
    best=(0,0)
    for b in range((p-1)//2, 2, -1):
        if b*(p-b-1) <= best[1]: break
        if minus_one_in_orbit(p,b):
            v=b*(p-b-1)
            if v>best[1]: best=(b,v)
    return best

primes = [p for p in sieve(20000) if p>=11]
worst=(1.0,None); rows=[]
for p in primes:
    b,v = bestb(p)
    r = v/p**2
    rows.append((p,b,v,r))
    if r < worst[0]: worst=(r,(p,b,v))
print("worst ratio over primes 11..20000:", worst)
# distribution
import statistics
rs=[r for (_,_,_,r) in rows]
print("min %.4f  median %.4f  mean %.4f  max %.4f" % (min(rs), statistics.median(rs), statistics.mean(rs), max(rs)))
below = [(p,b,r) for (p,b,v,r) in rows if r < 1/12]
print("count with ratio < 1/12 = 0.0833:", len(below), below[:20])
below2 = [(p,b,round(r,4)) for (p,b,v,r) in rows if r < 0.15]
print("count with ratio < 0.15:", len(below2), below2[:25])
