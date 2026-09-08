"""Structure of the best E<=1 background cycles: print the cycle and D_i/p."""
import sys
from math import gcd
from fractions import Fraction

def isprime(n):
    if n < 2: return False
    d = 2
    while d*d <= n:
        if n % d == 0: return False
        d += 1
    return True

def emin(p, D, A, C, Emax):
    if gcd(A, D) != 1 or gcd(C, D) != 1: return None
    tgt = (-A) % D
    x = C % D; seen = set(); e = 0
    while x not in seen:
        if x == tgt: return e
        seen.add(x); x = (x*p) % D; e += 1
        if Emax is not None and e > Emax: return None
    return None

def build(p, Emax, frac=0.15):
    lo = max(3, int(frac*p)); hi = min(p-1, int((1-frac)*p)+2)
    Ds = list(range(lo, hi+1))
    states = [(A,B) for A in Ds for B in Ds if A != B and gcd(A,B)==1]
    adj = {}
    costs = set()
    for (A,B) in states:
        out = []
        for C in Ds:
            if C == B or gcd(B,C) != 1: continue
            e = emin(p, B, A, C, Emax)
            if e is None: continue
            cost = C*(p-B)
            out.append(((B,C), cost, e)); costs.add(cost)
        adj[(A,B)] = out
    return states, adj, sorted(costs)

def best(p, Emax):
    states, adj, costs = build(p, Emax)
    if not costs: return 0, None, None
    def prune(T):
        succ = {s: [(t,e) for (t,c,e) in adj[s] if c >= T] for s in states}
        alive = set(states); ch = True
        while ch:
            ch = False
            for s in list(alive):
                if not any(t in alive for (t,e) in succ[s]):
                    alive.discard(s); ch = True
        return alive, succ
    lo, hi, b, info = 0, len(costs)-1, 0, None
    while lo <= hi:
        m = (lo+hi)//2
        alive, succ = prune(costs[m])
        if alive: b = costs[m]; info = (alive, succ); lo = m+1
        else: hi = m-1
    return b, info[0], info[1]

def cyc(alive, succ):
    s = min(alive); seen = {}; path = []
    while s not in seen:
        seen[s] = len(path); path.append(s)
        s = [t for (t,e) in succ[s] if t in alive][0]
    return path[seen[s]:]

for p in [11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]:
    if not isprime(p): continue
    b, alive, succ = best(p, 1)
    if b == 0:
        print(f"p={p}: none"); continue
    c = cyc(alive, succ)
    Dseq = [x[1] for x in c]
    fr = [f"{Fraction(D,p)}" for D in Dseq]
    print(f"p={p:>4} cost={b:>6} ratio={b/p**2:.4f} cycle D = {Dseq}  D/p = {fr}")
    sys.stdout.flush()
