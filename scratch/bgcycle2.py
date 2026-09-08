"""Best background cycle with the orbit exponent capped at E.

E = 0 : identity closure only (D_{i-1} + D_{i+1} = 0 mod D_i)
E = 1 : one multiplication by p allowed at each vertex
...
E = None : unrestricted (the census model)
Reports the best min-junction-cost cycle and its ratio to p^2.
"""
import sys
from math import gcd
def isprime(n):
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def emin(p, D, A, C, Emax):
    """least e >= 0 with p^e * C = -A (mod D), or None; e <= Emax."""
    if gcd(A, D) != 1 or gcd(C, D) != 1:
        return None
    tgt = (-A) % D
    x = C % D
    seen = set()
    e = 0
    while x not in seen:
        if x == tgt:
            return e
        seen.add(x)
        x = (x * p) % D
        e += 1
        if Emax is not None and e > Emax:
            return None
    return None

def best_cycle(p, Emax=None, frac=0.18):
    lo = max(3, int(frac * p))
    hi = min(p - 1, int((1 - frac) * p) + 2)
    Ds = list(range(lo, hi + 1))
    states = [(A, B) for A in Ds for B in Ds if A != B and gcd(A, B) == 1]
    adj = {}
    allcosts = set()
    for (A, B) in states:
        out = []
        for C in Ds:
            if C == B or gcd(B, C) != 1:
                continue
            if emin(p, B, A, C, Emax) is None:
                continue
            cost = C * (p - B)
            out.append(((B, C), cost))
            allcosts.add(cost)
        adj[(A, B)] = out
    if not allcosts:
        return 0, None
    def prune(T):
        succ = {s: [t for (t, c) in adj[s] if c >= T] for s in states}
        alive = set(states)
        changed = True
        while changed:
            changed = False
            for s in list(alive):
                if not any(t in alive for t in succ[s]):
                    alive.discard(s); changed = True
        return alive, succ
    costs = sorted(allcosts)
    lo_i, hi_i, best, bestinfo = 0, len(costs) - 1, 0, None
    while lo_i <= hi_i:
        mid = (lo_i + hi_i) // 2
        alive, succ = prune(costs[mid])
        if alive:
            best = costs[mid]; bestinfo = (alive, succ); lo_i = mid + 1
        else:
            hi_i = mid - 1
    return best, bestinfo

def extract_cycle(alive, succ):
    # walk until revisit
    s = min(alive)
    seen = {}
    path = []
    while s not in seen:
        seen[s] = len(path); path.append(s)
        nxt = [t for t in succ[s] if t in alive]
        s = nxt[0]
    return [x[1] for x in path[seen[s]:]]

primes = [p for p in range(7, 90) if isprime(p)]
print(f"{'p':>4} {'E=0':>8} {'E=1':>8} {'E=2':>8} {'E=3':>8} {'free':>8}   ratios (free, E=1)")
for p in primes:
    row = []
    for E in [0, 1, 2, 3, None]:
        b, info = best_cycle(p, E)
        row.append(b)
    r_free = row[-1] / p**2
    r_1 = row[1] / p**2
    print(f"{p:>4} {row[0]:>8} {row[1]:>8} {row[2]:>8} {row[3]:>8} {row[4]:>8}   {r_free:.4f} {r_1:.4f}")
    sys.stdout.flush()
