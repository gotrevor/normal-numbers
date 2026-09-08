"""Max-bottleneck cycle in the background-junction graph.

Model (derived 2026-09-08 reflection lap):
  vertices  = backgrounds D, 3 <= D <= p-1
  a walk    = ... -> D_{i-1} -> D_i -> D_{i+1} -> ...
  junction D -> D' costs  D'*(p - D)   (first failing channel)
  orbit condition at D_i (needs prev and next):  exists e >= 0 with
      p^e * D_{i+1} == -D_{i-1}   (mod D_i)
  consecutive backgrounds coprime.
Then M(p,1) should equal   max over closed walks of  min edge cost.
"""
import sys
from math import gcd

def orbit_ok(p, D, A, C):
    """exists e >= 0 : p^e * C = -A (mod D)."""
    if gcd(A, D) != 1 or gcd(C, D) != 1:
        return None
    tgt = (-A) % D
    x = C % D
    e = 0
    seen = set()
    while x not in seen:
        seen.add(x)
        if x == tgt:
            return e
        x = (x * p) % D
        e += 1
    return None

def best_cycle(p, Dmin=None, Dmax=None, verbose=False):
    if Dmin is None: Dmin = 3
    if Dmax is None: Dmax = p - 1
    Ds = list(range(Dmin, Dmax + 1))
    # states (A,B) with gcd(A,B)=1, A!=B
    states = [(A, B) for A in Ds for B in Ds if A != B and gcd(A, B) == 1]
    idx = {s: i for i, s in enumerate(states)}
    # transitions (A,B) -> (B,C) with cost C*(p-B)
    adj = {s: [] for s in states}
    for (A, B) in states:
        for C in Ds:
            if C == B or gcd(B, C) != 1:
                continue
            if orbit_ok(p, B, A, C) is None:
                continue
            cost = C * (p - B)
            if cost <= 0:
                continue
            adj[(A, B)].append(((B, C), cost))
    # binary search on threshold: does the subgraph with cost>=T contain a cycle?
    def has_cycle(T):
        # iteratively prune states with no outgoing/incoming edge, then check
        succ = {s: [t for (t, c) in adj[s] if c >= T] for s in states}
        alive = set(s for s in states)
        changed = True
        while changed:
            changed = False
            # prune no-outgoing
            for s in list(alive):
                if not any(t in alive for t in succ[s]):
                    alive.discard(s); changed = True
        return len(alive) > 0, alive, succ
    costs = sorted({c for s in states for (_, c) in adj[s]})
    lo, hi, best = 0, len(costs) - 1, 0
    bestalive = None
    while lo <= hi:
        mid = (lo + hi) // 2
        ok, alive, succ = has_cycle(costs[mid])
        if ok:
            best = costs[mid]; bestalive = (alive, succ); lo = mid + 1
        else:
            hi = mid - 1
    return best, bestalive

CENSUS = {5:6, 7:9, 11:25, 13:35, 17:64, 19:80, 23:120, 29:192, 31:224}

if __name__ == "__main__":
    for p in [5,7,11,13,17,19,23,29,31]:
        b, info = best_cycle(p)
        c = CENSUS[p]
        mark = "OK " if b == c else "!! "
        print(f"{mark}p={p:3d}  model={b:5d}  census={c:5d}  floor(p/2)^2={(p//2)**2:5d}")
        sys.stdout.flush()
