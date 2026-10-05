#!/usr/bin/env -S uv run --quiet python3
"""Rebuild the candidate backward graphs B_delta (delta in {2,4,6,8}) of Brier et al.
by enumerating every 2^a 3^b 7^c below 10^N, then count the equation families
F(s) per vertex and the per-family search sizes.

A vertex y of A_delta: a 7-smooth integer (= some digit product) whose S-orbit ends
at delta.  For even delta, 5 never divides y (Fonga sec.5 / Brier sec.5).
"""
import math, sys, json
from functools import lru_cache
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 60
LIM = 10 ** N

def S(n):
    p = 1
    for ch in str(n):
        p *= ord(ch) - 48
        if p == 0:
            return 0
    return p

def terminal(n):
    steps = 0
    while n >= 10:
        n = S(n); steps += 1
    return n, steps

# enumerate 7-smooth, 5-free
vals = []
a = 1
while a < LIM:
    b = a
    while b < LIM:
        c = b
        while c < LIM:
            vals.append(c)
            c *= 7
        b *= 3
    a *= 2
graph = {d: set() for d in (2, 4, 6, 8)}
for y in vals:
    t, _ = terminal(y)
    if t in graph:
        graph[t].add(y)

def fact(n):
    e = [0, 0, 0]
    for i, p in enumerate((2, 3, 7)):
        while n % p == 0:
            n //= p; e[i] += 1
    assert n == 1
    return tuple(e)

# digit factorizations of s = 2^A 3^B 7^C into digits 2..9 (no 5)
DIG = {2: (1, 0, 0), 3: (0, 1, 0), 4: (2, 0, 0), 6: (1, 1, 0), 7: (0, 0, 1), 8: (3, 0, 0), 9: (0, 2, 0)}
def factorizations(A, B, C):
    out = []
    n7 = C
    # choose n9, n6, n8, n4, n3, n2 :  3: n3 + 2 n9 + n6 = B ;  2: n2 + 2n4 + 3n8 + n6 = A
    for n6 in range(0, min(A, B) + 1):
        for n9 in range(0, (B - n6) // 2 + 1):
            n3 = B - n6 - 2 * n9
            rest = A - n6
            for n8 in range(0, rest // 3 + 1):
                for n4 in range(0, (rest - 3 * n8) // 2 + 1):
                    n2 = rest - 3 * n8 - 2 * n4
                    out.append({2: n2, 3: n3, 4: n4, 6: n6, 7: n7, 8: n8, 9: n9})
    return out

if __name__ == "__main__":
    print(f"enumerated {len(vals)} 7-smooth 5-free numbers < 10^{N}")
    summary = {}
    for d in (2, 4, 6, 8):
        U = sorted(graph[d])
        fams = []
        for s in U:
            A, B, C = fact(s)
            for nu in factorizations(A, B, C):
                k = sum(nu.values())
                fams.append((s, nu, k + 1))
        maxk = max(f[2] for f in fams)
        arg = [f for f in fams if f[2] == maxk][0][0]
        depth = max(terminal(y)[1] for y in U) + 1  # persistence of a preimage x is steps(S(x))+1
        print(f"delta={d}: |U|={len(U)}, families={len(fams)}, max k+1={maxk} (s={arg}={fact(arg)}), "
              f"max persistence of an n with this target (if graph complete) = {depth}")
        print("   largest vertices:", [(y, fact(y)) for y in U[-3:]])
        summary[d] = dict(U=U, fams=[(s, nu, kp1) for s, nu, kp1 in fams])
    json.dump({str(k): {"U": v["U"], "fams": [[s, {str(a): b for a, b in nu.items()}, kp] for s, nu, kp in v["fams"]]} for k, v in summary.items()},
              open("families.json", "w"))
