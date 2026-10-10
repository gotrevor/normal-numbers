#!/usr/bin/env python3
"""Base-10 analogue of the Erdős gap-triples tree (zeroless powers of two).

Ambient: residues r mod 10^d with 2^d | r  (the 10-adic ideal e_5 Z_10 = {0} x Z_5;
2^n mod 10^d lies here for n >= d).  Children of r at depth d: r + j 10^d with
2^{d+1} | r + j 10^d, i.e. j == r/2^d (mod 2): five lifts, digit j.
Tuple condition: r and every M*r (M = 2^a) have nonzero digits 0..d-1.
Unlike base 3 this is NOT a finite carry automaton (the parity bit r/2^d mod 2 is a
function of all of r), so survival has no cycle certificate; death at a finite depth
is still a finite certificate.

levels(Ms, D, cap) -> list of level sizes (None past cap).
death_depth(Ms, D) -> least d with an empty level (DFS), or None if alive at D."""
import sys

def children(r, d):
    par = (r >> d) & 1          # r/2^d mod 2 (r is divisible by 2^d)
    p = 10 ** d
    for j in range(1, 10):      # j = 0 is the forbidden digit
        if j % 2 == par:
            yield r + j * p

def ok(r, d, Ms):
    """digit d of each M*r is nonzero (digit d of r itself is checked by children)."""
    p = 10 ** d
    return all((M * r // p) % 10 != 0 for M in Ms)

def levels(Ms, D, cap=2_000_000):
    lev = [0]; sizes = []
    for d in range(D):
        nxt = [c for r in lev for c in children(r, d) if ok(c, d, Ms)]
        sizes.append(len(nxt))
        if not nxt or len(nxt) > cap:
            if len(nxt) > cap: sizes[-1] = None
            break
        lev = nxt
    return sizes

def death_depth(Ms, D):
    """Least d such that no residue survives digits 0..d-1, i.e. level d-1 empty -> return d."""
    best = [0]
    def dfs(r, d):
        if d == D: return True
        for c in children(r, d):
            if ok(c, d, Ms):
                if d + 1 > best[0]: best[0] = d + 1
                if dfs(c, d + 1): return True
        return False
    sys.setrecursionlimit(10000)
    if dfs(0, 0): return None
    return best[0] + 1

def powers_check(D):
    """Independent instrument: zeroless residues of 2^n mod 10^D over one period, n >= D."""
    per = 4 * 5 ** (D - 1); p = 10 ** D
    seen = set()
    for n in range(D, D + per):
        r = pow(2, n, p)
        if all(c != '0' for c in str(r).zfill(D)): seen.add(r)
    return len(seen)

if __name__ == "__main__":
    exps = [int(a) for a in sys.argv[2:]]
    D = int(sys.argv[1])
    Ms = [2 ** a for a in exps]
    print("multipliers 2^", exps, "levels", levels(Ms, D))
