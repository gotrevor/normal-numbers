#!/usr/bin/env python3
"""Confirm the obstruction: mergeability of transducer states is EXACTLY equality of
the row lattice Z^2 M, taken up to scaling (a left-GL2(Z) x scalar invariant).

Mechanism: after a common input word w (W = B_{a1}...B_{a_k}, det +-1) the two states
are P M W and Q N W with P,Q products of emission matrices B_d^{-1} (det +-1).  Equal
projectively  <=>  N = lambda (Q^{-1}P) M  with Q^{-1}P in GL2(Z)  <=>  the row lattices
Z^2 M and Z^2 N agree up to scaling.  W is invertible, so it cannot change this.
"""
import sys
from fractions import Fraction as F
from math import gcd
from collections import deque
sys.path.insert(0, "probes")
from cf_transducer_sync import norm, det, image, delta, explore, pair_merge

def hnf_class(M):
    """row lattice of M in Hermite normal form, scaled to be primitive"""
    p,q,r,s = M
    rows = [[p,q],[r,s]]
    # column-style HNF of the row lattice: reduce to [[a,b],[0,c]] with a,c>0
    a,b = rows[0]; c,d = rows[1]
    # gcd on first column
    while c != 0:
        k = a // c
        a, b, c, d = c, d, a - k*c, b - k*d
    if a < 0: a, b = -a, -b
    if a == 0:
        a, b, c, d = 0, 0, 0, 0
    # now lattice = <(a,b), (0,d)>
    d = abs(d)
    if d != 0: b %= d
    g = gcd(gcd(abs(a), abs(b)), abs(d))
    if g > 1: a, b, d = a//g, b//g, d//g
    return (a, b, d)

def run(name, M0, K):
    digits = list(range(1, K+1))
    states = explore(M0, digits)
    mg = pair_merge(states, digits)
    ok = bad = 0
    ex = []
    for i,M in enumerate(states):
        for N in states[i+1:]:
            merge = (M,N) in mg or (N,M) in mg
            same  = hnf_class(M) == hnf_class(N)
            if merge == same: ok += 1
            else:
                bad += 1
                if len(ex) < 5: ex.append((M,N,merge,same,hnf_class(M),hnf_class(N)))
    classes = {}
    for M in states: classes.setdefault(hnf_class(M), []).append(M)
    print("\n=== %s  M0=%s  det=%d  states=%d  classes=%d"
          % (name, M0, det(M0), len(states), len(classes)))
    print("  class sizes:", sorted(len(v) for v in classes.values()))
    print("  classes:", sorted(classes))
    print("  pairs where mergeable == same-class: %d   mismatches: %d" % (ok, bad))
    for e in ex: print("    MISMATCH", e)
    # is the class action by digits a permutation of classes?
    for c, reps in sorted(classes.items()):
        img = {}
        for a in digits:
            tgt = set(hnf_class(delta(M,a)) for M in reps)
            img[a] = sorted(tgt)
        print("   %s -> %s" % (c, {a:v for a,v in img.items()}))

if __name__ == "__main__":
    run("x -> 2x", (2,0,0,1), 8)
    run("x -> 3x", (3,0,0,1), 6)
