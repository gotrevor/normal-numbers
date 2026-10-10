#!/usr/bin/env python3
"""Width of the exact top-down joint tree (joint.py) by depth: the number of base-B prefixes of
length t whose interval still meets every other 0/1-digit set.  This is the integer shadow of the
covering number of the slice K_B ∩ cK_b ∩ ... at scale B^-t, the quantity Shmerkin-Wu bound by
delta^-eps.  width(bases, L) -> list of live-node counts for t = 1..L."""
import sys
from joint import next01

def width(bases, L):
    B = bases[0]; others = bases[1:]
    level = [1]; out = []
    for p in range(L - 1, -1, -1):
        live = []
        for P in level:
            lo = P * B ** p; hi = lo + (B ** p - 1) // (B - 1)
            if all(next01(b, lo) <= hi for b in others): live.append(P)
        out.append(len(live))
        if p == 0 or not live: break
        level = [Q for P in live for Q in (P * B, P * B + 1)]
    return out

if __name__ == "__main__":
    bases = [int(x) for x in sys.argv[1].split(',')]
    for L in [int(x) for x in sys.argv[2:]]:
        w = width(bases, L)
        print(bases, L, 'max', max(w), 'argmax-depth', w.index(max(w)) + 1, 'total', sum(w), flush=True)
