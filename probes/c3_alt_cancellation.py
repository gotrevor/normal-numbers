#!/usr/bin/env python3
"""Known-answer check for TwoPointC3Alt.altSum_depthHead_eq_zero (TT2025 (5.8)).

The shift is  r_{S,h} = p0*h + sum_{k in S} (h - (k+1)) * v[k],  S subset of {0..K-1},
the Lean file's `altShift` (Fin K index k stands for the paper's k+1).

Claim: for 1 <= h <= K the map S |-> r_{S,h} pairs subsets of opposite parity with EQUAL shift,
so the alternating sum of ANY function of the shift vanishes; for h = K+1 it does not.
Hand-computed anchor (K=3, p0=7, v=(5,11,17), h=1): the four shifts are 7, -4, -27, -38, each
hit once with sign +1 and once with -1 -> net 0 for every shift value.
"""
from collections import defaultdict
from itertools import combinations

def subsets(K):
    for r in range(K + 1):
        for S in combinations(range(K), r):
            yield S

def net_per_shift(K, p0, v, h):
    d = defaultdict(int)
    for S in subsets(K):
        r = p0 * h + sum((h - (k + 1)) * v[k] for k in S)
        d[r] += (-1) ** len(S)
    return dict(d)

def main():
    K, p0, v = 3, 7, (5, 11, 17)
    anchor = net_per_shift(K, p0, v, 1)
    assert set(anchor) == {7, -4, -27, -38}, anchor
    assert all(x == 0 for x in anchor.values()), anchor
    print("anchor (K=3,h=1) OK:", anchor)
    for K in range(1, 9):
        v = tuple(2 * k + 5 for k in range(K))
        for h in range(1, K + 1):
            d = net_per_shift(K, 13, v, h)
            assert all(x == 0 for x in d.values()), (K, h, d)
        d = net_per_shift(K, 13, v, K + 1)
        assert any(x != 0 for x in d.values()), (K, K + 1, d)
        print(f"K={K}: h=1..{K} all cancel; h={K+1} does not  (sharp)")

if __name__ == "__main__":
    main()
