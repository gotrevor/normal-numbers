#!/usr/bin/env python3
"""Survivor set of {xi in [0,1]: ||b^n xi|| > b^{-c}} for b <= B, windows of radius >= minrad.
Interval subtraction, refined by zooming: usage surv.py c B minrad"""
import sys, math
from fractions import Fraction
c = float(sys.argv[1]); B = int(sys.argv[2]); minrad = float(sys.argv[3])
def ispp(b):
    for a in range(2, b):
        q = a
        while q < b: q *= a
        if q == b: return True
    return False
bases = [b for b in range(2, B + 1) if not ispp(b)]
# start with [0,1]; subtract windows stage by stage in order of decreasing radius
wins = []
for b in bases:
    d = b ** -c
    n = 0
    while True:
        rad = d * b ** -n
        if rad < minrad: break
        wins.append((rad, b, n))
        n += 1
wins.sort(reverse=True)
S = [(0.0, 1.0)]
for (rad, b, n) in wins:
    bn = b ** n
    newS = []
    for (lo, hi) in S:
        # windows k/bn +- rad intersecting [lo, hi]
        k0 = math.floor((lo - rad) * bn); k1 = math.ceil((hi + rad) * bn)
        segs = [(lo, hi)]
        for k in range(k0, k1 + 1):
            wl = k / bn - rad; wh = k / bn + rad
            nxt = []
            for (a, bb) in segs:
                if wh < a or wl > bb: nxt.append((a, bb)); continue
                if wl > a: nxt.append((a, wl))
                if wh < bb: nxt.append((wh, bb))
            segs = nxt
            if not segs: break
        newS.extend(segs)
    S = newS
    if not S:
        print('EMPTY after window (b=%d,n=%d,rad=%.3g)' % (b, n, rad)); break
if S:
    tot = sum(h - l for l, h in S)
    print('survivors: %d intervals, total %.3g' % (len(S), tot))
    for (l, h) in S[:20]: print('  [%.12f, %.12f] len %.3g' % (l, h, h - l))
