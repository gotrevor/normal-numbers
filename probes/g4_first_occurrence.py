#!/usr/bin/env -S uv run --quiet python3
"""First-occurrence horizon N(4,L) = max over length-L base-4 words of the first position
where the word occurs in the digits of G4 = sum omega(n)/4^n.

`isRich_of_effDisjRate` (SwingC3.lean) needs N(b,L) = O_b(b^L).  A random/normal sequence has
N(b,L) ~ L b^L log b (coupon collector); a de Bruijn-like sequence achieves b^L.  This probe
decides which regime G4 is in, by tabulating N(4,L)/4^L.

Known-answer check: the digits start 0,1,1,1,1,2,1,1,1,2,..., so for L=1 the word (0,) first
occurs at position 0 and (1,) at position 1; the L=1 horizon is at least 2 (digit 3 appears
later).  Asserted below.
"""
import sys
from collections import defaultdict

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
GUARD = 500
M = N + GUARD
omega = bytearray(M+1)
for p in range(2, M+1):
    if omega[p] == 0:
        for q in range(p, M+1, p):
            omega[q] += 1
d = [0]*(M+1)
carry = 0
for n in range(M, 0, -1):
    t = omega[n] + carry
    d[n] = t & 3
    carry = t >> 2
d = d[1:N+1]
assert d[:10] == [0,1,1,1,1,2,1,1,1,2], d[:10]

print(f"N = {N}")
for L in range(1, 12):
    first = {}
    code = 0
    mask = (1 << (2*L)) - 1
    for i, x in enumerate(d):
        code = ((code << 2) | x) & mask
        if i >= L-1 and code not in first:
            first[code] = i - L + 1
    tot = 4**L
    if len(first) < tot:
        print(f"L={L:2d}: only {len(first)}/{tot} words seen by N -- horizon > {N} "
              f"(> {N/4**L:.1f} * 4^L)")
        break
    h = max(first.values())
    arg = max(first, key=first.get)
    word = tuple((arg >> (2*(L-1-j))) & 3 for j in range(L))
    print(f"L={L:2d}: horizon N(4,L) = {h:>10}  = {h/4**L:8.2f} * 4^L   "
          f"(coupon-collector L*ln(4^L) ~ {L*4**L*1.386:.0f})  worst word {word}")
