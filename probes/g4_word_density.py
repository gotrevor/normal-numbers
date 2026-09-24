#!/usr/bin/env -S uv run --quiet python3
"""Empirical base-4 digit statistics of G4 = sum_{n>=1} omega(n)/4^n.

Digit n of G4 is (omega(n) + carry_n) mod 4 where carry_n = floor((omega(n+1)+carry_{n+1})/4);
we compute the carries exactly by sweeping from a guard position downwards.

Known-answer check: omega(1..8) = 0,1,1,1,1,2,1,1 and no carry reaches that far, so the
first eight base-4 digits are 0,1,1,1,1,2,1,1.  Asserted below.
"""
import sys
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
GUARD = 500
M = N + GUARD

omega = bytearray(M+1)
for p in range(2, M+1):
    if omega[p] == 0:
        for q in range(p, M+1, p):
            omega[q] += 1

digits = [0]*(M+1)
carry = 0
for n in range(M, 0, -1):
    t = omega[n] + carry
    digits[n] = t & 3
    carry = t >> 2
d = digits[1:N+1]
assert d[:8] == [0,1,1,1,1,2,1,1], d[:8]

print(f"N={N}  digit freqs:", {k: round(sum(1 for x in d if x==k)/N,5) for k in range(4)})
for L in (1,2,3,4,5):
    cnt = Counter(tuple(d[i:i+L]) for i in range(N-L+1))
    rar = min(cnt, key=cnt.get)
    print(f"  L={L}: seen {len(cnt)}/{4**L}  rarest {rar} count {cnt[rar]}"
          f"  ones-run {tuple([1]*L)} count {cnt.get(tuple([1]*L),0)}")
