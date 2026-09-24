#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# ///
"""Probe: is SwingC2.CarryLeaf TRUE at K = 0?

CarryLeaf b says: for all K M r a N with 0 < M, gcd(r,M)=1, a <= b^(K/2), M <= 2^(b^(K/2)),
N <= b^(K/2), there is a prime p > N with p = r (mod M) and
    carry b tau (2^a p + K) = floor( sum_{k>=0} tau(2^a p + K + 1 + k) / b^(k+1) )  <  b^K.

At K = 0 the side conditions read a <= 1, M <= 2, N <= 1, and the budget is b^0 = 1, i.e. the
carry must be ZERO.  This probe sweeps all admissible (a, M, r) and all primes p up to a bound
and reports the minimum carry.  If that minimum is >= 1 for every admissible datum, CarryLeaf is
FALSE at K = 0 and needs the hypothesis 1 <= K.

Known-answer check (hand-computed, b = 3, a = 1, p = 3, so m = 6):
  tau(7)=2, tau(8)=4, tau(9)=3, tau(10)=4, tau(11)=2, tau(12)=6, ...
  sum >= 2/3 + 4/9 + 3/27 + 4/81 = .6667+.4444+.1111+.0494 = 1.2716 > 1, so carry >= 1.
"""
from fractions import Fraction
from math import gcd

LIM = 20000
_tau = [0] * (LIM + 1)
for d in range(1, LIM + 1):
    for m in range(d, LIM + 1, d):
        _tau[m] += 1

def divisor_count(n):
    return _tau[n]

def primerange(lo, hi):
    sieve = bytearray([1]) * hi
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(hi ** .5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    return [i for i in range(lo, hi) if sieve[i]]


def carry(b, m, terms=40):
    s = Fraction(0)
    for k in range(terms):
        s += Fraction(int(divisor_count(m + 1 + k)), b ** (k + 1))
    return s

# known-answer check
b, m = 3, 6
partial = sum(Fraction(int(divisor_count(m + 1 + k)), b**(k+1)) for k in range(4))
assert partial == Fraction(2,3)+Fraction(4,9)+Fraction(3,27)+Fraction(4,81), partial
assert float(partial) > 1.27 and float(partial) < 1.28, float(partial)
assert int(carry(3, 6)) >= 1

print("known-answer check OK\n")

for b in (3, 4, 5, 10):
    print(f"--- base b = {b} (budget b^0 = 1, carry must be 0) ---")
    worst = None
    for M in (1, 2):
        for r in range(M):
            if gcd(r, M) != 1:
                continue
            for a in (0, 1):
                best = None
                for p in primerange(2, 4000):
                    if p <= 1:
                        continue
                    if p % M != r % M:
                        continue
                    c = int(carry(b, 2**a * p))
                    if best is None or c < best[0]:
                        best = (c, p)
                print(f"  M={M} r={r} a={a}: min carry over p<4000 = {best[0]} at p={best[1]}")
                worst = best[0] if worst is None else min(worst, best[0])
    print(f"  => min over all admissible data: {worst}"
          f"  {'CarryLeaf HOLDS at K=0' if worst == 0 else 'CarryLeaf FALSE at K=0'}\n")
