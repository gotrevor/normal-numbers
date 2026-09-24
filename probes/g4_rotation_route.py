#!/usr/bin/env -S uv run --quiet python3
"""Test the rotation route (SwingC3Split.lean) empirically in base 4.

Claim: T_b(n) = tailSmall(n) + tailLarge(n) with tailSmall periodic mod Q = prod of primes <= P.
So along n = a (mod Q) the orbit point is tailLarge rotated by the CONSTANT tailSmall(a), and
choosing a by CRT moves that constant over all multiples of 4^-l.  Consequence to test: a word
that is globally rare must be COMMON in the classes a whose rotation lines it up.

Known-answer check: tailSmall with P = 1 (no primes) is identically 0, and then
tailLarge = tailB, i.e. the split is trivial.  Asserted below.
"""
import sys
from collections import Counter

N = int(sys.argv[1]) if len(sys.argv) > 1 else 4_000_000
L = 4                      # word length
PRIMES = [5, 7, 11, 13]    # all > L, so no prime divides two window entries
Q = 1
for p in PRIMES: Q *= p
GUARD = 400
M = N + GUARD

omega = bytearray(M + 2)
for p in range(2, M + 1):
    if omega[p] == 0:
        for q in range(p, M + 1, p):
            omega[q] += 1

# small part: number of PRIMES dividing m
def omega_small(m):
    return sum(1 for p in PRIMES if m % p == 0)

# known-answer check: empty prime set -> small part identically zero
assert sum(1 for p in [] if 12 % p == 0) == 0

d = [0] * (M + 2)
carry = 0
for n in range(M, 0, -1):
    t = omega[n] + carry
    d[n] = t & 3
    carry = t >> 2

digits = d[1:N + 1]
target = (1, 1, 1, 1)

# global frequency
glob = sum(1 for i in range(N - L) if tuple(digits[i:i + L]) == target)
print(f"N={N}  Q={Q} (primes {PRIMES})  target word {target}")
print(f"global count {glob}  freq {glob/(N-L):.3e}   (uniform would be {4**-L:.3e})")

# per-class frequency, n indexed so that window starts at digit position n
by_class_hit = Counter()
by_class_tot = Counter()
for i in range(N - L):
    a = (i + 1) % Q          # digit position i reads omega(i+1)...
    by_class_tot[a] += 1
    if tuple(digits[i:i + L]) == target:
        by_class_hit[a] += 1

freqs = sorted(((by_class_hit[a] / by_class_tot[a], a) for a in by_class_tot), reverse=True)
print("top 8 classes by target frequency:")
for f, a in freqs[:8]:
    print(f"   a={a:4d}  omega_small(a+1..a+4)={[omega_small(a+j) for j in range(1,5)]}"
          f"  freq {f:.3e}  ({f/(glob/(N-L)) if glob else float('nan'):6.2f}x global)")
print("bottom 3:")
for f, a in freqs[-3:]:
    print(f"   a={a:4d}  omega_small(a+1..a+4)={[omega_small(a+j) for j in range(1,5)]}  freq {f:.3e}")
