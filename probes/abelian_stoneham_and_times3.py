#!/usr/bin/env -S uv run --quiet --with gmpy2 python3
"""Two abelian-normality probes (2026-09-23), each a candidate conjecture's first test.

A. Natural separation?  α₂,₃ = Σ 1/(3ᵐ 2^(3ᵐ)) is normal in base 2 (Stoneham.lean) and NOT normal
   in base 6 (Bailey–Borwein 2012), yet disjunctive in base 6 (StonehamBoundary.lean).  Is it
   ABELIAN-normal in base 6?  Print, for window length L, the worst |freq − multinomial| over
   Parikh vectors and over ordinary blocks, as z-scores (√n·dev/σ).  Control: iid uniform digits.

B. ×3 lifting?  Conjecture: x and 3x both abelian-normal in base 2 ⇒ x normal.  Test on the
   hexSwap sequence ξ (abelian-normal, not normal, `AbelianBinaryExample.lean`): is 3ξ abelian?
   If 3ξ's window one-counts are Binomial, the conjecture dies on the spot.  Control: iid bits x,
   3x (must look Binomial), and ξ itself (must look Binomial, with `0011` at 5/64).

Usage: abelian_stoneham_and_times3.py [N6] [M16]   (base-6 digits of α; hex digits of ξ)
"""
import sys, math, random, itertools
from collections import Counter
import gmpy2

N6 = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
M16 = int(sys.argv[2]) if len(sys.argv) > 2 else 250000
rng = random.Random(20260923)


def stoneham_base6(N):
    G = 64
    S = gmpy2.mpz(0)
    T = gmpy2.mpz(0)
    m = 1
    while 3 ** m - N <= int(1.6 * N) + G + 64:
        e2 = N - 3 ** m
        e3 = N - m
        if e2 >= 0:
            S += gmpy2.mpz(2) ** e2 * gmpy2.mpz(3) ** e3
        else:
            T += (gmpy2.mpz(3) ** e3 << G) >> (-e2)
        m += 1
    S += T >> G
    s = gmpy2.digits(S, 6).rjust(N, "0")
    assert len(s) == N
    return [int(ch) for ch in s]


def multinomial_p(vec, b):
    L = sum(vec)
    p = math.factorial(L)
    for v in vec:
        p //= math.factorial(v)
    return p / b ** L


def worst_z(counts, n, probs):
    """max over keys of |count/n − p| / sqrt(p(1−p)/n); keys absent from counts count as 0."""
    best = (0.0, None)
    for key, p in probs.items():
        f = counts.get(key, 0) / n
        z = abs(f - p) / math.sqrt(p * (1 - p) / n)
        if z > best[0]:
            best = (z, key, f, p)
    return best


def abelian_and_block(d, b, L):
    n = len(d) - L + 1
    parikh, block = Counter(), Counter()
    for i in range(n):
        w = tuple(d[i:i + L])
        block[w] += 1
        c = [0] * b
        for x in w:
            c[x] += 1
        parikh[tuple(c)] += 1
    pp = {}
    for w in itertools.product(range(b), repeat=L):
        c = [0] * b
        for x in w:
            c[x] += 1
        pp[tuple(c)] = multinomial_p(c, b)
    pb = {w: b ** -L for w in itertools.product(range(b), repeat=L)}
    return worst_z(parikh, n, pp), worst_z(block, n, pb)


def fmt(t):
    z, key, f, p = t
    return f"z={z:7.1f} at {key} (freq {f:.5f} vs {p:.5f})"


print("=== A. α₂,₃ in base 6 ===")
for label, d in (("iid control", [rng.randrange(6) for _ in range(N6)]), ("alpha_{2,3}", stoneham_base6(N6))):
    for L in (1, 2, 3, 4):
        ab, bl = abelian_and_block(d, 6, L)
        print(f"{label:12s} N={len(d)} L={L}  abelian {fmt(ab)}   block {fmt(bl)}")


def hexswap(h):
    return {2: 3, 5: 4, 11: 10, 12: 13}.get(h, h)


def bits_of_hex(hs):
    return [(h >> (3 - r)) & 1 for h in hs for r in range(4)]


def times3(bits):
    X = gmpy2.mpz(int("".join(map(str, bits)), 2))
    n = len(bits)
    Y = (3 * X) % (gmpy2.mpz(1) << n)
    s = gmpy2.digits(Y, 2).rjust(n, "0")
    return [int(c) for c in s[:-64]]


def binom_worst(bits, L):
    n = len(bits) - L + 1
    cnt = Counter()
    run = sum(bits[:L])
    cnt[run] += 1
    for i in range(1, n):
        run += bits[i + L - 1] - bits[i - 1]
        cnt[run] += 1
    probs = {j: math.comb(L, j) / 2 ** L for j in range(L + 1)}
    return worst_z(cnt, n, probs)


def word_freq(bits, w):
    L = len(w)
    n = len(bits) - L + 1
    return sum(1 for i in range(n) if bits[i:i + L] == w) / n


print("\n=== B. x vs 3x, base 2 ===")
hexes = [rng.randrange(16) for _ in range(M16)]
xi = bits_of_hex([hexswap(h) for h in hexes])
iid = [rng.randrange(2) for _ in range(4 * M16)]
for label, b in (("iid x", iid), ("3·iid x", times3(iid)), ("xi", xi), ("3·xi", times3(xi))):
    zs = [binom_worst(b, L)[0] for L in range(1, 9)]
    print(f"{label:8s} worst one-count z, L=1..8: " + " ".join(f"{z:6.1f}" for z in zs)
          + f"   freq(0011)={word_freq(b, [0, 0, 1, 1]):.5f} (1/16={1/16:.5f})")
