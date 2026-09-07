#!/usr/bin/env -S uv run --quiet python3
"""Fast LOWER-BOUND screen for the universal Mahler constant sup_g M(g,1)/g^2.

The exact algorithm (mahler_exact_M.py) costs ~800 s at g = 32 and grows fast,
so it cannot survey.  This screens with the repo's background+burst family
(MahlerLowerBoundBackground.lean):

    alpha = a/(g-1) + B * sum_i g^{-i!}

Multiplying by m keeps the shape: the background becomes the constant digit
b = (m*a) mod (g-1) and the burst becomes N = m*B.  So the eventual digit set of
m*alpha is the digit set of the d-digit string  b*(g^d-1)/(g-1) + m*B  (mod g^d).
If some target digit w is missed by every m <= M, then M(g,1) > M.

Reports max over (a, B) of that first-miss depth -- a LOWER bound on M(g,1),
never the exact value.  Validated against the exact census (docs/mahler-exact-values-2026-09-07.md),
2026-09-07.  With a DENSE B-sweep (B < 24 g^2) the screen reproduces M(g,1)
exactly at g = 4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24 and at the primes
5, 7, 13 -- but falls back to the trivial witness B = 2 at g = 22, 26, 27,
where it is far short (231 vs 336, 325 vs 400, 234 vs 375).  That was a SEARCH
RANGE artifact, not a family failure: every winning burst found is a prime
power (g=18 -> 3^8, g=10 -> 5^3, g=15 -> 5^2, g=24 -> 2^5), and at 22, 26, 27
the corresponding power (11^4, 13^4, 3^9) sits just past 24 g^2.

So this version sweeps PRIME POWERS to a much higher cap, plus all small B.
It is still a LOWER bound by construction: a peak located here is a candidate
to confirm with the exact algorithm, not a result.

Usage:  mahler_universal_screen.py [GMIN] [GMAX] [BSCALE]
        BSCALE sets the prime-power burst range B < BSCALE*g^3 (default 8);
        all B < 2*g^2 are swept densely regardless.
"""
import sys, time


def first_miss(a, B, g, cap):
    """Least m at which every digit is reachable; cap+1 if some digit never is."""
    first = {}
    gm1 = g - 1
    for m in range(1, cap + 1):
        b = (m * a) % gm1
        N = m * B
        d = 0
        t = N
        while t:
            t //= g
            d += 1
        d += 3
        R = (b * (g ** d - 1) // gm1 + N) % (g ** d)
        for _ in range(d):
            first.setdefault(R % g, m)
            R //= g
        if len(first) == g:
            return m
    return cap + 1


def burst_candidates(g, bscale):
    """All small B, plus every prime power up to a much higher cap.

    Every winning burst observed in the dense sweep is a prime power, which is
    what makes a high cap affordable: the prime powers below N are only
    O(N / log N)-ish in count for the primes plus a handful of true powers.
    """
    lo_cap = 2 * g * g
    hi_cap = bscale * g * g * g
    cands = set(range(1, lo_cap))
    sieve = bytearray([1]) * hi_cap
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(hi_cap ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    for pr in range(2, hi_cap):
        if sieve[pr]:
            q = pr
            while q < hi_cap:
                cands.add(q)
                q *= pr
    return sorted(cands)


def screen(g, bscale):
    cap = int(1.05 * g * g)          # we only care about ratios near the record
    best = (0, None, None)
    for B in burst_candidates(g, bscale):
        for a in range(0, g - 1):
            v = first_miss(a, B, g, cap)
            if v > best[0]:
                best = (v, a, B)
    return best


def main():
    gmin = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    gmax = int(sys.argv[2]) if len(sys.argv) > 2 else 48
    bscale = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    print(f"# background+burst lower-bound screen: all B < 2g^2, prime powers B < {bscale}g^3")
    print(f"# {'g':>3} {'lower':>7} {'/g^2':>7}  (a, B)")
    for g in range(gmin, gmax + 1):
        t0 = time.time()
        v, a, B = screen(g, bscale)
        lo = v                        # channels 1..v-1 miss a digit => M >= v
        print(f"  {g:>3} {lo:>7} {lo / (g * g):>7.4f}  (a={a}, B={B})"
              f"   [{time.time() - t0:.1f}s]", flush=True)


main()
