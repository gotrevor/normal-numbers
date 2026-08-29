#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Probe: the Stoneham base-6 readout identity (Rosetta-stone conjecture).

Claim being tested (session 2026-08-29, new): for alpha = alpha_{2,3}
= sum_{k>=1} 1/(3^k 2^(3^k)) and n >= 3,

    frac(6^n * alpha)  =  (3^a mod 2^c) / 2^c  +  error,
        k* = min{k : 3^k > n},  a = n - k*,  c = 3^k* - n,
    |error| <= 2 * 3^(a-1) / 2^(3^(k*+1) - n)   (next-term bound, exp-small)

i.e. WITHIN A BLOCK n in (3^(k*-1), 3^k*), the base-6 digits of alpha replay
the base-6 expansion of the single dyadic rational 2^-(3^k* - k*):
    6^n alpha mod 1 ~ 6^(n - 3^(k*-1)...) * 2^-(3^k*-k*) mod 1,
equivalently the 2-adic digits of powers of 3 (3^a mod 2^c).

Consequences if the identity holds:
  - Bailey-Borwein 2012 base-6 nonnormality = the coarse shadow (the segment
    of each block where 3^a < 2^c, i.e. the readout is still < 1: zero run).
  - alpha_{2,3} is 6-DISJUNCTIVE  <=>  every base-6 word occurs in the base-6
    expansion of 2^-m for infinitely many m of the form 3^k - k (within the
    block window) — a pure statement about powers of 3 in Z_2.

Outputs: per-block max error vs the next-term prediction; word-coverage stats
of the actual base-6 digit stream; longest zero-run (should sit at block
starts, per Bailey-Borwein).

Self-tests: fixed-point digits vs mpmath at n=50; digit extraction vs mpmath
for the first 12 base-6 digits.
"""

import sys
from math import log2
import mpmath

B = 26_000          # fixed-point bits
N_MAX = 6_560       # test blocks k* = 2..8  (3^8 = 6561)

# alpha in fixed point: terms k with 3^k <= B contribute
ALPHA_FP = 0
k = 1
while 3 ** k < B:
    ALPHA_FP += (1 << B) // (3 ** k << (3 ** k))
    k += 1
MASK = (1 << B) - 1


def frac6_fp(n: int) -> int:
    """floor(2^B * frac(6^n alpha)) up to O(6^n * ulp) error."""
    return (pow(6, n) * ALPHA_FP) & MASK


def readout(n: int) -> tuple[int, int, int]:
    """(r_num, c, kstar): predicted frac = r_num / 2^c."""
    kstar = 1
    while 3 ** kstar <= n:
        kstar += 1
    a = n - kstar
    c = 3 ** kstar - n
    return pow(3, a, 1 << c), c, kstar


def main() -> None:
    # --- self-test: fixed point vs mpmath at n = 50 --------------------------
    with mpmath.workprec(1200):
        alpha = mpmath.fsum(mpmath.mpf(1) / (3 ** j * mpmath.mpf(2) ** (3 ** j))
                            for j in range(1, 8))
        want = mpmath.frac(6 ** 50 * alpha)
        got = mpmath.mpf(frac6_fp(50)) / mpmath.mpf(2) ** B
        assert abs(want - got) < mpmath.mpf(2) ** -100, "fixed-point frac6 broken"
        # first 12 base-6 digits
        x = alpha
        want_digits = []
        for _ in range(12):
            x = x * 6
            d = int(mpmath.floor(x))
            want_digits.append(d)
            x -= d
    F = ALPHA_FP
    got_digits = []
    for _ in range(12):
        F *= 6
        got_digits.append(F >> B)
        F &= MASK
    assert got_digits == want_digits, "digit extraction broken"
    print(f"self-tests OK (frac6 at n=50; first 12 base-6 digits = {got_digits})")

    # --- the readout identity, per block -------------------------------------
    print("\nreadout identity |frac(6^n a) - (3^a mod 2^c)/2^c|, per block:")
    print(f"{'block k*':>9} {'n range':>14} {'max log2 err':>13} {'predicted':>10}")
    for kstar in range(2, 9):
        lo = 3 ** (kstar - 1) + 1 if kstar > 1 else 1
        hi = min(3 ** kstar - 1, N_MAX)
        worst = -10 ** 9
        worst_pred = None
        for n in range(max(lo, 3), hi + 1):
            r_num, c, ks = readout(n)
            assert ks == kstar
            X = frac6_fp(n)
            # exact comparison at common scale 2^(B + c), circle distance
            E = abs((X << c) - (r_num << B))
            E = min(E, (1 << (B + c)) - E)
            err_log2 = (E.bit_length() - (B + c)) if E else -(B + c)
            a = n - kstar
            pred = 1.585 * (a - 1) - (3 ** (kstar + 1) - n) + 1  # next-term bound
            if err_log2 > worst:
                worst, worst_pred = err_log2, pred
        print(f"{kstar:>9} {f'({3**(kstar-1)},{hi}]':>14} {worst:>13} {worst_pred:>10.0f}")

    # --- digit stream stats ---------------------------------------------------
    F = ALPHA_FP
    digits = []
    for _ in range(N_MAX):
        F *= 6
        digits.append(F >> B)
        F &= MASK
    s = "".join(map(str, digits))
    # zero runs
    runs = []
    i = 0
    while i < len(s):
        if s[i] == "0":
            j = i
            while j < len(s) and s[j] == "0":
                j += 1
            runs.append((i + 1, j - i))
            i = j
        else:
            i += 1
    runs.sort(key=lambda t: -t[1])
    print(f"\nlongest base-6 zero-runs (pos, len): {runs[:5]}")
    print("block starts 3^k+1: 4, 10, 28, 82, 244, 730, 2188 — runs should sit there")
    for wlen in (1, 2, 3):
        seen = {s[i:i + wlen] for i in range(len(s) - wlen + 1)}
        print(f"length-{wlen} base-6 words present: {len(seen)}/{6 ** wlen}")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
