#!/usr/bin/env -S uv run --quiet python3
"""Probe: fixed-frequency Weyl cancellation along the Stoneham staircase (rung T3).

Given the readout theorem (probe-verified), block k of alpha_{2,3}'s base-6
expansion is the x6-orbit of 2^-(3^k - k):  v_j = 3^a mod 2^c / 2^c with
c decreasing by 1 and a increasing by 1 each step.  6-disjunctivity needs the
block orbits to visit every interval for infinitely many k; by Erdos-Turan it
SUFFICES that for each FIXED h, the Weyl sum

    S_h(k) = sum_j e(h * v_j)   over the block's non-trivial segment

is o(block length) along infinitely many k.  This is a single fixed-frequency
exponential sum over a short x6-orbit in the 2-adic solenoid — the honest
frontier object (full-period equidistribution is classical Postnikov-Korobov;
our segment is LINEAR in c, far below the 2^(c/2) root barrier).

This probe measures |S_h(k)| / A_k for h = 1..8, blocks k = 5..11, over the
segment where the readout is nondegenerate (3^a > 2^c/6, i.e. past the forced
zero-run).  Random-model prediction: |S_h|/A ~ A^(-1/2).  A stubborn plateau
at some h would be structure (and a finding); steady decay arms the rung.

Also reports per-block length-3 base-6 word coverage of the readout digits.
"""

import sys
from cmath import exp as cexp
from math import pi, log2, sqrt


def block_weyl(k: int, hs: list[int]) -> tuple[int, dict[int, float], int]:
    """Iterate v_j over block k's nondegenerate segment; return (A, |S_h|/A, words3)."""
    S3k = 3 ** k
    # positions n in (3^(k-1), 3^k); a = n - k, c = 3^k - n
    n0 = 3 ** (k - 1) + 1
    # start of nondegenerate segment: 3^a * 6 >= 2^c  <=>  a*log2(3) >= c - log2(6)
    # with a = n - k, c = S3k - n:  n >= (S3k + k*log2(3) - log2(6)) / (1 + log2(3))
    L3 = log2(3)
    n_start = max(n0, int((S3k + k * L3 - log2(6)) / (1 + L3)) - 2)
    a = n_start - k
    c = S3k - n_start
    R = pow(3, a, 1 << c)
    sums = {h: 0j for h in hs}
    count = 0
    words = set()
    prev2 = []
    n_end = S3k - 65  # keep c > 64 so the float angle is meaningful
    while n_start + count <= n_end:
        # v = R / 2^c via top 64 bits
        top = (R >> (c - 64)) if c > 64 else (R << (64 - c))
        v = top / 18446744073709551616.0
        for h in hs:
            sums[h] += cexp(2j * pi * h * v)
        d = int(6 * v)
        prev2.append(d)
        if len(prev2) >= 3:
            words.add(tuple(prev2[-3:]))
        count += 1
        # step: v <- 6v mod 1  ==  R' = 3R mod 2^(c-1), c' = c-1
        c -= 1
        R = (3 * R) & ((1 << c) - 1)
    return count, {h: abs(sums[h]) / count for h in hs}, len(words)


def main() -> None:
    hs = list(range(1, 9))
    print("fixed-h Weyl sums |S_h|/A over the nondegenerate block segment")
    print("(random model: ~A^-1/2; a plateau = structure):\n")
    header = f"{'k':>3} {'A':>7} {'A^-1/2':>8} " + " ".join(f"{'h='+str(h):>7}" for h in hs) + f" {'w3':>4}"
    print(header)
    for k in range(5, 12):
        A, ratios, w3 = block_weyl(k, hs)
        row = f"{k:>3} {A:>7} {1/sqrt(A):>8.4f} " + \
              " ".join(f"{ratios[h]:>7.4f}" for h in hs) + f" {w3:>4}"
        print(row)
    print("\nw3 = distinct length-3 base-6 words among the block's readout digits")
    print("(216 possible; coverage growing with k arms PowersOfThreeReadoutDense)")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
