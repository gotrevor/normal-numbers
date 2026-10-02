#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Numeric tripwire for `BakerBanajiQuarterCantor` (ExplicitSquareNonNormal.lean).

mu = law of cantorReal under fair coins: y = 1/2 + (1/8) * sum_k e_k 4^{-k}.  We truncate to
K = 20 coins (= binary digits 0..41, i.e. 40 free+forced digit positions past the leading 1) and
average EXACTLY over all 2^20 equally likely prefixes (no sampling noise), with the tail replaced
by its mean.  Tail error in the phase is <= 2*pi*|xi|*max|F'|*diam(tail) ~ 1e-12 for xi <= 2^20.

  sqrt  : |E e(xi*sqrt(y))| should DECAY along xi = 2^k (Baker-Banaji / Mosquera-Shmerkin).
  4t    : affine control.  Hand computation: E e(4 xi y) has modulus prod_k |cos(pi xi 4^{-k}/2)|;
          along xi = 2*4^j the factors k <= j are 1 and k = j+m gives |cos(pi 4^{-m})|, so the
          modulus is prod_{m=1}^{K-1-j} |cos(pi 4^{-m})| in [0.6927, 0.7072] -- NO decay.

Run: probes/bakerbanaji_sqrt_decay_probe.py   (exit 0 = all assertions pass)
"""
import math
import numpy as np

K = 20


def points():
    idx = np.arange(2**K, dtype=np.int64)
    y = np.full(idx.shape, 0.5)
    for k in range(K):
        y += ((idx >> k) & 1) * (4.0 ** -k) / 8.0
    # mean of the tail sum_{k>=K} e_k 4^{-k}/8 with fair coins
    y += 0.5 * (4.0 ** -K) / (1 - 0.25) / 8.0
    return y


def ft(vals, xi):
    return abs(np.mean(np.exp(2j * np.pi * xi * vals)))


def main():
    y = points()
    assert abs(y.min() - 0.5) < 1e-9 and abs(y.max() - 2 / 3) < 1e-9, (y.min(), y.max())
    s, a = np.sqrt(y), 4.0 * y

    print(" k   xi=2^k   |FT sqrt|   |FT 4t|")
    sq = {}
    for k in range(4, 21):
        xi = 2.0**k
        sq[k] = ft(s, xi)
        print(f"{k:2d} {xi:9.0f}  {sq[k]:.3e}  {ft(a, xi):.3e}")

    # affine control along xi = 2*4^j: hand-computed product, no decay
    for j in range(2, 10):
        xi = 2.0 * 4**j
        hand = math.prod(abs(math.cos(math.pi * 4.0**-m)) for m in range(1, K - j))
        got = ft(a, xi)
        assert abs(got - hand) < 1e-6, (j, got, hand)
        assert 0.69 < got < 0.71, (j, got)

    # sqrt decays: least-squares slope of log|FT| vs log xi over k = 8..20 is clearly negative,
    # and every value at k >= 16 is an order of magnitude below the affine plateau (~0.69)
    ks = np.arange(8, 21)
    slope = np.polyfit(ks * math.log(2), np.log([sq[k] for k in ks]), 1)[0]
    print(f"fitted exponent (|FT sqrt| ~ xi^slope, k=8..20): {slope:.3f}")
    assert slope < -0.1, slope
    assert max(sq[k] for k in range(16, 21)) < 0.069, sq
    print("OK: sqrt decays, affine control does not")


if __name__ == "__main__":
    main()
