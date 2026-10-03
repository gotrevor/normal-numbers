#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Numeric tripwire for `BakerBanajiAnalytic` (ExplicitOmegaK.lean), on the measure nu_L, L = 2.

nu_2 = law of y = 2/4 + sum_{i>=2} D_i 4^{-i}, D_i iid uniform on {0,1,2} (base-4 digits, leading
digit 2, top digit 3 never used).  Support is in [1/2, 1/2 + 2/12] = [1/2, 2/3] inside the window.
It is the stationary measure of the 3 maps t -> t/4 + 3/8 + d/16 (fixed points 1/2, 7/12, 2/3),
weights 1/3: `IsSelfSimilarOnWindow`.

Method (exact, no sampling).  Enumerate the 3^N prefixes D_2..D_{N+1}; the tail is
delta = 4^{-(N+1)} W, W = sum_{j>=1} D_j 4^{-j}, independent of the prefix, with
  phi_W(s) = E e(-s W) = prod_j (1 + e(-s 4^{-j}) + e(-2 s 4^{-j})) / 3.
Linearising F over the tail, E e(-xi F(y)) = mean_prefix e(-xi F(y_N)) phi_W(xi F'(y_N) 4^{-(N+1)}),
with phase error <= pi |xi| max|F''| diam(tail)^2 = pi xi (1/(2 sqrt 2)) ((2/3) 4^{-(N+1)})^2,
about 3e-8 for xi = 4^10, N = 11.  Exact for affine F.

  sqrt : |FT| should decay along xi = 4^k (Baker-Banaji Cor 1.5 / Thm 1.1).
  4t   : affine control.  Hand computation: for k >= 1, 4^{k+1} y = integer + W' with W' ~ W, so
         |FT(4^k)| = |phi_W(1)| = prod_{j>=1} (1 - (4/3) sin^2(pi 4^{-j}))
               = (1/3)(0.949253)(0.996790)(0.999799)(0.9999875)... = 0.31533 for every k: NO decay.
         (|1 + z + z^2| / 3 = |sin(3x)/(3 sin x)| = 1 - (4/3) sin^2 x for z = e(2x/2pi), x = pi 4^{-j}.)

Run: probes/bakerbanaji_nuL_probe.py   (exit 0 = all assertions pass)
"""
import numpy as np

CONTROL_HAND = 0.31533  # hand-computed above, NOT captured from this script


def prefixes(N):
    idx = np.arange(3**N, dtype=np.int64)
    y = np.full(idx.shape, 0.5)
    for i in range(N):
        y += (idx % 3) * 4.0 ** -(i + 2)
        idx //= 3
    return y


def phi_W(s, J=40):
    out = np.ones_like(s, dtype=complex)
    for j in range(1, J + 1):
        z = np.exp(-2j * np.pi * s * 4.0 ** -j)
        out *= (1 + z + z * z) / 3
    return out


def ft(F, dF, xi, N):
    y = prefixes(N)
    tail = phi_W(xi * dF(y) * 4.0 ** -(N + 1))
    return abs(np.mean(np.exp(-2j * np.pi * xi * F(y)) * tail))


def main():
    sq, dsq = np.sqrt, lambda t: 0.5 / np.sqrt(t)
    af, daf = (lambda t: 4.0 * t), (lambda t: np.full_like(t, 4.0))
    print(f"{'k':>3} {'xi':>9} {'|FT sqrt| N=11':>16} {'N=13':>12} {'|FT 4t|':>10}")
    rows = []
    for k in range(4, 11):
        xi = 4.0**k
        s11, s13 = ft(sq, dsq, xi, 11), ft(sq, dsq, xi, 13)
        a = ft(af, daf, xi, 11)
        rows.append((k, s13, a))
        print(f"{k:>3} {int(xi):>9} {s11:>16.3e} {s13:>12.3e} {a:>10.5f}")
        assert abs(s11 - s13) < 1e-6, ("truncation not converged", k, s11, s13)
        assert abs(a - CONTROL_HAND) < 2e-4, ("affine control off hand value", k, a)
    # Decay tripwire: the top three frequencies all sit well below the non-decaying control.
    top = [s for k, s, _ in rows if k >= 8]
    assert max(top) < 0.2 * CONTROL_HAND, ("sqrt pushforward not decaying", top)
    print("OK: control flat at", CONTROL_HAND, "; sqrt max over xi in [4^8, 4^10] =", f"{max(top):.3e}")


if __name__ == "__main__":
    main()
