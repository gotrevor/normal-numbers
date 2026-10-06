#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Exponential sums over inverses of Cantor-digit integers mod 3^b.

S(n) = sum_{P in C_b, 3 ∤ P} e(n * P^{-1} mod 3^b / 3^b), C_b = integers < 3^b with ternary
digits in {0, 2}.  Compared with the same sum over P itself (a Riesz product, which does not
decay: n = 1 keeps about 0.37 of the mass).  One FFT of the indicator gives every S(n).

Usage: cantor_inverse_sums.py [bmin] [bmax]
       cantor_inverse_sums.py test
"""
import subprocess
import sys
from pathlib import Path

import numpy as np


def cantor_units(b: int) -> np.ndarray:
    """Integers < 3^b with ternary digits in {0,2} and last digit 2 (units mod 3)."""
    vals = np.array([0], dtype=np.int64)
    for i in range(b):
        digits = [2] if i == 0 else [0, 2]
        vals = np.concatenate([vals + d * 3 ** i for d in digits])
    return vals


def max_ratio(b: int, invert: bool) -> tuple:
    """max over n with 3 ∤ n of |S(n)| / |C|, and the argmax."""
    M = 3 ** b
    P = cantor_units(b)
    pts = np.array([pow(int(x), -1, M) for x in P], dtype=np.int64) if invert else P
    ind = np.zeros(M)
    np.add.at(ind, pts, 1.0)
    S = np.fft.fft(ind)
    n = np.arange(M)
    mask = (n % 3) != 0
    r = np.abs(S[mask]) / len(P)
    k = int(np.argmax(r))
    return float(r[k]), int(n[mask][k])


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        here = Path(__file__).resolve().parent
        sys.exit(subprocess.call(["uv", "run", "--quiet", "--with", "numpy", "--with", "pytest",
                                  "pytest", "-q", str(here / "test_cantor_inverse_sums.py")]))
    bmin = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    bmax = int(sys.argv[2]) if len(sys.argv) > 2 else 13
    print(" b   |C|     direct max|S|/|C| (n)     inverse max|S|/|C| (n)    sqrt-floor 1/sqrt|C|")
    for b in range(bmin, bmax + 1):
        d, nd = max_ratio(b, False)
        v, nv = max_ratio(b, True)
        c = len(cantor_units(b))
        print(f"{b:2d} {c:6d}   {d:.4f} ({nd})   {v:.4f} ({nv})   {c ** -0.5:.4f}")
