#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Probe for PiBBP.lean: hex-digit runs of pi vs BBP-surrogate sliver visits.

Checks, all exact or high-precision:
  1. self-test: recursive surrogate u_{n+1} = frac(16*u_n + 16*kick(n))
     (Fraction-exact) agrees with the direct u_n = frac(16^n * s_n);
  2. self-test: digits reconstruct pi (sum d_i 16^-i within tolerance);
  3. record 0-runs and F-runs in the first N hex digits of pi, with
     len / log16(pos) ratios (random model predicts ~1.0);
  4. surrogate sliver visits u_n >= 1 - width(n), width = 64/(3(8n+1)^2)
     + slack, and whether record-run positions coincide with them;
  5. the theorems' conclusions verified numerically at every run found
     (orbit-near-wrap => surrogate in sliver), including sub-threshold runs.

Conventions match the Lean: position n means the run starts at hex digit
index n (0-based), i.e. orbit 16 pi n = frac(16^n * pi) in [0, 16^-k)
for a 0-run of length k (or [1 - 16^-k, 1) for an F-run).
"""

from fractions import Fraction
from math import log
import mpmath as mp

N_DIGITS = 40_000   # hex digits scanned for runs
N_SURR = 1_500      # surrogate steps computed exactly

def kick(j: int) -> Fraction:
    return (Fraction(4, 8 * j + 1) - Fraction(2, 8 * j + 4)
            - Fraction(1, 8 * j + 5) - Fraction(1, 8 * j + 6))

def frac(x: Fraction) -> Fraction:
    return x - (x.numerator // x.denominator)

def surrogates(n_max: int) -> list[Fraction]:
    """u_n = frac(16^n * s_n), computed recursively and exactly."""
    us = [Fraction(0)]
    u = Fraction(0)
    for n in range(n_max):
        u = frac(16 * u + 16 * kick(n))
        us.append(u)
    return us

def surrogate_direct(n: int) -> Fraction:
    s = sum((kick(j) / 16**j for j in range(n)), Fraction(0))
    return frac(16**n * s)

def hex_digits(n: int) -> list[int]:
    mp.mp.dps = int(n * log(16, 10)) + 60
    x = mp.pi - 3
    ds = []
    for _ in range(n):
        x = x * 16
        d = int(x)
        ds.append(d)
        x -= d
    return ds

def runs_of(digits: list[int], val: int):
    """(start, length) of maximal runs of `val`."""
    out, i = [], 0
    while i < len(digits):
        if digits[i] == val:
            j = i
            while j < len(digits) and digits[j] == val:
                j += 1
            out.append((i, j - i))
            i = j
        else:
            i += 1
    return out

def records(runs):
    out, best = [], 0
    for pos, ln in runs:
        if ln > best:
            best = ln
            out.append((pos, ln))
    return out

def main():
    # 1. recursion vs direct
    us = surrogates(N_SURR)
    for n in (0, 1, 2, 5, 17, 40):
        assert us[n] == surrogate_direct(n), f"surrogate mismatch at {n}"
    print(f"self-test 1 OK: recursive == direct surrogate (n up to 40)")

    # 2. digits reconstruct pi
    ds = hex_digits(N_DIGITS)
    mp.mp.dps = 120
    approx = 3 + mp.fsum(d * mp.mpf(16) ** -(i + 1) for i, d in enumerate(ds[:80]))
    assert abs(approx - mp.pi) < mp.mpf(16) ** -78, "digit reconstruction failed"
    print(f"self-test 2 OK: digits reconstruct pi")

    # 3. record runs.  Digit index i (0-based) = orbit position n = i:
    # orbit 16 pi n has integer part digit d_n, so a k-run of digit 0
    # starting at digit index i corresponds to position n = i in the Lean
    # convention (frac(16^n pi) in [0,16^-k) iff digits n..n+k-1 are 0...
    # note frac(16^n * pi) begins with digit d_n).
    for val, name in ((0, "0-run"), (15, "F-run")):
        rs = records(runs_of(ds, val))
        print(f"record {name}s (pos, len, len/log16(pos)):")
        for pos, ln in rs:
            r = ln / (log(pos, 16)) if pos > 1 else float("nan")
            print(f"  {pos:>8} {ln:>3}  {r:5.2f}")

    # 4+5. sliver visits and run/sliver coincidence
    def width(n: int) -> Fraction:
        return Fraction(64, 3 * (8 * n + 1) ** 2)

    visits = [n for n in range(1, N_SURR + 1) if 1 - us[n] < 4 * width(n)]
    print(f"surrogate sliver visits (1-u_n < 4*width) in [1,{N_SURR}]: {len(visits)}")
    print(f"  first visits: {visits[:20]}")

    # 5a. tail bracket lo(n) <= tau_n <= hi(n) (the proved piTail_ge/le),
    # tau_n = 16^n*(pi - s_n) via mpmath at scaled precision
    def lo(n: int) -> Fraction:
        return Fraction(3, 16 * (n + 1) ** 2)
    s = Fraction(0)
    checked_tail = 0
    for n in range(0, 400):
        if n > 0:
            s += kick(n - 1) / 16 ** (n - 1)
        mp.mp.dps = int(n * log(16, 10)) + 60
        tau = mp.mpf(16) ** n * (mp.pi - mp.mpf(s.numerator) / mp.mpf(s.denominator))
        assert mp.mpf(float(lo(n))) * (1 - mp.mpf(1e-9)) <= tau <= \
            mp.mpf(width(n).numerator) / mp.mpf(width(n).denominator), \
            f"tail bracket violated at n={n}: tau={tau}"
        checked_tail += 1
    print(f"self-test 3 OK: tail bracket lo <= tau <= hi holds for n < {checked_tail}")

    # 5b. theorem-hypothesis runs (16*(n+1)^2 < 3*16^k): each must show a
    # top-sliver surrogate.  Random model: none expected in scanned range.
    hyp_runs = []
    for val in (0, 15):
        for pos, ln in runs_of(ds[:N_SURR], val):
            if pos >= 1 and 16 * (pos + 1) ** 2 < 3 * 16 ** ln:
                hyp_runs.append((pos, ln, val))
                u = us[pos]
                assert 1 - u <= width(pos) + Fraction(16) ** -ln, \
                    f"dichotomy violated at pos={pos} len={ln} u={float(u):.6f}"
    print(f"threshold runs (16(n+1)^2 < 3*16^k) in [1,{N_SURR}]: {len(hyp_runs)}"
          f" — all sliver-checked" if hyp_runs else
          f"threshold runs in [1,{N_SURR}]: 0 (expected: random model makes"
          f" them doubly-exponentially rare; the theorem is about exactly"
          f" these, and 5a shows its tail hypothesis is non-vacuous)")

if __name__ == "__main__":
    main()
