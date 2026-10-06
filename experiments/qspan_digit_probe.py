#!/usr/bin/env -S uv run --quiet python3
"""Digit statistics of rational combinations of a random digit-restricted pair.

Probe for the QSpan lane audit (2026-10-05).  Draw x, y with independent uniform base-10 digits
from a digit set D (default {0,...,4}), then for each small combination (a*x + b*y)/q measure
the deviation of its length-L block frequencies from uniform.  A normal number shows deviation
~ sqrt(10^L / N); a structural failure shows a deviation that does not shrink with N.

Usage:
  qspan_digit_probe.py [--digits 01234] [--n 200000] [--seed 1] [--amax 6] [--qmax 12]
  qspan_digit_probe.py test        # run the pytest suite next to this file
"""
import argparse
import random
import subprocess
import sys
from collections import Counter
from math import gcd
from pathlib import Path

sys.set_int_max_str_digits(0)


def random_digits(digit_set: str, n: int, rng: random.Random) -> str:
    return "".join(rng.choice(digit_set) for _ in range(n))


def combo_digits(xd: str, yd: str, a: int, b: int, q: int, n: int) -> str:
    """First n fractional digits of frac((a*x + b*y)/q), x = 0.xd, y = 0.yd.

    Exact integer arithmetic on the truncations; the last few digits are unreliable (tail
    carries), so callers use n well below len(xd)."""
    N = len(xd)
    X, Y = int(xd), int(yd)
    Z = (a * X + b * Y) % (q * 10 ** N)  # fractional part of (aX+bY)/q, scaled by 10^N
    s = str(Z // q).rjust(N, "0")
    return s[:n]


def block_deviation(s: str, L: int) -> float:
    """max |freq(w) - 10^-L| over length-L blocks w, overlapping windows."""
    total = len(s) - L + 1
    c = Counter(s[i:i + L] for i in range(total))
    expected = 1 / 10 ** L
    worst = max(abs(c.get(f"{w:0{L}d}", 0) / total - expected) for w in range(10 ** L))
    return worst


def phi(digit_set: str, t: float) -> complex:
    """Digit polynomial: mean of e(t d) over the digit set."""
    import cmath
    ds = [int(c) for c in digit_set]
    return sum(cmath.exp(2j * cmath.pi * t * d) for d in ds) / len(ds)


def nu_hat(digit_set: str, a: int, b: int, h: int, terms: int = 40) -> complex:
    """Stationary Fourier coefficient of a*x + b*y mod 1 for x, y with independent iid digits:
    prod_{i>=1} phi(a h / 10^i) * phi(b h / 10^i).  Exact zero iff some factor vanishes."""
    from fractions import Fraction
    out = 1
    for i in range(1, terms + 1):
        out *= phi(digit_set, float(Fraction(a * h, 10 ** i) % 1)) * \
               phi(digit_set, float(Fraction(b * h, 10 ** i) % 1))
    return out


def empirical_hat(s: str, h: int, window: int = 15) -> complex:
    """(1/n) sum_n e(h * frac(10^n z)) from the digit string s of z."""
    import cmath
    n = len(s) - window
    return sum(cmath.exp(2j * cmath.pi * h * int(s[i:i + window]) / 10 ** window)
               for i in range(n)) / n


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--digits", default="01234")
    ap.add_argument("--n", type=int, default=200000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--amax", type=int, default=6)
    ap.add_argument("--qmax", type=int, default=12)
    ap.add_argument("--L", type=int, default=2)
    args = ap.parse_args(argv)
    rng = random.Random(args.seed)
    xd = random_digits(args.digits, args.n + 50, rng)
    yd = random_digits(args.digits, args.n + 50, rng)
    noise = (10 ** args.L / args.n) ** 0.5 / 10 ** args.L
    rows = []
    for a in range(-args.amax, args.amax + 1):
        for b in range(0, args.amax + 1):
            if b == 0 and a <= 0:
                continue
            for q in range(1, args.qmax + 1):
                if gcd(gcd(abs(a), b), q) != 1:
                    continue
                s = combo_digits(xd, yd, a, b, q, args.n)
                rows.append((block_deviation(s, args.L) / noise, a, b, q))
    rows.sort()
    print(f"digit set {args.digits}, N={args.n}, L={args.L}; deviation in units of sqrt-noise")
    for r, a, b, q in rows[:15]:
        print(f"  {r:8.2f}   ({a}x + {b}y)/{q}")
    print(f"  ... {len(rows)} combinations; worst {rows[-1][0]:.1f}")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        here = Path(__file__).resolve().parent
        sys.exit(subprocess.call(["uv", "run", "--quiet", "--with", "pytest", "pytest", "-q",
                                  str(here / "test_qspan_digit_probe.py")]))
    main()
