#!/usr/bin/env -S uv run --quiet python3
"""Exact diagnostics for theta = sum 1/(3^k * 2^(k*k)).

Tests the finite-precision permutation of its actual seeds and constructs
small-numerator adversaries sharing a growing number of their low ternary
digits.  The adversaries refute an inference from low-digit data to short-
block cancellation.  They are NOT the actual seeds or a counterexample to
theta normality, and are not asserted to obey the full seed recurrence.

No large digit prefixes, random models, or floating-point phase estimates.
Run: uv run --no-project experiments/theta_seed_precision.py
"""

from fractions import Fraction
from math import isqrt


def seed_residues(limit: int) -> list[int]:
    """A_k mod 3^k, from A_(k+1) = 3*2^(2k+1)*A_k + 1."""
    values = [0]
    modulus = 1
    for k in range(limit):
        modulus *= 3
        values.append((3 * pow(2, 2 * k + 1, modulus) * values[-1] + 1) % modulus)
    return values


def low_seed(k: int, precision: int) -> int:
    """Finite 3-adic expression; equals A_k mod 3^r when k >= r.

    Negative powers mean modular inverses, not rational rounding.
    """
    modulus = 3 ** precision
    return sum(3 ** u * pow(2, 2 * k * u - u * u, modulus)
               for u in range(precision)) % modulus


def v3_capped(value: int, cap: int) -> int:
    value = abs(value)
    if value == 0:
        return cap
    result = 0
    while result < cap and value % 3 == 0:
        value //= 3
        result += 1
    return result


def test_seed_identity() -> None:
    seeds = seed_residues(180)
    checks = 0
    for r in range(1, 11):
        for k in range(r, 181):
            assert seeds[k] % (3 ** r) == low_seed(k, r)
            checks += 1
    # Compare with the defining finite sum, independently of the recurrence.
    for k in range(1, 21):
        direct = sum(3 ** (k - j) * 2 ** (k * k - j * j)
                     for j in range(1, k + 1))
        assert direct % (3 ** k) == seeds[k]
    print(f"seed identity: {checks} low-precision checks; 20 direct-sum checks passed")


def test_precision_permutations() -> None:
    valuation_checks = 0
    for r in range(2, 11):
        period = 3 ** (r - 2)
        values = [low_seed(k, r) for k in range(r, r + 2 * period)]
        assert values[:period] == values[period:]
        assert sorted(values[:period]) == list(range(7, 3 ** r, 9))
        for i in range(min(period, 70)):
            for j in range(i):
                assert v3_capped(values[i] - values[j], r) == min(r, v3_capped(i - j, r) + 2)
                valuation_checks += 1
        print(f"r={r:2}: all {period:5} residues 7 mod 9 visited exactly once; period repeats")
    print(f"valuation identity: {valuation_checks} pair checks passed")


def low_digit_adversaries() -> None:
    seeds = seed_residues(2048)
    print("k    matching low digits    guaranteed near-zero terms / block    Re(S)/length >=")
    for k in (128, 256, 512, 1024, 2048):
        r = isqrt(k)
        modulus = 3 ** k
        numerator = seeds[k] % (3 ** r)
        assert numerator > 0 and numerator % 9 == 7
        assert numerator % (3 ** r) == seeds[k] % (3 ** r)
        # Every t in [0,T) obeys 2^t * numerator / 3^k <= 1/100.
        threshold = modulus // (100 * numerator)
        count = threshold.bit_length()
        length = 2 * k + 1
        assert 0 < count <= length
        assert 100 * numerator * 2 ** (count - 1) <= modulus
        assert modulus < 100 * numerator * 2 ** count
        # cos(2*pi*x) >= 1-2*pi^2*x^2 >= 499/500 for 0<=x<=1/100,
        # and cos >= -1 for every remaining term.  This is a rational bound.
        lower = Fraction(999 * count - 500 * length, 500 * length)
        assert lower > 0
        print(f"{k:4} {r:19} {count:26} / {length:<5} {lower} ({float(lower):.4f})")


if __name__ == "__main__":
    test_seed_identity()
    test_precision_permutations()
    low_digit_adversaries()
    print("PASS.  Information obstruction only; no claim about cancellation of the actual seeds.")
