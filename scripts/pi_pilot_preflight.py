#!/usr/bin/env -S uv run --quiet python3
"""Exact cheap controls for the three pilot targets, before spending a worker lap.

These finite checks validate the proposed algebra and seed formulas.  The Lean
pilots must supply the quantified proofs; passing here is not a substitute.
"""
from fractions import Fraction as Q


def evaluate(coefficients, x):
    return sum((a * x ** j for j, a in enumerate(coefficients)), Q(0))


def residual(coefficients):
    return [a + ((j + 2) * (j + 1) * coefficients[j + 2]
                 if j + 2 < len(coefficients) else 0)
            for j, a in enumerate(coefficients)]


def oscillator():
    for degree in range(4):
        p = [Q(0)] * degree + [Q(1)]
        r = residual(p)
        assert evaluate(p, 0) + evaluate(p, 3) == evaluate(r, 1) + evaluate(r, 2)
    p = [Q(65, 4), Q(-32), Q(-8), Q(8), Q(-1)]
    assert residual(p) == [Q(1, 4), Q(16), Q(-20), Q(8), Q(-1)]
    assert evaluate(p, 0) + evaluate(p, 3) == Q(-1, 2)
    # Known-answer degree boundary: the cubic identity fails on this quartic.
    r = residual(p)
    assert evaluate(p, 0) + evaluate(p, 3) != evaluate(r, 1) + evaluate(r, 2)
    for j in range(17):
        x = Q(j, 4)
        assert evaluate(r, x) == x * (4 - x) * (x - 2) ** 2 + Q(1, 4) > 0


def radical():
    for b in [Q(0), Q(1, 2), Q(1), Q(3, 2), Q(2)]:
        a = b * b - 2
        assert (2 - b) * (2 + b) == 2 - a
    # The tempting strict gain fails already at b=1, a=-1.
    assert not (2 - 1) * (2 + 1) <= Q(9, 10) * (2 - (-1))


def spigot():
    for length in range(1, 21):
        p, r, q = 1, 4 ** (length + 1), 3 * 4 ** (length + 1)
        output = []
        for _ in range(2 * length):
            low, high = 2 * (2 * p + r), 2 * (4 * p + r)
            d = low // q
            assert d in (0, 1) and high < (d + 1) * q
            output.append(d)
            p, r = 2 * p, 2 * r - d * q
        assert output == [0, 1] * length
        assert p == 4 ** length and r == 4 ** (length + 1)
        assert [0, 0] not in [output[j:j + 2] for j in range(len(output) - 1)]


if __name__ == '__main__':
    oscillator()
    radical()
    spigot()
    print('PASS: cubic identity, strict quartic control, radical compensation, positive-width alternating seeds')
