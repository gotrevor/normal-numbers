#!/usr/bin/env -S uv run --quiet python3
"""Exact preflight of the binary/ternary quadratic-norm proposal.

This tests finite rational approximants and denominator cost, not pi's digits.
The coefficient-5 control deliberately breaks the coefficient-6 identity.
"""
from fractions import Fraction as Q
import json


def binary(n):
    return sum((Q(4, 8*k+1)-Q(2, 8*k+4)-Q(1, 8*k+5)-Q(1, 8*k+6))
               / 16**k for k in range(n))


def ternary(m, coefficient=6):
    return coefficient * sum((Q(1, 4*k+1)-Q(1, 3*(4*k+3)))
                             / 9**k for k in range(m))


def norm_data(a, b):
    raw = 3*a*a-b*b
    cleared = 3*(a.numerator*b.denominator)**2 - (b.numerator*a.denominator)**2
    denominator = (a.denominator*b.denominator)**2
    assert Q(cleared, denominator) == raw
    return raw, cleared, denominator


def sample(n, m):
    a, b = binary(n), ternary(m)
    raw, cleared, denominator = norm_data(a, b)
    assert 0 < abs(raw) < 1
    assert abs(cleared) > 1
    assert abs(raw.numerator) > 1
    broken = 3*a*a-ternary(m, 5)**2
    assert broken > 8
    return {"n": n, "m": m, "raw_norm": str(raw),
            "raw_norm_float": float(raw),
            "cleared_integer_bits": abs(cleared).bit_length(),
            "denominator_bits": denominator.bit_length(),
            "reduced_numerator_bits": abs(raw.numerator).bit_length(),
            "reduced_denominator_bits": raw.denominator.bit_length(),
            "wrong_coefficient_control": float(broken)}


def pell_control(k):
    p, q = 1, 0
    for _ in range(k):
        p, q = 2*p+3*q, p+2*q
    assert p*p-3*q*q == 1
    raw, cleared, denominator = norm_data(Q(q, p), Q(1))
    assert raw == -Q(1, p*p)
    assert raw.numerator == cleared == -1
    return {"k": k, "cleared_norm": cleared, "raw_norm": str(raw),
            "denominator_bits": denominator.bit_length()}


if __name__ == '__main__':
    rows = [sample(n, m) for n, m in [(2, 3), (4, 5), (8, 10), (16, 20), (32, 40)]]
    assert all(abs(Q(b['raw_norm'])) < abs(Q(a['raw_norm']))
               for a, b in zip(rows, rows[1:]))
    print(json.dumps({"status": "finite controls pass; raw norm shrinks but cleared integer grows",
                      "samples": rows,
                      "pell_unit_controls": [pell_control(k) for k in [1, 2, 4, 8, 16, 32]]},
                     indent=2))
