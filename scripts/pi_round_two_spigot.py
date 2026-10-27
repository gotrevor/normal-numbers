#!/usr/bin/env -S uv run --quiet python3
"""Exact finite probe, not a test of a uniform invariant or a disjunctivity proof.

Budget calibration: test C=4 through word length 8, using at most 4096 output bits.
Controls: an independent alternating Machin enclosure for the first 256 bits;
the same interval-emission logic on the rational fixed point 10/3 (missing 00).
Only integer and Fraction arithmetic are used.  No dependency downloads.
"""
from fractions import Fraction
from math import gcd
import json


def run(bits, rational=False):
    n, p, r, q = 0, 1, -3, 1
    output, times = [], []
    for step in range(1, 12 * bits + 100):
        low, high = 2 * (2 * p + r), 2 * (4 * p + r)
        d = low // q
        if 0 <= d < 2 and high < (d + 1) * q:
            output.append(str(d))
            times.append(step)
            p, r = 2 * p, 2 * r - d * q
            if len(output) == bits:
                return ''.join(output), times
        elif rational:
            # z -> 5/3 + z/2, fixed point 10/3, invariant tail interval [2,4].
            p, r, q = 3 * p, 10 * p + 6 * r, 6 * q
        else:
            p, r, q = (n + 1) * p, (2 * p + r) * (2 * n + 3), (2 * n + 3) * q
            n += 1
        g = gcd(gcd(p, r), q)
        p, r, q = p // g, r // g, q // g
    raise AssertionError('read/emit probe budget exhausted')


def atan_interval(q, terms=100):
    s = sum((Fraction((-1) ** n, (2 * n + 1) * q ** (2 * n + 1))
             for n in range(terms)), Fraction(0))
    nxt = Fraction((-1) ** terms, (2 * terms + 1) * q ** (2 * terms + 1))
    return min(s, s + nxt), max(s, s + nxt)


def main():
    stream, times = run(4096)
    a, b = atan_interval(5)
    c, d = atan_interval(239)
    lo, hi = 16 * a - 4 * d - 3, 16 * b - 4 * c - 3
    lower, upper = (lo * 2 ** 256).__floor__(), (hi * 2 ** 256).__floor__()
    assert lower == upper == int(stream[:256], 2)
    control, _ = run(512, rational=True)
    assert control == '01' * 256
    assert '00' not in control and '11' not in control
    rows = []
    for k in range(1, 9):
        first = {}
        for end in range(k, len(stream) + 1):
            first.setdefault(stream[end - k:end], times[end - 1])
        complete = len(first) == 2 ** k
        budget = 4 * (k + 1) * 2 ** k
        rows.append(dict(k=k, seen=len(first), expected=2 ** k,
                         complete=complete, latest_first_hit_step=max(first.values()),
                         candidate_budget_C4=budget,
                         passes_C4=complete and max(first.values()) <= budget))
    print(json.dumps(dict(bits=4096, machine_steps=times[-1],
                         independent_machin_bits_checked=256,
                         rational_control='512 alternating bits; 00 and 11 absent',
                         note='Finite calibration only; no invariant was synthesized.',
                         rows=rows), indent=2))


if __name__ == '__main__':
    main()
