#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Exact finite checks of the disk floor-error identity and its scale."""

import json
from fractions import Fraction as Q
from math import isqrt


def chi(d: int) -> int:
    return 1 if d % 4 == 1 else -1 if d % 4 == 3 else 0


def disk(radius: int) -> int:
    return 1 + 4*radius + 4*sum(
        isqrt(radius*radius-j*j) for j in range(1, radius+1))


def error(size: int, cutoff: int, character=True) -> Q:
    return sum(((chi(d) if character else 1) *
                (Q(size, d)-size//d) for d in range(1, cutoff+1)), Q(0))


def run() -> dict:
    assert [disk(r) for r in (1, 2, 4)] == [5, 13, 49]
    assert error(16, 1) == 0
    assert error(16, 3) == -Q(1, 3)
    records = []
    for n in range(4):
        radius, size, modulus = 4**n, 16**n, 8**n
        count = disk(radius)
        divisor_sum = sum(chi(d)*(size//d) for d in range(1, size+1))
        assert count == 1+4*divisor_sum
        total = error(size, size)
        small = error(size, radius)
        tail = total-small
        perimeter_bound = Q(5*radius+5, 4)
        assert abs(total) <= perimeter_bound
        assert abs(4*tail/modulus) <= Q(14, 2**n)
        control = error(size, size, character=False)
        records.append({
            "n": n, "radius": radius, "terms": size,
            "character_total_perimeter_bound_passes": True,
            "character_tail_scaled_bound_passes": True,
            "unweighted_control_exceeds_perimeter_bound": control > perimeter_bound,
            "total_approx": float(total), "tail_approx": float(tail),
            "unweighted_control_approx": float(control),
            "perimeter_bound": str(perimeter_bound),
        })
    assert records[-1]["unweighted_control_exceeds_perimeter_bound"]
    return {"arithmetic": "exact rational comparisons; floats are display only",
            "known_answer_controls": "passed",
            "records": records,
            "scope": "Finite checks only. The all-index theorem has explicit divisor and Leibniz inputs."}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
