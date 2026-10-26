#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Exact rational diagnostics, not a proof of an infinite 2-adic identity."""

import json
from fractions import Fraction as Q


def kick(n: int, first_coefficient: int = 4) -> Q:
    return (Q(first_coefficient, 8*n+1) - Q(2, 8*n+4)
            - Q(1, 8*n+5) - Q(1, 8*n+6))


def v2(q: Q) -> int:
    if q == 0:
        raise ValueError("zero has infinite valuation")
    def integer_v2(n: int) -> int:
        n = abs(n)
        return (n & -n).bit_length() - 1
    return integer_v2(q.numerator) - integer_v2(q.denominator)


def run(count: int = 256) -> dict:
    # Known-answer checks before measuring the BBP cancellation.
    assert v2(Q(8, 3)) == 3
    assert v2(Q(3, 8)) == -3
    assert kick(-1) == Q(16, 21)
    # F(n)=1: coboundary=15/16, forward sum tends to 1 in R;
    # backward partial sum is 16^N-1, tending to -1 in Q_2.
    control = Q(0)
    for n in range(1, 9):
        control += 16**n * Q(15, 16)
        assert control == 16**n - 1
    partial = Q(0)
    changed = Q(0)
    rows = []
    for n in range(1, count+1):
        partial += 16**n * kick(-n)
        changed += 16**n * kick(-n, 5)
        # Empirical stronger pattern; not asserted as an infinite theorem.
        expected = 4*n + 4 + v2(Q(n))
        rows.append({"N": n, "bbp_v2": v2(partial),
                     "changed_coefficient_v2": v2(changed),
                     "stronger_pattern": v2(partial) == expected})
    return {
        "arithmetic": "exact fractions; no floating point",
        "cutoffs_checked": count,
        "known_answer_controls": "passed",
        "bbp_v2_at_least_4N_plus_4": all(r["bbp_v2"] >= 4*r["N"]+4 for r in rows),
        "stronger_pattern_all": all(r["stronger_pattern"] for r in rows),
        "changed_coefficient_all_v2_equal_4": all(r["changed_coefficient_v2"] == 4 for r in rows),
        "rows": rows,
        "limitation": "Finite exact evidence does not prove convergence to zero or disjunctivity.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
