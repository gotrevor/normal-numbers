#!/usr/bin/env -S uv run --quiet python3
"""Find exact positive point-evaluation controls for oscillator certificates.

Target: 10*(P(0)+P(3)) + P(0)+P(4), for degree(P)<=4.
Write Q=P''+P; invert on polynomials via P=Q-Q''+Q''''.
The resulting moments are [22,34,62,130,322].  Search half-integer nodes
in [0,4].  A positive quadrature rules out a quartic certificate excluding
both integers 3 and 4, without a floating-point SDP or a pi digit oracle.
"""
from fractions import Fraction as F
from itertools import combinations
import json


def solve(matrix, rhs):
    a = [list(row) + [value] for row, value in zip(matrix, rhs)]
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return None
        a[j], a[pivot] = a[pivot], a[j]
        p = a[j][j]
        a[j] = [v / p for v in a[j]]
        for i in range(len(a)):
            if i != j:
                f = a[i][j]
                a[i] = [x - f * y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def main():
    moments = list(map(F, [22, 34, 62, 130, 322]))
    # Known-answer solver control, with a deliberately negative weight.
    assert solve([[F(1), F(1)], [F(0), F(1)]], [F(1), F(-1)]) == [F(2), F(-1)]
    for nodes in combinations([F(i, 2) for i in range(9)], 5):
        weights = solve([[x ** j for x in nodes] for j in range(5)], moments)
        if weights is not None and all(w >= 0 for w in weights):
            assert all(sum(w * x ** j for x, w in zip(nodes, weights)) == moments[j]
                       for j in range(5))
            # Independently check the oscillator functional on P=X^j.
            for j in range(5):
                left = 11 * (1 if j == 0 else 0) + 10 * 3 ** j + 4 ** j
                right = sum(w * (x ** j + (j * (j - 1) * x ** (j - 2) if j >= 2 else 0))
                            for x, w in zip(nodes, weights))
                assert left == right
            print(json.dumps(dict(nodes=list(map(str, nodes)), weights=list(map(str, weights)),
                                  moments=list(map(str, moments)), degree=4), indent=2))
            return
    raise AssertionError('No positive rule on the tested grid; not a nonexistence proof')


if __name__ == '__main__':
    main()
