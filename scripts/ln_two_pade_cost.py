#!/usr/bin/env -S uv run --quiet --offline --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["sympy==1.14.0"]
# ///
"""Bounded exact-cost experiment for logarithmic Pade synthesis.

Frozen grid: n=4,8,16,32; width=n; 0<=m<=4n.  Gate: sum |u_j|5^(-n-j)<1/4.
Use an exact rational dual lower bound first.  Optimize only the remaining
cases, with exact integer lattice reduction and bounded local improvement.
No optimum is claimed for the heuristic lattice stage.
"""
from fractions import Fraction as Q
from math import comb, lcm
from time import monotonic
import argparse
import json
import copy
from sympy import Matrix
from ln_two_route_screen import pade_data, extended_gcd


def log_bracket(terms=512):
    lower = sum(Q(1, k*2**k) for k in range(1, terms+1))
    return lower, lower+Q(1, (terms+1)*2**terms)


def integer_distance_lower(lower, upper):
    k = lower.numerator // lower.denominator
    if k != upper.numerator // upper.denominator:
        return Q(0)
    return min(lower-k, k+1-upper)


def error_ratio_upper(a, b, n, width, lower, upper):
    return max(5**j*max(abs(a[j]*lower-b[j]), abs(a[j]*upper-b[j]))
               for j in range(n, n+width))


def round_down(q, denominator=10**12):
    return Q(q.numerator*denominator // q.denominator, denominator)


def column_reduce(mat, transform, row, anchor, other):
    av, bv = mat[row][anchor], mat[row][other]
    if not bv:
        return
    g, s, t = extended_gcd(av, bv)
    for rows in [mat, transform]:
        for r in rows:
            x, y = r[anchor], r[other]
            r[anchor], r[other] = s*x+t*y, -(bv//g)*x+(av//g)*y


def affine_lattice(a, b, n, width, m):
    aa = [int(v) for v in a[n:n+width]]
    bb = b[n:n+width]
    d = lcm(*(v.denominator for v in bb))
    cc = [int(v*d) for v in bb]
    mat = [aa+[0], cc+[-d]]
    original = [row[:] for row in mat]
    size = width+1
    transform = [[int(i == j) for j in range(size)] for i in range(size)]
    for j in range(1, size):
        column_reduce(mat, transform, 0, 0, j)
    for j in range(2, size):
        column_reduce(mat, transform, 1, 1, j)
    if mat[1][1] < 0:
        for rows in [mat, transform]:
            for row in rows:
                row[1] = -row[1]
    assert Matrix(original)*Matrix(transform) == Matrix(mat)
    assert abs(int(Matrix(transform).det())) == 1
    target = 2**m
    if target % mat[0][0]:
        return None
    t0 = target // mat[0][0]
    if (mat[1][0]*t0) % mat[1][1]:
        return None
    t1 = -mat[1][0]*t0 // mat[1][1]
    particular = [row[0]*t0+row[1]*t1 for row in transform]
    assert [sum(x*y for x, y in zip(row, particular)) for row in original] == [target, 0]
    weights = [5**(width-1-j) for j in range(width)]
    point = [v*w for v, w in zip(particular, weights)]
    basis = [[transform[i][j]*weights[i] for i in range(width)]
             for j in range(2, size)]
    return point, basis, weights


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def gram_schmidt(rows):
    orthogonal, norms = [], []
    for row in rows:
        v = list(map(Q, row))
        for prev, norm in zip(orthogonal, norms):
            c = dot(row, prev)/norm
            v = [x-c*y for x, y in zip(v, prev)]
        orthogonal.append(v)
        norms.append(dot(v, v))
    return orthogonal, norms


def nearest_plane(point, basis):
    ortho, norms = gram_schmidt(basis)
    residual = point[:]
    for row, orth, norm in reversed(list(zip(basis, ortho, norms))):
        k = round(dot(residual, orth)/norm)
        residual = [x-k*y for x, y in zip(residual, row)]
    return residual


def exact_lll(basis, seconds=20, max_steps=10000):
    """Small-dimensional LLL using rational Gram-Schmidt throughout.

    SymPy 1.14's LLL assertion failed on this exact basis.  Keep SymPy only
    for independent integer-matrix checks; do not suppress its assertion.
    """
    rows = [row[:] for row in basis]
    size = len(rows)
    trans = [[int(i == j) for j in range(size)] for i in range(size)]
    start, steps, k = monotonic(), 0, 1
    while k < size:
        steps += 1
        if steps > max_steps or monotonic()-start > seconds:
            raise RuntimeError('exact LLL bounded-work limit reached')
        ortho, norms = gram_schmidt(rows)
        for j in reversed(range(k)):
            q = round(dot(rows[k], ortho[j])/norms[j])
            if q:
                rows[k] = [x-q*y for x, y in zip(rows[k], rows[j])]
                trans[k] = [x-q*y for x, y in zip(trans[k], trans[j])]
                ortho, norms = gram_schmidt(rows)
        mu = dot(rows[k], ortho[k-1])/norms[k-1]
        if norms[k] >= (Q(3, 4)-mu*mu)*norms[k-1]:
            k += 1
        else:
            rows[k], rows[k-1] = rows[k-1], rows[k]
            trans[k], trans[k-1] = trans[k-1], trans[k]
            k = max(1, k-1)
    ortho, norms = gram_schmidt(rows)
    for i in range(size):
        for j in range(i):
            assert abs(dot(rows[i], ortho[j])/norms[j]) <= Q(1, 2)
        if i:
            mu = dot(rows[i], ortho[i-1])/norms[i-1]
            assert norms[i] >= (Q(3, 4)-mu*mu)*norms[i-1]
    assert Matrix(trans)*Matrix(basis) == Matrix(rows)
    assert abs(int(Matrix(trans).det())) == 1
    return rows


def improve_l1(point, basis, passes=20):
    residual = point[:]
    for _ in range(passes):
        changed = False
        for row in basis:
            candidates = {0}
            for x, y in zip(residual, row):
                if y:
                    floor = x // y
                    candidates.update([floor, floor+1])
            old_cost = sum(map(abs, residual))
            k = min(candidates, key=lambda k: (sum(abs(x-k*y) for x, y in zip(residual, row)), abs(k), k))
            if sum(abs(x-k*y) for x, y in zip(residual, row)) < old_cost:
                residual = [x-k*y for x, y in zip(residual, row)]
                changed = True
        if not changed:
            break
    return residual


def optimize(a, b, n, width, m):
    start = monotonic()
    lattice = affine_lattice(a, b, n, width, m)
    if lattice is None:
        return {"status": "algebraically impossible"}
    point, basis, weights = lattice
    rows = exact_lll(basis)
    result = improve_l1(nearest_plane(point, rows), rows)
    # A bounded neighborhood of the nearest-plane point, followed by L1 descent.
    for row in rows:
        for sign in [-1, 1]:
            trial = improve_l1([x+sign*y for x, y in zip(result, row)], rows)
            if sum(map(abs, trial)) < sum(map(abs, result)):
                result = trial
    assert all(x % w == 0 for x, w in zip(result, weights))
    coeffs = [x//w for x, w in zip(result, weights)]
    coefficient = sum(u*a[n+j] for j, u in enumerate(coeffs))
    constant = sum(u*b[n+j] for j, u in enumerate(coeffs))
    budget = sum(Q(abs(u), 5**(n+j)) for j, u in enumerate(coeffs))
    assert coefficient == 2**m and constant.denominator == 1
    return {"status": "gate passed" if budget < Q(1, 4) else "candidate fails gate",
            "coefficients": coeffs, "constant": str(constant),
            "budget": str(budget), "budget_float": float(budget),
            "elapsed_seconds": monotonic()-start}


def controls(a, b):
    yes = optimize(a, b, 1, 2, 4)
    assert yes['status'] == 'gate passed' and Q(yes['budget']) == Q(6, 25)
    no = optimize(a, b, 5, 2, 4)
    assert no['status'] == 'algebraically impossible'
    lo, hi = log_bracket()
    ratio = error_ratio_upper(a, b, 1, 2, lo, hi)
    dual = integer_distance_lower(16*lo, 16*hi)/ratio
    assert dual <= Q(6, 25) < Q(1, 4)
    return {"positive": yes, "negative": no, "positive_dual_bound": str(round_down(dual))}


def verify_report(report):
    """Recompute with closed binomial formulas, independent of the recurrence.

    This checks the delivered certificates, not the LLL implementation's
    claim to have found them.  Stored lower bounds are rationals rounded down.
    """
    a = [sum(comb(n, k)*comb(n+k, k) for k in range(n+1)) for n in range(65)]
    b = [2*sum((Q(a[k-1]*a[n-k], k) for k in range(1, n+1)), Q(0))
         for n in range(65)]
    lo, hi = log_bracket(report['log_bracket_terms'])
    assert Q(report['log_lower']) == lo and Q(report['log_upper']) == hi
    expected = {(n, m) for n in [4, 8, 16, 32] for m in range(4*n+1)}
    assert len(report['cases']) == len(expected)
    assert {(r['n'], r['m']) for r in report['cases']} == expected
    for row in report['cases']:
        n, width, m = row['n'], row['width'], row['m']
        assert width == n
        ratio = error_ratio_upper(a, b, n, width, lo, hi)
        bound = integer_distance_lower(2**m*lo, 2**m*hi)/ratio
        assert Q(row['dual_lower_bound']) <= bound
        if row['status'] == 'excluded by exact dual bound':
            assert Q(row['dual_lower_bound']) >= Q(1, 4)
        else:
            u = row['coefficients']
            assert len(u) == width
            assert sum(v*a[n+j] for j, v in enumerate(u)) == 2**m
            assert sum(v*b[n+j] for j, v in enumerate(u)) == Q(row['constant'])
            assert Q(row['constant']).denominator == 1
            budget = sum(Q(abs(v), 5**(n+j)) for j, v in enumerate(u))
            assert budget == Q(row['budget']) and bound <= budget
            assert (row['status'] == 'gate passed') == (budget < Q(1, 4))
    for summary in report['summary']:
        n = summary['n']
        ratio = error_ratio_upper(a, b, n, n, lo, hi)
        best, m = min((integer_distance_lower(2**m*lo, 2**m*hi)/ratio, m)
                      for m in range(4*n+1))
        assert Q(summary['minimum_dual_bound']) <= best
        assert summary['minimum_dual_exponent'] == m


def run(control_only=False):
    a, b = pade_data(65)
    tested = controls(a, b)
    if control_only:
        return {"controls": tested}
    lo, hi = log_bracket()
    rows, summary = [], []
    for n in [4, 8, 16, 32]:
        ratio = error_ratio_upper(a, b, n, n, lo, hi)
        lower_bounds, optimized = [], []
        for m in range(4*n+1):
            lower_bound = integer_distance_lower(2**m*lo, 2**m*hi)/ratio
            lower_bounds.append((lower_bound, m))
            row = {"n": n, "width": n, "m": m,
                   "dual_lower_bound": str(round_down(lower_bound))}
            if lower_bound >= Q(1, 4):
                row['status'] = 'excluded by exact dual bound'
            else:
                row.update(optimize(a, b, n, n, m))
                optimized.append(m)
            rows.append(row)
        best_bound, best_m = min(lower_bounds)
        summary.append({"n": n, "width": n, "exponents": [0, 4*n],
                        "minimum_dual_bound": str(round_down(best_bound)),
                        "minimum_dual_bound_float": float(best_bound),
                        "minimum_dual_exponent": best_m, "optimized_exponents": optimized})
    report = {"gate": "weighted L1 budget < 1/4", "log_bracket_terms": 512,
            "log_lower": str(lo), "log_upper": str(hi), "controls": tested,
            "summary": summary, "cases": rows,
            "bound_storage": "rational lower bounds rounded down to multiples of 10^-12",
            "scope": "exact finite lower bounds and witnesses; no all-n or all-exponent claim"}
    verify_report(report)
    broken = copy.deepcopy(report)
    hit = next(row for row in broken['cases'] if row['status'] == 'gate passed')
    hit['coefficients'][0] += 1
    try:
        verify_report(broken)
    except AssertionError:
        pass
    else:
        raise AssertionError('mutated witness escaped the independent verifier')
    report['independent_verifier'] = 'binomial formulas pass; mutated witness rejected'
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--controls', action='store_true')
    args = parser.parse_args()
    print(json.dumps(run(args.controls), indent=2))
