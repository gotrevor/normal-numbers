#!/usr/bin/env -S uv run --quiet python3
"""Exact controls for the ln(2) route screen; no digit-frequency census.

Run must certify every rejected Pade window by an odd-prime congruence,
and every feasible control by actual integer coefficients.  Jet identities
are tested as finite rational telescoping identities, not infinite sums.
"""
from fractions import Fraction as Q
from math import factorial, gcd, lcm, prod
import json


def beta(m, n):
    return Q(factorial(m), prod(range(n, n+m+1)))


def potential(m, n):
    return sum((-1)**j * beta(j, n) for j in range(m))


def clone(m, n):
    return 2*potential(m, n)-potential(m, n+1)


def jet_controls():
    checks = 0
    for m in range(1, 11):
        target = sum(Q((-1)**j, j+1) for j in range(m))
        assert potential(m, 1) == target
        for n in range(1, 25):
            r = clone(m, n)
            assert r == Q(1, n)-(-1)**m*beta(m, n)
            assert r > 0
            assert abs(r-Q(1, n)) <= Q(factorial(m), n**(m+1))
            finite = sum(clone(m, k)/2**k for k in range(1, n+1))
            assert finite == target-potential(m, n+1)/2**n
            checks += 1
    # Red control: the wrong coboundary coefficient must break the identity.
    assert 3*potential(2, 3)-potential(2, 4) != clone(2, 3)
    return {"orders": [1, 10], "positions": [1, 24], "finite_checks": checks}


def pade_data(end):
    a, b = [Q(1), Q(3)], [Q(0), Q(2)]
    for n in range(1, end):
        a.append((3*(2*n+1)*a[n]-n*a[n-1])/(n+1))
        b.append((3*(2*n+1)*b[n]-n*b[n-1])/(n+1))
    for n in range(end):
        assert a[n].denominator == 1
        assert a[n]*b[n+1]-a[n+1]*b[n] == Q(2, n+1)
    return a, b


def extended_gcd(a, b):
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r-q*r
        old_s, s = s, old_s-q*s
        old_t, t = t, old_t-q*t
    if old_r < 0:
        return -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def bezout(values):
    g, coeffs = 0, []
    for value in values:
        g, s, t = extended_gcd(g, value)
        coeffs = [s*c for c in coeffs]+[t]
    assert sum(c*v for c, v in zip(coeffs, values)) == g
    return g, coeffs


def first_odd_prime(g):
    while g % 2 == 0:
        g //= 2
    if g == 1:
        return None
    p = 3
    while p*p <= g:
        if g % p == 0:
            return p
        p += 2
    return g


def window(a, b, n, width, keep_witness=False):
    aa = [int(v) for v in a[n:n+width]]
    bb = b[n:n+width]
    d = lcm(*(v.denominator for v in bb))
    cc = [int(d*v) for v in bb]
    h, lam = bezout(cc+[d])
    assert h == 1  # common denominator is minimal
    a0 = sum(u*v for u, v in zip(lam, aa))
    xx = [v-c*a0 for v, c in zip(aa, cc)]+[-d*a0]
    g, mu = bezout(xx)
    determinants = [aa[i]*cc[j]-aa[j]*cc[i]
                    for i in range(width) for j in range(i+1, width)]
    assert g == gcd(*(determinants+[v*d for v in aa]))
    p = first_odd_prime(g)
    row = {"n": n, "width": width, "coefficient_generator": str(g)}
    if p:
        assert d % p == 0
        j = next(j for j in range(width) if cc[j] % p)
        c = aa[j]*pow(cc[j], -1, p) % p
        assert all((av-c*cv) % p == 0 for av, cv in zip(aa, cc))
        row.update({"status": "obstructed", "prime": p, "slope": c,
                    "common_denominator": str(d)})
    else:
        lam_weight = sum(u*c for u, c in zip(mu, cc+[d]))
        u = [v-lam_weight*l for v, l in zip(mu, lam)]
        assert sum(v*av for v, av in zip(u, aa)) == g
        z = sum(v*bv for v, bv in zip(u, bb))
        assert z.denominator == 1
        assert sum(v*cv for v, cv in zip(u, cc))+u[-1]*d == 0
        row.update({"status": "feasible", "dyadic_exponent": g.bit_length()-1,
                    "max_coefficient_bits": max(abs(v).bit_length() for v in u[:-1])})
        if keep_witness:
            budget = sum(Q(abs(v), 5**(n+j)) for j, v in enumerate(u[:-1]))
            assert budget > 1
            row.update({"coefficients": [str(v) for v in u[:-1]], "constant": str(z),
                        "weighted_l1_upper_bound": str(budget),
                        "small_error_gate": "fails for this witness; no optimality claim"})
    return row


def run():
    jets = jet_controls()
    a, b = pade_data(165)
    grid = [window(a, b, n, width) for width in [2, 3, 5, 10]
            for n in range(1, 80)]
    feasible = {str(width): [r['n'] for r in grid
                if r['width'] == width and r['status'] == 'feasible']
                for width in [2, 3, 5, 10]}
    assert feasible == {"2": [1, 2], "3": [1, 2, 4],
                        "5": [1, 2, 3, 4, 6], "10": list(range(1, 11))}
    broad = [window(a, b, n, n, True) for n in [4, 8, 16, 32]]
    assert all(r['status'] == 'feasible' for r in broad)
    assert a[5] == 1683 and b[5] == Q(34997, 30)
    assert a[6] == 8989 and b[6] == Q(62307, 10)
    assert -4*a[1]+a[2] == -4*b[1]+b[2] == 1
    return {"jet_controls": jets, "pade_wronskians_checked": 165,
            "feasible_start_indices": feasible,
            "short_windows": grid, "broad_window_witnesses": broad,
            "scope": "finite exact certificates; feasibility says nothing about small error or digit visits"}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
