"""Probe for the 2026-10-06 stretch lap: Farey disjointness plus the per-r count.

Run-entering window m for the run starting at b (CantorExactExponentStretch.RunEnteringCountAt):
P in C_b (ternary digits 0/2), q in [3^m, 3^(m+1)), r != 0, |r| < 3^b q^(1-tau), P q = r mod 3^b.

* farey_set(b, m): P with a rational p/q != P/3^b, q < 3^(m+1), |P/3^b - p/q| < 3^-b.
  Lean claim: at most 2^(2m+3) such P (two of them in one depth-(2m+3) cylinder would need two
  distinct Farey fractions closer than 1/(q q')).  Contains the window set once tau m >= b.
* per_r_pairs(b, m, tau): the map P -> (r, P mod 3^(m+1)) on witnesses with 3 not dividing P q is
  injective (the low digits and r fix q, then P), so the window set has about 2R 2^(m+1)
  elements, R = 3^(b - (tau-1) m).
* threshold: min(4^m, R 2^m) < 2^b for every m iff tau > 3 - log_3 2 = 2.3691.

Usage: stretch_farey_perr.py            (table)
       stretch_farey_perr.py test       (pytest file beside it)
"""
import math
import subprocess
import sys
from pathlib import Path


def cantor_ints(b):
    out = [0]
    for _ in range(b):
        out = [3 * p + d for p in out for d in (0, 2)]
    return sorted(out)


def is_cantor(P, b):
    for _ in range(b):
        if P % 3 == 1:
            return False
        P //= 3
    return P == 0


def solutions(q, r, b):
    """All P mod 3^b with P q = r mod 3^b."""
    M = 3 ** b
    v = 0
    qq = q
    while qq % 3 == 0 and v < b:
        qq //= 3
        v += 1
    if r % (3 ** v):
        return []
    Mv = 3 ** (b - v)
    P0 = (r // 3 ** v) * pow(qq, -1, Mv) % Mv
    return [P0 + t * Mv for t in range(3 ** v)]


def window_set(b, m, tau):
    """Exact window set: P in C_b with a witness (q, r)."""
    M = 3 ** b
    out = set()
    for q in range(3 ** m, 3 ** (m + 1)):
        bound = M * q ** (1 - tau)
        rmax = math.ceil(bound) - 1
        for r in range(-rmax, rmax + 1):
            if r == 0 or abs(r) >= bound:
                continue
            for P in solutions(q, r % M, b):
                if is_cantor(P, b):
                    out.add(P)
    return out


def farey_set(b, m):
    """P in C_b within 3^-b of some p/q != P/3^b with q < 3^(m+1): |P q - p 3^b| < q, nonzero."""
    M = 3 ** b
    out = set()
    for q in range(1, 3 ** (m + 1)):
        for r in range(-(q - 1), q):
            if r == 0:
                continue
            for P in solutions(q, r % M, b):
                if is_cantor(P, b):
                    out.add(P)
    return out


def per_r_pairs(b, m, tau):
    """Witness pairs (r, P mod 3^(m+1)) for P q = r with 3 not dividing P q; returns (pairs, injective)."""
    M = 3 ** b
    seen = {}
    injective = True
    for q in range(3 ** m, 3 ** (m + 1)):
        if q % 3 == 0:
            continue
        bound = M * q ** (1 - tau)
        rmax = math.ceil(bound) - 1
        for r in range(-rmax, rmax + 1):
            if r == 0 or abs(r) >= bound or r % 3 == 0:
                continue
            for P in solutions(q, r % M, b):
                if is_cantor(P, b):
                    key = (r, P % 3 ** (m + 1))
                    if key in seen and seen[key] != P:
                        injective = False
                    seen[key] = P
    return seen, injective


def threshold():
    return 3 - math.log(2, 3)


def worst_exponent(tau):
    """max over u = m/b of log_3(min(4^m, R 2^m) / 2^b) / b, R = 3^(b - (tau-1) m)."""
    d = math.log(2, 3)
    best = -1e9
    for i in range(1, 1000):
        u = i / 1000
        val = min(2 * d * u, 1 - (tau - 1) * u + d * u) - d
        best = max(best, val)
    return best


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        here = Path(__file__).resolve().parent
        sys.exit(subprocess.call(["python3", "-m", "pytest", "-q", str(here / "test_stretch_farey_perr.py")]))
    print("threshold 3 - log_3 2 =", threshold())
    for tau in (2.2, 2.3, 2.369, 2.4, 2.585):
        print(f"tau {tau}: worst log_3(min bound / 2^b)/b = {worst_exponent(tau):+.4f}")
    print(" b  m  tau   |window|  farey|S|  2^(2m+3)  2R2^(m+1)  heuristic 2^b 3^-(tau-2)m")
    for (b, m, tau) in [(10, 4, 2.3), (10, 5, 2.3), (12, 5, 2.3), (12, 6, 2.3), (12, 7, 2.3),
                        (12, 6, 2.2), (12, 7, 2.2), (12, 8, 2.2)]:
        W = window_set(b, m, tau)
        F = farey_set(b, m) if 2 * m + 3 <= b + 6 else set()
        R = 3 ** (b - (tau - 1) * m)
        print(f"{b:2d} {m:2d} {tau:4.2f} {len(W):8d} {len(F):8d} {2 ** (2 * m + 3):9d} "
              f"{2 * R * 2 ** (m + 1):10.0f} {2 ** b * 3 ** (-(tau - 2) * m):12.1f}")
