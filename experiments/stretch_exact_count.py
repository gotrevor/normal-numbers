"""Probe for the 2026-10-05 stretch lap (CantorExactExponentStretch).

* cantor_ints(b): Cantor numerators P < 3^b (ternary digits 0/2).
* low_residue_count(b, k, q): #{P : P q mod 3^b within 3^k of 0}; Lean bound 2 * 2^k
  (card_lowResidue_le).
* riesz_l1(b): sum_s |prod_j (1 + e(2 s 3^j / 3^b))| / 3^b; ratio -> Lambda = 1.29663 (< 4/3).
* window_hits(b, m, tau): exact number of P with a rational p/q != P/3^b, q in [3^m, 3^(m+1)),
  within q^-tau; compared against the elementary bound 2 * 3^(m+1) * 2^(k+1)... per window.
"""
import math


def cantor_ints(b):
    out = [0]
    for _ in range(b):
        out = [3 * p + d for p in out for d in (0, 2)]
    return sorted(out)


def low_residue_count(b, k, q):
    M = 3 ** b
    return sum(1 for P in cantor_ints(b) if (P * q) % M < 3 ** k or M < (P * q) % M + 3 ** k)


def riesz_l1(b):
    N = 3 ** b
    c = [abs(2 * math.cos(2 * math.pi * t / N)) for t in range(N)]
    tot = 0.0
    for s in range(N):
        p, t = 1.0, s
        for _ in range(b):
            p *= c[(2 * t) % N]
            t = (3 * t) % N
        tot += p
    return tot / N


def window_hits(b, m, tau):
    M = 3 ** b
    hits = 0
    for P in cantor_ints(b):
        found = False
        for q in range(3 ** m, 3 ** (m + 1)):
            bound = M * q ** (1 - tau)
            r = (P * q) % M
            for rr in (r, r - M):
                if rr != 0 and abs(rr) < bound:
                    found = True
            if found:
                break
        hits += found
    return hits


if __name__ == "__main__":
    for b in range(1, 10):
        print("L1", b, riesz_l1(b))
    for (b, m, tau) in [(8, 3, 2.3), (9, 3, 2.6), (10, 4, 2.6), (10, 4, 2.2)]:
        k = b - math.floor((tau - 1) * m)
        print("window", b, m, tau, window_hits(b, m, tau), "of", 2 ** b,
              "elementary bound", 2 * 3 ** m * 2 * 2 ** k, "heuristic", 2 ** b * 3 ** ((2 - tau) * m))
