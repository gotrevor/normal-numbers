#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Do the fresh primes cancel?  The instrument behind quantitative C′ (2026-09-30).

Quantitative C′ (docs/CPRIME-QUANTITATIVE-2026-09-30.md) bounds the transfer term by the
triangle inequality (2.1):

    |W - W_y| <= B := sum_j a_j [2 S_P(y_j, N) + J/N],   a_j = |e(h/4^j) - 1|,

so a prime set with fresh mass rho > 0 keeps a defect linear in rho.  This probe measures, on
residue-class and randomly thinned prime sets, how much of B the true difference uses:

    W    = (1/N) sum_{n<N} prod_{j=1..J} z_j^{omega_P(n+j)},          z_j = e(h/4^j)
    W_y  = the same with only the primes p <= y_j of P counted at site j  (frozen part)
    W_1  = the same with the primes p <= max(y_j, sqrt N) counted         (adds band F1)
    M    = (1/N) sum_n |full product - frozen product|                    (pointwise L1)

Reported: A = |W - W_y| against M and B (cancellation in the average, and slack in the
hit count), the RELATIVE defect A/|W_y| (the fable verdict of 2026-09-19 says fresh primes
rescale the frozen mean by an N-independent Dickman-type factor rather than adding noise, in
which case A/|W_y| stays bounded while A -> 0), and the split A1 = |W_1 - W_y| (fresh band
(y_j, sqrt N]) versus A2 = |W - W_1| (fresh band (sqrt N, N]).

Order split: W - W_y = T1 + T2 exactly, where T1 = mean of frozen * sum_j (z_j^fresh_j - 1)
keeps every n whose fresh primes sit at ONE site, and T2 collects n with fresh primes at two or
more sites (a prime-pair configuration p | n+j, p' | n+j', j != j').  If T2 = O(rho^2) the
parity-type wall enters only at second order in the fresh mass.

Cutoffs: y_j = N^(a 2^-j) with a = --a (default 1, so y_1 = sqrt N).  The paper's a = u^-2 with
u >= 66 is numerically degenerate (y_1 ~ 1 at N = 2^24); this probe measures the mechanism at
reachable scales, not the paper's constants.  J = floor(log2 log2 N) + 1 (the repo's windowJ).

    experiments/cprime_fresh_cancellation.py [--logN 20 22 24] [--h 1 3 5] [--a 1.0]
Tests: experiments/test_cprime_fresh_cancellation.py
"""
import argparse
import math
import sys

import numpy as np


def primes_upto(m):
    s = np.ones(m + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(m ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return np.nonzero(s)[0]


def window_J(N):
    """The repo's windowJ: floor(log2 log2 N) + 1."""
    l2 = N.bit_length() - 1
    return (l2.bit_length() - 1) + 1


def cutoffs(N, J, a):
    return [int(math.floor(N ** (a * 2.0 ** (-j)))) for j in range(1, J + 1)]


def band_counts(L, ps, edges):
    """counts[b][n] = #{p in ps : p | n, edges[b-1] < p <= edges[b]} for n <= L,
    with edges[-1] = 0 implicit and a final band above edges[-1].  int16 per band."""
    edges = sorted(set(edges))
    nb = len(edges) + 1
    out = [np.zeros(L + 1, dtype=np.int16) for _ in range(nb)]
    band = np.searchsorted(np.array(edges), ps, side="left")  # p <= edges[b] -> b
    for p, b in zip(ps.tolist(), band.tolist()):
        out[b][p::p] += 1
    return edges, out


def omega_le(edges, out, c):
    """#{p in P, p | n, p <= c} as an array, c must be one of the edges."""
    k = edges.index(c)
    acc = out[0].copy()
    for b in range(1, k + 1):
        acc += out[b]
    return acc


def measure(N, ps, hs, a=1.0):
    """All quantities for one prime set (sorted array ps of primes) and one N, for each h in hs."""
    J = window_J(N)
    ys = cutoffs(N, J, a)
    r = math.isqrt(N)
    mids = [max(y, r) for y in ys]
    L = N + J
    edges, out = band_counts(L, ps, ys + mids + [L])
    full_cnt = omega_le(edges, out, L)
    frozen = [omega_le(edges, out, y) for y in ys]
    mid = [omega_le(edges, out, c) for c in mids]
    psN = ps[ps <= N]
    fresh = [float(np.sum(1.0 / psN[psN > y])) for y in ys]
    rho = float(np.sum(1.0 / psN[psN > r]))
    kmax = int(full_cnt.max()) + 1
    rows = []
    for h in hs:
        Wf = np.ones(N, dtype=np.complex128)
        Wy = np.ones(N, dtype=np.complex128)
        W1 = np.ones(N, dtype=np.complex128)
        S1 = np.zeros(N, dtype=np.complex128)  # sum_j (z_j^fresh_j(n+j) - 1)
        B = 0.0
        for j in range(1, J + 1):
            z = np.exp(2j * math.pi * h / 4.0 ** j)
            tab = z ** np.arange(kmax)
            Wf *= tab[full_cnt[j:j + N]]
            Wy *= tab[frozen[j - 1][j:j + N]]
            W1 *= tab[mid[j - 1][j:j + N]]
            S1 += tab[full_cnt[j:j + N] - frozen[j - 1][j:j + N]] - 1
            B += abs(z - 1) * (2 * fresh[j - 1] + J / N)
        W, Wyv, W1v = Wf.mean(), Wy.mean(), W1.mean()
        M = float(np.abs(Wf - Wy).mean())
        A = abs(W - Wyv)
        T1 = (Wy * S1).mean()
        T2 = W - Wyv - T1
        rows.append(dict(N=N, J=J, h=h, rho=rho, W=abs(W), Wy=abs(Wyv), A=A, M=M, B=B,
                         T1=abs(T1), T2=abs(T2), T2_over_rho2=abs(T2) / rho ** 2 if rho else float("nan"),
                         A1=abs(W1v - Wyv), A2=abs(W - W1v),
                         A_over_M=A / M if M else float("nan"),
                         A_over_Wy=A / abs(Wyv) if abs(Wyv) else float("inf")))
    return rows


def thinned(ps, theta):
    """Deterministic pseudo-random thinning: keep p iff frac(p * golden) < theta."""
    keep = ((ps.astype(np.float64) * 0.6180339887498949) % 1.0) < theta
    return ps[keep]


def prime_sets(ps):
    sets = [("all primes", ps)]
    for q in (3, 5, 7, 11, 13, 23, 31, 61):
        sets.append((f"p = 1 mod {q}", ps[ps % q == 1]))
    sets.append(("p = 2 mod 31", ps[ps % 31 == 2]))
    for theta in (0.5, 0.25, 0.125, 0.0625, 0.03125):
        sets.append((f"thin {theta:g}", thinned(ps, theta)))
    return sets


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--logN", type=int, nargs="+", default=[20, 22, 24])
    ap.add_argument("--h", type=int, nargs="+", default=[1, 3, 5])
    ap.add_argument("--a", type=float, default=1.0)
    args = ap.parse_args(argv)
    for lN in args.logN:
        N = 1 << lN
        ps = primes_upto(N + 64)
        print(f"\n## N = 2^{lN}, J = {window_J(N)}, y_j = N^({args.a:g}*2^-j)")
        print("| set | h | rho | abs W_y | abs W | A | M | B | A/M | A/abs W_y | A1 | A2 | T1 | T2 | T2/rho^2 |")
        print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
        for name, P in prime_sets(ps):
            for m in measure(N, P, args.h, args.a):
                print(f"| {name} | {m['h']} | {m['rho']:.4f} | {m['Wy']:.4f} | {m['W']:.4f} | "
                      f"{m['A']:.4f} | {m['M']:.4f} | {m['B']:.3f} | {m['A_over_M']:.3f} | "
                      f"{m['A_over_Wy']:.3f} | {m['A1']:.4f} | {m['A2']:.4f} | "
                      f"{m['T1']:.4f} | {m['T2']:.5f} | {m['T2_over_rho2']:.2f} |")
                sys.stdout.flush()


if __name__ == "__main__":
    main()
