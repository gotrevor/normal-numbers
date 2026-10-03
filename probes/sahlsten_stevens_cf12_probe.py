#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Numeric tripwire for `NormalNumbers.BadNormal.Literature.SahlstenStevensBernoulli12`.

Referee: docs/BAD-NORMAL-REFEREE-2026-10-03.md.

mu = law of [0; 1+w0, 1+w1, ...] under fair coins = stationary measure of the IFS
{f1(t) = 1/(1+t), f2(t) = 1/(2+t)} with weights (1/2, 1/2).

PART A (Lyapunov exponent, independent of probes/bad_bernoulli12_dimension.py).
  lambda = int log|T'| dmu = -P'(0), where P(t) = log rho(L_t) and
  L_t g(x) = sum_a (1/2) (a+x)^{-2t} g(1/(a+x)) on [0,1] (|T'(1/(a+x))| = (a+x)^2).
  rho(L_t) is computed by Chebyshev collocation (spectral convergence), and the derivative by a
  Richardson-extrapolated central difference.
  KNOWN-ANSWER CONTROL for that instrument: the same operator without the 1/2 weights has
  rho = 1 exactly at s = dim_H E_{1,2} = 0.5312805062772051416... (Jenkinson-Pollicott), and at
  t = 0 the weighted operator fixes constants, so rho(L_0) = 1 exactly.

PART B (Fourier decay).  |mu^(xi)| = |E e(xi x)|, averaged EXACTLY over all 2^N depth-N words
  (uniform weights are exact), each cylinder represented by one point f_w(x0).  Error in each
  phase <= 2 pi |xi| * (max depth-N cylinder width); max width is attained by the all-ones word,
  1/(F_{N+1} F_{N+2}) (computed below, ~1.1e-10 at N = 24), so the error in |mu^| is <= 4.6e-5
  at xi = 2^16, far below the measured values.
  CONTROLS through the SAME pipeline (same word enumeration, same averaging):
    * Dirac at 1/phi = [0; 1, 1, ...]: word set {1}^N only -> |FT| = 1 for every xi (flat).
    * middle-third Cantor measure, IFS {t/3, t/3 + 2/3}: along xi = 3^k the modulus is
      prod_{j>=1} |cos(2 pi 3^{-j})| = 0.3714... (hand-checked in the referee doc) -- NO decay.
  Support hand-check: E_{1,2} spans [(sqrt3 - 1)/2, sqrt3 - 1] = [0.36603, 0.73205].

Run: probes/sahlsten_stevens_cf12_probe.py   (exit 0 = all assertions pass)
"""
import math

import numpy as np

# ---------------------------------------------------------------- PART A


def cheb_nodes(n):
    k = np.arange(n)
    return 0.5 * (1 - np.cos(np.pi * (k + 0.5) / n))  # first-kind nodes on [0,1]


def interp_matrix(nodes, pts):
    """Barycentric Lagrange: row i evaluates the interpolant of node values at pts[i]."""
    n = len(nodes)
    w = np.array([1.0 / np.prod([nodes[j] - nodes[k] for k in range(n) if k != j]) for j in range(n)])
    d = pts[:, None] - nodes[None, :]
    exact = np.isclose(d, 0.0, atol=1e-15)
    d[exact] = 1.0
    m = w[None, :] / d
    m = m / m.sum(axis=1, keepdims=True)
    for i, j in zip(*np.nonzero(exact)):
        m[i] = 0.0
        m[i, j] = 1.0
    return m


def rho(t, weight, n=40):
    x = cheb_nodes(n)
    M = np.zeros((n, n))
    for a in (1, 2):
        M += weight * (a + x)[:, None] ** (-2 * t) * interp_matrix(x, 1.0 / (a + x))
    return max(abs(np.linalg.eigvals(M)))


def lyapunov(n=40):
    P = lambda t: math.log(rho(t, 0.5, n))
    d = lambda h: (P(h) - P(-h)) / (2 * h)
    h = 1e-3
    return -(4 * d(h / 2) - d(h)) / 3  # Richardson: O(h^4)


def dim_E12(n=40):
    lo, hi = 0.4, 0.7
    for _ in range(60):
        mid = (lo + hi) / 2
        if rho(mid, 1.0, n) > 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


# ---------------------------------------------------------------- PART B


def word_points(maps, depth, x0):
    """All f_{a1} o ... o f_{a_depth}(x0), each word once (uniform weights)."""
    X = np.array([x0])
    for _ in range(depth):
        X = np.concatenate([f(X) for f in maps])
    return X


def ft(X, xi, chunk=1 << 22):
    s = 0j
    for i in range(0, len(X), chunk):
        s += np.exp(2j * np.pi * xi * X[i:i + chunk]).sum()
    return abs(s / len(X))


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def main():
    # ---- A
    assert abs(rho(0.0, 0.5) - 1.0) < 1e-12, "rho(L_0) must be 1 (constants are fixed)"
    s = dim_E12()
    print(f"[A control] dim_H E_(1,2) from rho=1: {s:.12f}  (literature 0.531280506277205)")
    assert abs(s - 0.5312805062772051) < 1e-9
    lam = lyapunov()
    lam_coarse = lyapunov(n=24)
    dim = math.log(2) / lam
    print(f"[A] lambda = {lam:.8f}  (n=24 nodes: {lam_coarse:.8f})  dim mu = log2/lambda = {dim:.6f}")
    assert abs(lam - lam_coarse) < 1e-7
    assert 1.3459 < lam < 1.3462, lam  # inside the audit's bracket [1.341565, 1.348663]
    assert dim > 0.5149 and lam < 2 * math.log(2)

    # ---- B
    N = 24
    f1 = lambda t: 1.0 / (1.0 + t)
    f2 = lambda t: 1.0 / (2.0 + t)
    X = word_points([f1, f2], N, 0.5)
    lo_hand, hi_hand = (math.sqrt(3) - 1) / 2, math.sqrt(3) - 1
    print(f"[B] support of the 2^{N} points: [{X.min():.6f}, {X.max():.6f}]  hand [{lo_hand:.6f}, {hi_hand:.6f}]")
    assert abs(X.min() - lo_hand) < 1e-6 and abs(X.max() - hi_hand) < 1e-6
    wmax = 1.0 / (fib(N + 1) * fib(N + 2))
    print(f"[B] max depth-{N} cylinder width 1/(F_{N+1}F_{N+2}) = {wmax:.3e}")

    golden = word_points([f1], N, 0.5)  # Dirac control: one word
    cantor = word_points([lambda t: t / 3, lambda t: t / 3 + 2 / 3], 20, 0.5)

    print("  k   xi=2^k   |mu^(xi)|   err bound   |Dirac 1/phi|")
    vals = {}
    for k in range(6, 17):
        xi = 2.0**k
        vals[k] = ft(X, xi)
        err = 2 * math.pi * xi * wmax
        g = ft(golden, xi)
        print(f" {k:2d} {xi:8.0f}   {vals[k]:.4e}   {err:.1e}     {g:.6f}")
        assert vals[k] > 20 * err, "probe resolution insufficient"
        assert abs(g - 1.0) < 1e-9
    ks = np.arange(6, 17)
    slope = np.polyfit(ks * math.log(2), np.log([vals[k] for k in ks]), 1)[0]
    print(f"[B] fitted exponent |mu^| ~ xi^slope over 2^6..2^16: {slope:.3f}")
    assert slope < -0.1, "no visible decay"
    # single dyadic xi are noisy (|mu^(2^13)| > |mu^(2^7)|); the meaningful statistic is the
    # ENVELOPE sup_{xi in [2^k, 2^(k+1)]} |mu^(xi)|, sampled on 48 log-spaced points per band
    print("  band k   sup_[2^k,2^(k+1)] |mu^|   sup |Dirac|")
    env = {}
    for k in range(6, 17):
        grid = 2.0 ** (k + np.arange(48) / 48)
        env[k] = max(ft(X, xi) for xi in grid)
        envg = max(ft(golden, xi) for xi in grid[:4])
        print(f"   {k:2d}       {env[k]:.4e}              {envg:.6f}")
        assert abs(envg - 1.0) < 1e-9
    eslope = np.polyfit(ks * math.log(2), np.log([env[k] for k in ks]), 1)[0]
    print(f"[B] fitted envelope exponent: {eslope:.3f}")
    assert eslope < -0.1
    assert max(env[k] for k in range(14, 17)) < 0.5 * min(env[k] for k in range(6, 9))

    hand = math.prod(abs(math.cos(2 * math.pi * 3.0**-j)) for j in range(1, 60))
    print(f"[B control] Cantor plateau hand value prod|cos(2pi 3^-j)| = {hand:.6f}")
    for k in range(3, 12):
        c = ft(cantor, 3.0**k)
        # depth 20 truncation: factors j > 20 - k are replaced by the point-x0 phase only;
        # the finite product over j = 1..20-k is the exact modulus of the depth-20 average
        fin = math.prod(abs(math.cos(2 * math.pi * 3.0**-j)) for j in range(1, 21 - k))
        print(f"   xi=3^{k:<2d} |Cantor^| = {c:.6f}   finite-product {fin:.6f}")
        assert abs(c - fin) < 1e-6 and c > 0.37
    print("OK")


if __name__ == "__main__":
    main()
