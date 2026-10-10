#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Model E|Phi_{<=D}|^4 at D = y^K, y -> infinity, one parity-phase site.  Exact-in-T formula.

Model: T = set of P-primes <= y dividing m (each independently, prob 1/p).  Phi(T) = (-1)^{|T|}.
Since M * prod (1 + b_p) = 1 with b_p = 2/(p-2), the weights M*B_d are the law of a random
squarefree D' (each P-prime <= y included independently with prob 2/p), and

    Phi_{<=D}(T) = E[ 1[D' <= D] prod_{p | D', p in T} (1 - p) ],
    Phi_{<=D}(T) - Phi(T) = - sum_{e subset T} c_T(e) * tau_{not T}(log D - log e),
    c_T(e) = prod_{p in e} 2(1-p)/p * prod_{p in T \\ e} (1 - 2/p),
    tau_{not T}(x) = P( sum_{p notin T} X_p log p > x ),  X_p ~ Bern(2/p).

The law of sum X_p log p is computed on a log grid (step H) by shift-add convolution; primes of
T are removed by stable deconvolution (2/p <= 2/5 < 1/2).  Validated against the brute-force
coefmass_m4.py at (y=100, D=1e4) via --check.

Heuristic under test: per prime of T the operator is ~ -(1 + 2a log p), a = (log tau)'
on scale log y, and E exp(t sum_{p in T} log p / log y) is bounded in y, so M4 should be
bounded uniformly in y at fixed K.  The triangle bound instead gives 3^{|T|}, a (log y)^{c} ghost.

Usage: coefmass_m4_scale.py [samples] [--check]
"""
import itertools
import math
import sys

import numpy as np
from sympy import primerange

H = 0.004  # log-grid step


def law_of_logsum(P, xmax):
    n = int(xmax / H) + 2
    g = np.zeros(n)
    g[0] = 1.0
    for p in P:
        s = int(round(math.log(p) / H))
        if s >= n:
            continue  # contributes only beyond xmax: mass at >xmax tracked as deficit
        q = 2 / p
        g[s:] = (1 - q) * g[s:] + q * g[:-s].copy()
        g[:s] *= 1 - q
    return g  # mass beyond xmax is 1 - g.sum()


def deconv(g, p):
    s = int(round(math.log(p) / H))
    q = 2 / p
    out = g.copy()
    if s >= len(g):
        return out / (1 - q)
    # g = (1-q) out + q shift(out)  =>  out[i] = (g[i] - q out[i-s]) / (1-q)
    out[:s] = g[:s] / (1 - q)
    for i0 in range(s, len(g), s):
        i1 = min(i0 + s, len(g))
        out[i0:i1] = (g[i0:i1] - q * out[i0 - s : i1 - s]) / (1 - q)
    return out


def sample_T(P, S, rng):
    P = np.array(P)
    small = P[P <= 20000]
    large = P[P > 20000]
    hits = rng.random((S, len(small))) < 1 / small
    lam = float(np.sum(1 / large)) if len(large) else 0.0
    cdf = np.cumsum(1 / large) / lam if len(large) else None
    out = []
    for i in range(S):
        T = list(small[hits[i]])
        if len(large):
            k = rng.poisson(lam)
            if k:
                T += list(large[np.searchsorted(cdf, rng.random(k))])
        out.append(sorted(set(int(t) for t in T)))
    return out


def m4_stats(y, Ks, S, rng, q=4, a=1):
    P = [p for p in primerange(2, y + 1) if p % q == a % q]
    xmax = max(Ks) * math.log(y)
    g0 = law_of_logsum(P, xmax)
    Ts = sample_T(P, S, rng)
    lows = {K: np.zeros(S) for K in Ks}
    cache = {}
    for i, T in enumerate(Ts):
        key = tuple(T)
        if key not in cache:
            g = g0
            for p in T:
                g = deconv(g, p)
            cdf = np.cumsum(g)
            vals = {}
            for K in Ks:
                logD = K * math.log(y)
                diff = 0.0
                for r in range(len(T) + 1):
                    for e in itertools.combinations(T, r):
                        loge = sum(math.log(p) for p in e)
                        c = math.prod(2 * (1 - p) / p for p in e) * math.prod(1 - 2 / p for p in T if p not in e)
                        x = logD - loge
                        tau = 1.0 if x < 0 else 1.0 - cdf[min(int(x / H), len(cdf) - 1)]
                        diff -= c * tau
                vals[K] = (-1) ** len(T) + diff
            cache[key] = vals
        for K in Ks:
            lows[K][i] = cache[key][K]
    for K in Ks:
        low = lows[K]
        phi = np.array([(-1.0) ** len(T) for T in Ts])
        print(
            f"y={y:8d} K={K:4.2f} #P={len(P):6d} E|T|={np.mean([len(T) for T in Ts]):.3f} "
            f"| E|low|^2={np.mean(low ** 2):.4f} E|low|^4={np.mean(low ** 4):.4f}±{np.std(low ** 4) / math.sqrt(S):.4f} max|low|={np.max(np.abs(low)):.3f} "
            f"tail={np.mean((phi - low) ** 2):.4f}"
        )
        sys.stdout.flush()


if __name__ == "__main__":
    args = [x for x in sys.argv[1:] if not x.startswith("--")]
    S = int(args[0]) if args else 20000
    rng = np.random.default_rng(7)
    if "--check" in sys.argv:
        # brute-force comparison point: coefmass_m4.py y=100 D=1e4 -> K = 2
        m4_stats(100, [1.0, 1.5, 2.0, 2.5], S, rng)
        sys.exit()
    for y in (10**2, 10**3, 10**4, 10**5, 10**6):
        m4_stats(y, [1.0, 1.5, 2.0, 3.0], S, rng)
