#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Limit-model (y -> infinity) moments and tail of the conductor-truncated product, one parity site.

Reduction (delta = 1/2, so D' has Dickman(1) law with density e^{-gamma} rho):
    Psi'(K) = (-1)^{|T|} Phi_{<=D}  =  mu_T * G (K),     mu_T = prod_{v in T} (2 delta_v - delta_0),
    G = ramp * G'',  G'' = e^{-gamma} (delta_0 + rho'(a) da),
so for K <= 1, Psi'(K) = e^{-gamma} f(K) exactly, where
    f(z) = (mu_T * ramp)(z) = sum_{e subset T} 2^{|e|} (-1)^{|T \\ e|} (z - s_e)_+ .
T = Poisson process, intensity delta dv/v on [eta, 1]  (v = log p / log y).

Known answers (eta -> 0, delta = 1/2, z <= 1):  E f(z) = e^{-gamma} z^2/2,  E f(z)^2 = z^2/2.

Algorithm ("wild frontier"): process points largest first.  A partial subset with remaining
budget d = z - s_e and remaining point mass S closes exactly as w (d - 2S) when d >= S (every
extension stays below z, and each operator has mass 1 and mean shift 2v); it dies when d < 0.
Only partial subsets with 0 <= d < S branch.  Exact up to the truncation at eta.

Importance sampling: sample at intensity tilt*delta, reweight by the Poisson likelihood ratio.

Usage: coefmass_limit_tail.py [--delta 0.5] [--eta 1e-6] [--samples 100000] [--tilt 1]
                              [--z 0.5,1,2] [--seed 1] [--degree 1] [--check]
"""
import argparse
import itertools
import math
import sys

import numpy as np

GAMMA = 0.5772156649015329


def sample_points(rng, rate, L):
    n = rng.poisson(rate * L)
    return np.sort(np.exp(-L * rng.random(n)))[::-1]


def suffix_moments(v, m):
    """M[k][j] = int x^j d mu_{v_k, v_{k+1}, ...}(x), j <= m;  mu_v = 2 delta_v - delta_0."""
    n = len(v)
    M = np.zeros((n + 1, m + 1))
    M[n, 0] = 1.0
    for k in range(n - 1, -1, -1):
        mv = [2 * v[k] ** i - (i == 0) for i in range(m + 1)]
        for j in range(m + 1):
            M[k, j] = sum(math.comb(j, i) * mv[i] * M[k + 1, j - i] for i in range(j + 1))
    return M


def f_frontier(v, z, m=1):
    """(mu_T * x_+^m)(z) for descending points v.  Returns (value, max frontier size).

    m = 1 is the sharp cutoff (Psi' = e^{-gamma} f for K <= 1).  m = k + 1 is the Riesz-smoothed
    cutoff with weight (1 - log d / log D)^k, which keeps the support d <= D."""
    S = np.concatenate([np.cumsum(v[::-1])[::-1], [0.0]])
    M = suffix_moments(v, m)
    binom = [math.comb(m, j) * (-1) ** j for j in range(m + 1)]
    front = [(z, 1.0)]
    total = 0.0
    width = 1
    for k, vk in enumerate(v):
        Sk = S[k]
        nxt = []
        for d, w in front:
            if d < 0:
                continue
            if d >= Sk:  # every extension stays in the polynomial region: close exactly
                total += w * sum(binom[j] * d ** (m - j) * M[k, j] for j in range(m + 1))
            else:
                nxt.append((d - vk, 2 * w))
                nxt.append((d, -w))
        front = nxt
        width = max(width, len(front))
        if not front:
            break
    for d, w in front:
        if d >= 0:
            total += w * d**m
    return total, width


def f_brute(v, z, m=1):
    n = len(v)
    tot = 0.0
    for r in range(n + 1):
        for e in itertools.combinations(range(n), r):
            s = sum(v[i] for i in e)
            if s < z:
                tot += 2**r * (-1) ** (n - r) * (z - s) ** m
    return tot


def run(args):
    rng = np.random.default_rng(args.seed)
    L = math.log(1 / args.eta)
    d, rate = args.delta, args.delta * args.tilt
    zs = [float(x) for x in args.z.split(",")]
    S = args.samples
    vals = np.zeros((S, len(zs)))
    logw = np.zeros(S)
    widths = np.zeros(S, dtype=int)
    for i in range(S):
        v = sample_points(rng, rate, L)
        # dP/dP' for Poisson(d dv/v) vs Poisson(rate dv/v) on [eta,1]
        logw[i] = len(v) * math.log(d / rate) - (d - rate) * L
        for j, z in enumerate(zs):
            vals[i, j], wd = f_frontier(v, z, args.degree)
            widths[i] = max(widths[i], wd)
    w = np.exp(logw)
    print(f"# degree={args.degree} delta={d} eta={args.eta:g} L={L:.2f} samples={S} tilt={args.tilt} "
          f"E[w]={w.mean():.4f} max frontier={widths.max()}")
    for j, z in enumerate(zs):
        a = np.abs(vals[:, j])
        line = [f"z={z:4.2f}"]
        if args.delta == 0.5 and z <= 1 and args.degree == 1:
            line.append(f"[ctrl E f={math.exp(-GAMMA) * z * z / 2:.4f} E f^2={z * z / 2:.4f}]")
        m1 = w * vals[:, j]
        line.append(f"E f={m1.mean():.4f}±{m1.std() / math.sqrt(S):.4f}")
        for q in (2, 3, 4, 5, 6):
            x = w * a**q
            share = x.max() / x.sum() if x.sum() > 0 else 0
            line.append(f"E|f|^{q}={x.mean():.4g}±{x.std() / math.sqrt(S):.2g}(top {share:.2f})")
        print(" ".join(line))
        tl = []
        for t in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024):
            p = np.mean(w * (a > t))
            tl.append(f"P>{t}={p:.2e}")
        print("   tail: " + " ".join(tl))
    sys.stdout.flush()


def check(rng):
    bad = 0
    for m in (1, 2, 3):
        for _ in range(200):
            v = sample_points(rng, 0.5 * 3, math.log(1e4))
            if len(v) > 14:
                continue
            for z in (0.3, 1.0, 2.5):
                a, _ = f_frontier(v, z, m)
                b = f_brute(v, z, m)
                if abs(a - b) > 1e-8 * max(1, abs(b)):
                    bad += 1
    print(f"frontier vs brute force (degrees 1-3): {bad} mismatches")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=float, default=0.5)
    ap.add_argument("--eta", type=float, default=1e-6)
    ap.add_argument("--samples", type=int, default=100000)
    ap.add_argument("--tilt", type=float, default=1.0)
    ap.add_argument("--z", default="0.5,1,2")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--degree", type=int, default=1, help="1 = sharp cutoff; k+1 = Riesz weight (1-t)^k")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    if a.check:
        check(np.random.default_rng(a.seed))
    run(a)
