#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Model L^4 norm of the sharp conductor projection Phi_{<=D}, one parity-phase site.

Why: E_int|Phi_{>D}|^2 <= E_model|Phi_{>D}|^2 + 2K TV + 8(1 + M4)/K, where M4 = E|Phi_{<=D}|^4.
That holds because min(|Phi_{>D}|^2, K) is a bounded function of the frozen state (TV transfers),
and E_int|Phi_{<=D}|^4 = M4 up to explicit CRT remainders once D^4 < N (D^4 < N alone is not
exactness; Astra 20261011T051146Z).  Optimizing K gives an error of about
sqrt(M4 TV).  So the integer transfer of the energy cutoff is reduced to: is M4 = O(1),
uniformly in y and D?  (If M4 grows like a log power, that is the (log y)^C ghost again.)

Model: independent residues; for p in P (= a mod q), p <= y: p | m with probability 1/p.
psi_p = -1 if p | m else 1, mu_p = 1 - 2/p.  Monte Carlo over samples.

Usage: coefmass_m4.py [samples]
"""
import math
import sys

import numpy as np
from sympy import primerange


def smooth_squarefree(primes, D):
    out = [(1, ())]
    for p in primes:
        if p > D:
            break
        out += [(d * p, fs + (p,)) for d, fs in out if d * p <= D]
    return out


def run(y, D, S, rng, q=4, a=1):
    P = [p for p in primerange(2, y + 1) if p % q == a % q]
    idx = {p: i for i, p in enumerate(P)}
    mu = np.array([1 - 2 / p for p in P])
    M = float(np.prod(mu))
    hit = rng.random((S, len(P))) < (1 / np.array(P))  # p | m
    psi = np.where(hit, -1.0, 1.0)
    r = (psi - mu) / mu  # phi_p / mu_p
    phi = np.prod(psi, axis=1)
    low = np.zeros(S)
    ds = smooth_squarefree(P, D)
    for _, fs in ds:
        t = np.ones(S)
        for p in fs:
            t *= r[:, idx[p]]
        low += t
    low *= M
    tail = np.mean((phi - low) ** 2)
    m4 = np.mean(low**4)
    print(
        f"y={y:6d} D={D:7d} #d={len(ds):6d} | E|low|^2={np.mean(low ** 2):.4f} E|low|^4={m4:.4f} "
        f"max|low|={np.max(np.abs(low)):.3f} P(|low|>2)={np.mean(np.abs(low) > 2):.2e} tail={tail:.4f}"
    )
    sys.stdout.flush()


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = np.random.default_rng(1)
    for y in (100, 1000, 10000):
        for D in (100, 1000, 10000, 100000):
            run(y, D, S, rng)
