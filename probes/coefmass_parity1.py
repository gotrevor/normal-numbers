#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Centered-expansion conductor cutoff, one parity-phase site: model vs integers.

Site j=1, z = -1 (h = 2), P = primes = a (mod q), frozen cutoff y.  For m = n+1,
    Phi(m)   = prod_{p in P, p <= y} psi_p(m),   psi_p = -1 if p | m else 1,
    mu_p     = 1 - 2/p,   phi_p = psi_p - mu_p,   Var_p = 4/p - 4/p^2.
Centered expansion Phi = sum_S prod_{p not in S} mu_p prod_{p in S} phi_p; truncate to d_S <= D = N^theta.

Algebra used for speed: with M = prod mu_p, b_p = (2/p)/mu_p = 2/(p-2), and
phi_p/mu_p = b_p * (1 + gamma_p 1[p|m]) with gamma_p = -p,
    Phi_<=D(m) / M = sum_{e | m, e <= D} gamma_e beta_e,   beta_e = sum_{d <= D, e | d} B_d,
gamma_e = prod_{p|e} (-p), B_d = prod_{p|d} b_p.  A divisor sum, so one slice-add per e.

Prints, per (N, y, theta): the integer mean |Phi - Phi_<=D|^2, the exact model tail
sum_{d_S > D} E_S, the Markov bound (sum_p Var_p log p)/log D, and the integer/model ratio.
"""
import math
import sys

import numpy as np
from sympy import primerange


def smooth_squarefree(primes, D):
    """All squarefree products of `primes` that are <= D, as (d, factor list)."""
    out = [(1, [])]
    for p in primes:
        if p > D:
            break
        out += [(d * p, fs + [p]) for d, fs in out if d * p <= D]
    return out


def run(N, y, theta, q=4, a=1):
    P = [p for p in primerange(2, y + 1) if p % q == a % q]
    D = int(N**theta)
    mu = {p: 1 - 2 / p for p in P}
    var = {p: 4 / p - 4 / p**2 for p in P}
    M = math.prod(mu.values())

    ds = smooth_squarefree(P, D)
    B = {d: math.prod(2 / (p - 2) for p in fs) for d, fs in ds}
    fac = dict(ds)
    # beta_e = sum over d <= D divisible by e of B_d
    beta = {e: 0.0 for e, _ in ds}
    for d, fs in ds:
        # every squarefree divisor e of d
        divs = [1]
        for p in fs:
            divs += [x * p for x in divs]
        for e in divs:
            beta[e] += B[d]

    m = np.arange(2, N + 2)  # m = n + 1, n = 1..N
    low = np.zeros(N)
    for e, fs in ds:
        g = math.prod(-p for p in fs)
        low[(e - 2) % e :: e] += g * beta[e]  # indices where e | m (m = idx + 2)
    low *= M

    phi = np.ones(N)
    for p in P:
        phi[p - 2 :: p] *= -1.0

    int_tail = float(np.mean((phi - low) ** 2))
    int_low2 = float(np.mean(low**2))
    model_low = sum(M**2 * math.prod(var[p] / mu[p] ** 2 for p in fs) for _, fs in ds)
    model_tail = 1 - model_low
    markov = sum(var[p] * math.log(p) for p in P) / math.log(D)
    u = math.sqrt(math.log(N) / (2 * math.log(y)))
    print(
        f"N={N:.0e} y={y:6d} u={u:4.2f} theta={theta:.2f} D={D:7d} #P={len(P):4d} #d={len(ds):6d} "
        f"| int_tail={int_tail:.5f} model_tail={model_tail:.5f} ratio={int_tail / model_tail if model_tail else float('nan'):6.3f} "
        f"markov={markov:.4f} | int|low|^2={int_low2:.5f} model={model_low:.5f} mean(Phi)={phi.mean():+.5f} M={M:+.5f}"
    )
    sys.stdout.flush()


if __name__ == "__main__":
    for N in (10**5, 10**6, 10**7):
        for alpha in (0.5, 0.25, 0.125):
            y = int(N**alpha)
            for theta in (0.25, 0.4, 0.5):
                run(N, y, theta)
