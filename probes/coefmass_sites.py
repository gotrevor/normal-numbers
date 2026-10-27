#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy", "sympy"]
# ///
"""Centered-expansion conductor cutoff, J sites: integer L^2 tail vs exact model tail.

Sites j = 1..J, z_j = e(h/4^j), w_j = z_j - 1, cutoffs y_j = N^(alpha 2^-(j-1)).
P = primes = a (mod q) with p > J (so a prime divides at most one n+j).
    Phi(n) = prod_j z_j^{omega_{P, <= y_j}(n+j)} = prod_p psi_p(n),
    psi_p(n) = z_j if p | n+j and p <= y_j, else 1;   mu_p = 1 + a_p/p, a_p = sum_{j: p<=y_j} w_j.
Centered expansion over S (subsets of P-primes <= y_1), truncated at d_S <= D = N^theta.

phi_p/mu_p = b_p + sum_j c_{p,j} 1[p | n+j],  b_p = (1-mu_p)/mu_p,  c_{p,j} = w_j/mu_p (p <= y_j).
Expanding prod_{p|d} over an assignment of each p | d to {0, 1..J} gives, for each tuple
(e_1..e_J), a single residue class mod prod e_j (n = -j mod e_j) with coefficient
prod_j C_j(e_j) * sum_{e_0} B(e_0) over e_0 coprime, e_0 prod e_j <= D.

Usage: coefmass_sites.py [h] [J] [q] [a]     (defaults 2 2 4 1)
"""
import cmath
import itertools
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


def crt(residues, moduli):
    x, m = 0, 1
    for r, n in zip(residues, moduli):
        # solve x' = x mod m, x' = r mod n
        t = ((r - x) * pow(m, -1, n)) % n
        x, m = x + m * t, m * n
    return x % m, m


def run(N, alpha, theta, h, J, q, a, ys=None):
    if ys is None:
        ys = [int(N ** (alpha * 2.0 ** (-j))) for j in range(J)]  # y_1 >= y_2 >= ...
    z = [cmath.exp(2j * math.pi * h / 4 ** (j + 1)) for j in range(J)]
    w = [zz - 1 for zz in z]
    P = [p for p in primerange(J + 1, ys[0] + 1) if p % q == a % q]
    D = int(N**theta)

    sites = {p: [j for j in range(J) if p <= ys[j]] for p in P}
    mu = {p: 1 + sum(w[j] for j in sites[p]) / p for p in P}
    var = {p: sum(abs(w[j]) ** 2 for j in sites[p]) / p - abs(mu[p] - 1) ** 2 for p in P}
    M = math.prod(mu.values())

    # exact model tail and Markov bound
    ds = smooth_squarefree(P, D)
    model_low = sum(abs(M) ** 2 * math.prod(var[p] / abs(mu[p]) ** 2 for p in fs) for _, fs in ds)
    markov = sum(var[p] * math.log(p) for p in P) / math.log(D)

    # coefficient per site-assignment tuple
    coef = {}
    for d, fs in ds:
        choices = [[None] + sites[p] for p in fs]
        for assign in itertools.product(*choices):
            c = 1 + 0j
            es = [1] * J
            for p, s in zip(fs, assign):
                if s is None:
                    c *= (1 - mu[p]) / mu[p]
                else:
                    c *= w[s] / mu[p]
                    es[s] *= p
            key = tuple(es)
            coef[key] = coef.get(key, 0) + c

    n0 = 1  # array index i <-> n = i + 1
    low = np.zeros(N, dtype=complex)
    for es, c in coef.items():
        r, m = crt([(-(j + 1)) % e for j, e in enumerate(es)], list(es))
        start = (r - n0) % m
        low[start::m] += c
    low *= M

    n = np.arange(1, N + 1)
    phi = np.ones(N, dtype=complex)
    for p in P:
        for j in sites[p]:
            phi[(-(j + 1) - n0) % p :: p] *= z[j]

    int_tail = float(np.mean(np.abs(phi - low) ** 2))
    int_low2 = float(np.mean(np.abs(low) ** 2))
    model_tail = 1 - model_low
    u = math.sqrt(1 / (2 * alpha)) if alpha else float("nan")
    print(
        f"N={N:.0e} u={u:4.2f} y={ys} theta={theta:.2f} D={D:6d} #P={len(P):4d} #tuples={len(coef):6d} "
        f"| int_tail={int_tail:.5f} model_tail={model_tail:.5f} ratio={int_tail / model_tail if model_tail > 1e-12 else float('nan'):6.3f} "
        f"markov={markov:.4f} | int|low|^2={int_low2:.5f} model={model_low:.5f} |mean Phi|={abs(phi.mean()):.5f} |M|={abs(M):.5f}"
    )
    sys.stdout.flush()


if __name__ == "__main__":
    if "--period" in sys.argv:
        # full-CRT-period hand control: P = {5,13,17}, period 4*1105 covers both sites and Q-free;
        # N a multiple of 5*13*17 makes integer means equal model means up to float error.
        for J, ys in ((1, [17]), (2, [17, 13]), (3, [17, 13, 5])):
            for theta in (0.2, 0.3, 0.4):
                run(1105 * 9001, 0, theta, 2, J, 4, 1, ys=ys)
        sys.exit()
    h, J, q, a = (int(x) for x in (sys.argv[1:] + ["2", "2", "4", "1"][len(sys.argv) - 1 :]))
    print(f"h={h} J={J} P = {a} mod {q}")
    for alpha in (0.5, 0.25):
        for N in (10**5, 10**6, 10**7):
            for theta in (0.25, 0.4, 0.5):
                run(N, alpha, theta, h, J, q, a)
