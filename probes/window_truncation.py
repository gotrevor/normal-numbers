#!/usr/bin/env -S uv run --quiet --with numpy python3
"""PROBE 13 (2026-09-20, Ren): the fixed-K question.  Window mean with K sites vs the schedule J = windowJ N.
|W_K(N) - W_J(N)| <= E_n |prod_{K<j<=J} f_j - 1| <= 2 pi |h| (avg omega over window) / (3 4^K).
Report the measured difference against that L^1 bound, per K, at several N.  If the difference decays like
4^-K with the log log N factor, a FIXED K never suffices, but K ~ log_2 log_2 log_2 N does.
"""
import sys, math, cmath
import numpy as np
def omega_full(L):
    om = np.zeros(L + 1, dtype=np.int8); comp = np.zeros(L + 1, dtype=bool)
    for p in range(2, L + 1):
        if not comp[p]:
            comp[p*p::p] = True; om[p::p] += 1
    return om
def windowJ(N):
    l2 = N.bit_length() - 1
    return (l2.bit_length() - 1) + 1
for lN in (16, 20, 24):
    N = 1 << lN; J = windowJ(N)
    om = omega_full(2 * N + J + 2)
    n = np.arange(N, 2 * N)
    avg = om[N + 1:2 * N + 1].astype(float).mean()
    for h in (1, 3, 5):
        phases = [np.exp(2j * math.pi * h * om[n + j].astype(float) / 4**j) for j in range(1, J + 1)]
        full = np.ones(N, dtype=np.complex128)
        for ph in phases: full *= ph
        WJ = full.mean()
        row = []
        part = np.ones(N, dtype=np.complex128)
        for K in range(1, J + 1):
            part *= phases[K - 1]
            WK = part.mean()
            bound = 2 * math.pi * h * avg / (3 * 4**K)
            row.append(f"K={K}: |WK-WJ|={abs(WK - WJ):.4f} L1bd={bound:.3f} |WK|={abs(WK):.4f}")
        print(f"N=2^{lN} J={J} avg_omega={avg:.3f} h={h}  |WJ|={abs(WJ):.4f}\n   " + "\n   ".join(row))
        sys.stdout.flush()
