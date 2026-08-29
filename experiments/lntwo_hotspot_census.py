#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Probe: hot-spot census of the ln-2 surrogate (the Babel main column).

Keystone fact (Bailey-Misiurewicz strong hot-spot theorem; a version proved
in this repo and used for Stoneham): a UNIFORM CONSTANT-FACTOR upper bound on
visit ratios over all b-adic cylinders forces normality.  Mass conservation
turns upper bounds into lower bounds; the only absolutely continuous
x2-invariant measure is Lebesgue.  So "ln 2 is 2-normal" is EQUIVALENT to:

    no binary word is ever over-visited by more than a constant factor
    by the orbit - one-sided counting statements only.

The orbit is the explicit rational surrogate x_n = res_n / L_n (tracking
error tau_n -> 0 makes surrogate and true visit ratios agree asymptotically),
with the self-contained recurrence

    res_{n+1} = (2 * r * res_n + L_{n+1}/(n+1)) mod L_{n+1},
    L_{n+1} = r * L_n,  r = p if n+1 = p^e else 1.

This census tallies visits to every dyadic cylinder of depth <= LMAX up to
several horizons N and reports the max visit ratio per depth.  Random-model
envelope: max ratio ~ 1 + O(1/sqrt(N * 2^-l)) (Poisson maximum over 2^l
cells).  A persistent hot spot (ratio not shrinking with N) would REFUTE the
census rungs of the ladder; shrinking ratios arm them.

Self-test: res recurrence vs direct definition at n = 3, 10, 37.
"""

import sys
from math import gcd, sqrt
from sympy import factorint

N_MAX = 50_000
LMAX = 12
CHECKPOINTS = [5_000, 20_000, 50_000]


def direct_res(n: int) -> tuple[int, int]:
    L = 1
    for j in range(1, n + 1):
        L = L * j // gcd(L, j)
    A = sum((L // j) * (1 << (n - j)) for j in range(1, n + 1))
    return A % L, L


def main() -> None:
    # --- self-test ------------------------------------------------------------
    res, L = 0, 1
    tests = {3, 10, 37}
    for n in range(1, 38):
        fac = factorint(n)
        r = list(fac)[0] if len(fac) == 1 and n > 1 else 1
        L *= r
        res = (2 * r * res + L // n) % L
        if n in tests:
            want = direct_res(n)
            assert (res, L) == want, f"res recurrence broken at n={n}"
    print("self-test OK: res recurrence matches definition (n=3, 10, 37)")

    # --- census ---------------------------------------------------------------
    counts = [[0] * (1 << l) for l in range(LMAX + 1)]
    res, L = 0, 1
    results = {}
    for n in range(1, N_MAX + 1):
        fac = factorint(n)
        r = list(fac)[0] if len(fac) == 1 and n > 1 else 1
        L *= r
        res = (2 * r * res + L // n) % L
        # top LMAX bits of res/L without full division
        shift = L.bit_length() - (LMAX + 32)
        if shift > 0:
            top = (res >> shift) * (1 << (LMAX + 32)) // (L >> shift)
        else:
            top = (res << (LMAX + 32)) // L
        cell = top >> 32  # LMAX-bit cell index
        for l in range(1, LMAX + 1):
            counts[l][cell >> (LMAX - l)] += 1
        if n in CHECKPOINTS:
            row = {}
            for l in range(1, LMAX + 1):
                expect = n / (1 << l)
                mx = max(counts[l])
                row[l] = mx / expect
            results[n] = row

    print("\nmax visit ratio (observed/expected) per cylinder depth:")
    header = f"{'depth':>6} {'width':>8} " + \
             " ".join(f"N={N:>6}" for N in CHECKPOINTS) + f" {'Poisson-ish':>12}"
    print(header)
    for l in range(1, LMAX + 1):
        vals = " ".join(f"{results[N][l]:>8.3f}" for N in CHECKPOINTS)
        env = 1 + 3 / sqrt(N_MAX / (1 << l))
        print(f"{l:>6} {f'2^-{l}':>8} {vals} {env:>12.3f}")
    print("\nreading: ratios shrinking toward 1 with N at every depth = no")
    print("persistent hot spot = the B-ladder's census rungs hold in range.")
    print("(the keystone: a uniform constant-factor bound at ALL depths, for")
    print(" all N, is EQUIVALENT to 2-normality of ln 2)")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
