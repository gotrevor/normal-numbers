#!/usr/bin/env -S uv run --quiet python3
"""Probe: the Walsh/parity <-> block-frequency identity (DESIGN-2026-09-20-walsh-weyl-bridge).

For a binary digit sequence s and a finite offset set S, the parity correlation is
    P_N(S) = (1/N) sum_{n<N} prod_{i in S} (-1)^(s(n+i)),
and for a block w in {0,1}^L the frequency F_N(w) counts n<N with s(n+i)=w_i for i<L.

Claimed (exact, finite, no analysis):
    F_N(w) = 2^-L * (1 + sum_{S nonempty subset of [L]} (-1)^(w.S) P_N(S))      (I)
    P_N(S) = sum_w (-1)^(w.S) F_N(w)                                            (II)
    |F_N(w) - 2^-L| <= max_{S nonempty} |P_N(S)| * (2^L - 1) / 2^L              (A)
    |P_N(S)| <= sum_w |F_N(w) - 2^-L|                                           (B)

This probe checks (I),(II),(A),(B) to floating tolerance on four sequences, and measures
the depth-2 parity correlation of the 11-avoiding (golden-mean) subshift, which the design
doc claims is bounded away from zero.
"""
import sys
from itertools import product
from random import Random


def parity(s, S, N):
    tot = 0
    for n in range(N):
        p = 1
        for i in S:
            if s[n + i]:
                p = -p
        tot += p
    return tot / N


def freq(s, w, N):
    L = len(w)
    c = 0
    for n in range(N):
        if all(s[n + i] == w[i] for i in range(L)):
            c += 1
    return c / N


def champernowne_bits(M):
    out = []
    k = 1
    while len(out) < M:
        out.extend(int(b) for b in bin(k)[2:])
        k += 1
    return out[:M]


def golden_mean_bits(M, seed=7):
    """11-avoiding sequence, sampled from the measure of MAXIMAL ENTROPY (Parry).

    Markov chain on {0,1} with no 11: from 0 go to 1 w.p. p, from 1 always to 0.
    Parry has p = P(0->1) = 1/phi^2 = 2 - phi = 0.3819660...  (NOT 1/phi; the
    transition is A_ij v_j / (phi v_i) with v = (phi, 1) the Perron eigenvector).
    Stationary: pi_0 = 1/(1+p) = 0.7236068, pi_1 = 0.2763932.
    """
    phi = (1 + 5 ** 0.5) / 2
    p = 1 / phi ** 2
    rng = Random(seed)
    out = [0]
    while len(out) < M:
        out.append(1 if (out[-1] == 0 and rng.random() < p) else 0)
    return out[:M]


def thue_morse_bits(M):
    return [bin(n).count("1") & 1 for n in range(M)]


def check(name, s, N, L=3):
    subsets = [S for k in range(1, L + 1) for S in __import__("itertools").combinations(range(L), k)]
    P = {S: parity(s, S, N) for S in subsets}
    worst_I = worst_II = 0.0
    maxdev = 0.0
    for w in product((0, 1), repeat=L):
        F = freq(s, w, N)
        rhs = 1.0
        for S in subsets:
            sign = -1 if sum(w[i] for i in S) % 2 else 1
            rhs += sign * P[S]
        worst_I = max(worst_I, abs(F - rhs / 2 ** L))
        maxdev = max(maxdev, abs(F - 2.0 ** -L))
    for S in subsets:
        tot = sum((-1 if sum(w[i] for i in S) % 2 else 1) * freq(s, w, N) for w in product((0, 1), repeat=L))
        worst_II = max(worst_II, abs(tot - P[S]))
    maxP = max(abs(P[S]) for S in subsets)
    sumdev = sum(abs(freq(s, w, N) - 2.0 ** -L) for w in product((0, 1), repeat=L))
    okA = maxdev <= maxP * (2 ** L - 1) / 2 ** L + 1e-12
    okB = maxP <= sumdev + 1e-12
    print(f"{name:<16} N={N:<6} |I err|={worst_I:.2e} |II err|={worst_II:.2e} "
          f"maxdev={maxdev:.4f} max|P|={maxP:.4f}  (A){'ok' if okA else 'FAIL'} (B){'ok' if okB else 'FAIL'}")
    return worst_I, worst_II, okA, okB, P


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    M = N + 10
    check("champernowne", champernowne_bits(M), N)
    check("golden-mean(11-free)", golden_mean_bits(M), N)
    check("thue-morse", thue_morse_bits(M), N)
    rng = Random(3)
    check("random", [rng.getrandbits(1) for _ in range(M)], N)
    check("constant-zero", [0] * M, N)

    print("\n-- depth-2 parity of the 11-avoiding subshift (design doc claim) --")
    s = golden_mean_bits(M)
    P01 = parity(s, (0, 1), N)
    F = {w: freq(s, w, N) for w in product((0, 1), repeat=2)}
    print(f"  F(00)={F[(0,0)]:.4f} F(01)={F[(0,1)]:.4f} F(10)={F[(1,0)]:.4f} F(11)={F[(1,1)]:.4f}")
    print(f"  P_N({{0,1}}) = F00+F11-F01-F10 = {P01:.4f}   (design doc: bounded away from 0)")
    print(f"  depth-1: P_N({{0}}) = {parity(s,(0,),N):.4f}")
    r5 = 5 ** 0.5
    print(f"  exact Parry (hand-computed, see test): F(00)=1/sqrt5={1/r5:.4f}, "
          f"F(01)=F(10)=(5-sqrt5)/10={(5-r5)/10:.4f}, F(11)=0")
    print(f"  exact P({{0,1}}) = 2/sqrt5 - 1 = {2/r5 - 1:.4f};  exact P({{0}}) = 1/sqrt5 = {1/r5:.4f}")


if __name__ == "__main__":
    main()
