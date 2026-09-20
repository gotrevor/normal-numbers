#!/usr/bin/env -S uv run --quiet python3
"""Probe: T3c — digit-run caps for alpha_{2,3} in base 6 at the critical slice.

Block K of the base-6 expansion (positions 3^(K-1) < n <= 3^K) reads out
v_n ~= (3^a mod 2^c) / 2^c with a = n - K, c = 3^K - n (readout theorem,
`stoneham_base6_readout`).  The CRITICAL position n* is the last n in the block
with 3^a < 2^c; there v = 3^a / 2^c is close to 1 exactly when the two-log form
c*log2 - a*log3 is small, so a run of the digit 5 starting at n*+1 is capped by
any lower bound on 2^c - 3^a.  Three caps, all hand-derived from D = 2^c - 3^a:

  trivial   D >= 1                          -> L <= c*log6(2)
  beta=1/3  D >= 3^a / 2^(a/3)  (sep_two_three, collatz-moonshot)
                                            -> L <= log6(2^c 2^(a/3) / 3^a)
  poly      c log2 - a log3 >= C / a^436 (rhinLite_log23_measure), 1-v >= delta/2
                                            -> L <= 436*log6(a) + log6(2/C)

with log2(1/C) = 1 + 6000*log2(396/5) + 436*log2(6)  (rhinLiteSepC).
The true run length L is computed exactly: L = max{L : D * 6^L <= 2^c}; for
K <= 9 it is cross-checked against the actual digit stream of alpha computed
by exact integer arithmetic (independent of the readout theorem).
"""
import sys
from math import log, log2

L3 = log(3) / log(6)
L2 = log(2) / log(6)
LOG2_INV_C = 1 + 6000 * log2(396 / 5) + 436 * log2(6)


def critical(K):
    """Return (n*, a, c) for block K: last n in (3^(K-1), 3^K) with 3^a < 2^c."""
    S = 3 ** K
    # a*log2(3) < c = S - n, a = n - K  ->  n < (S + K*log2 3)/(1 + log2 3); take floor, then fix
    n = int((S + K * log2(3)) / (1 + log2(3)))
    while 3 ** (n - K) >= 2 ** (S - n):
        n -= 1
    while 3 ** (n + 1 - K) < 2 ** (S - n - 1):
        n += 1
    return n, n - K, S - n


def run_of_fives(D, c):
    """max L with D * 6^L <= 2^c."""
    L, x = 0, D
    while x * 6 <= (1 << c):
        x *= 6
        L += 1
    return L


def alpha_digits_base6(N):
    """First N base-6 digits of alpha_{2,3} = sum 1/(3^k 2^(3^k)), exact integers."""
    P = int(N * log2(6)) + 200
    # scale alpha by 2^P as integer (floor), summing terms until they vanish
    tot, k = 0, 1
    while True:
        e = 3 ** k
        if e > P:
            break
        tot += (1 << (P - e)) // (3 ** k)
        k += 1
    digs = []
    x = tot
    for _ in range(N):
        x *= 6
        digs.append(x >> P)
        x &= (1 << P) - 1
    return digs


def main():
    Kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    print(f"log2(1/C) = {LOG2_INV_C:.1f}   (poly cap constant log6(2/C) = {(1 + LOG2_INV_C) * L2:.0f} digits)")
    print(f"{'K':>2} {'n*':>8} {'a':>8} {'c':>8} {'L_true':>6} {'L_triv':>8} {'L_1/3':>8} {'L_poly':>8} {'delta':>10}  window  xcheck")
    for K in range(4, Kmax + 1):
        n, a, c = critical(K)
        R = pow(3, a, 1 << c)
        assert R == 3 ** a % (1 << c)
        D = (1 << c) - 3 ** a
        assert D > 0
        window = (1 << c) < 2 * 3 ** a  # sep_two_three hypothesis h2
        L = run_of_fives(D, c)
        delta = c * log(2) - a * log(3)
        Ltriv = c * L2
        Lthird = (c + a / 3) * L2 - a * L3
        Lpoly = 436 * log(a) / log(6) + (1 + LOG2_INV_C) * L2
        xc = ""
        if K <= 9:
            digs = alpha_digits_base6(n + L + 3)
            run = 0
            while digs[n + run] == 5:  # digs[n] is digit number n+1
                run += 1
            xc = f"stream={run} {'OK' if run == L else 'MISMATCH'}"
        print(f"{K:>2} {n:>8} {a:>8} {c:>8} {L:>6} {Ltriv:>8.1f} {Lthird:>8.1f} {Lpoly:>8.0f} {delta:>10.3e}  {'yes' if window else 'NO '}  {xc}")


if __name__ == "__main__":
    main()
