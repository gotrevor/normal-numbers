#!/usr/bin/env -S uv run --quiet python3
"""Probe: does the carry layer preserve the depth-1 digit character of G4?

DESIGN-2026-09-20-walsh-weyl-bridge.md §4 claims (75%) that G4's base-4 digit characters
e(k*d_n/4) are the circle-side SD/Chowla sector split of the 2026-09-19 verdict, with
k = 2 -- i.e. (-1)^(d_n) -- standing in for the bounded multiplicative function
(-1)^(omega(n)).  That identification is only legitimate if CARRIES do not break it:
G4 = sum_n omega(n)/4^n has omega(n) > 3 for n with many distinct prime factors
(omega = 4 first at n = 210), so the base-4 digit d_n is NOT omega(n) mod 4 in general.

This probe computes the TRUE base-4 digits of G4 by exact integer arithmetic and measures

  (a) the density of positions where d_n != omega(n) mod 4        (carry-disturbed positions)
  (b) the parity correlation  (1/N) sum (-1)^(d_n) * (-1)^(omega(n))
  (c) the depth-1 digit-character means (1/N) sum e(k d_n / 4) for k = 1, 2, 3
  (d) the same for the carry-free surrogate omega(n) mod 4, for comparison

Reading: (b) near 1 and (a) near 0 means the identification survives and the sector story
stands.  (b) bounded away from 1 means the carry layer is a real obstruction and the
design doc's claim must be weakened.
"""
import sys
from cmath import exp as cexp
from math import pi


def omega_sieve(N):
    """omega(n) = number of DISTINCT prime factors, for n <= N."""
    w = [0] * (N + 1)
    for p in range(2, N + 1):
        if w[p] == 0:  # p is prime
            for m in range(p, N + 1, p):
                w[m] += 1
    return w


def g4_base4_digits(N, guard=64):
    """True base-4 digits d_1..d_N of G4 = sum_{n>=1} omega(n)/4^n, exact integers.

    Scale by 4^P with P = N + guard: floor(G4 * 4^P) = sum_{n<=P} omega(n) * 4^(P-n)
    plus a tail < 4^-guard worth of digits, which cannot reach position N.
    """
    P = N + guard
    w = omega_sieve(P)
    total = 0
    for n in range(1, P + 1):
        if w[n]:
            total += w[n] << (2 * (P - n))
    digs = []
    for n in range(1, N + 1):
        digs.append((total >> (2 * (P - n))) & 3)
    return digs, w


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    digs, w = g4_base4_digits(N)
    om = [w[n] & 3 for n in range(1, N + 1)]
    omraw = [w[n] for n in range(1, N + 1)]

    disturbed = sum(1 for i in range(N) if digs[i] != om[i])
    par = sum(1 if (digs[i] & 1) == (omraw[i] & 1) else -1 for i in range(N)) / N
    agree_par = sum(1 for i in range(N) if (digs[i] & 1) == (omraw[i] & 1)) / N
    big = sum(1 for n in range(1, N + 1) if w[n] > 3)

    print(f"N = {N}")
    print(f"  positions with omega(n) > 3 (carry sources) : {big}  ({big/N:.6f})")
    print(f"  (a) carry-disturbed digits d_n != omega mod 4: {disturbed}  ({disturbed/N:.6f})")
    print(f"  (b) parity correlation  <(-1)^d_n (-1)^omega> : {par:+.6f}   "
          f"(agreement {agree_par:.6f})")
    print("  (c) depth-1 digit-character means of the TRUE digits:")
    for k in (1, 2, 3):
        m = sum(cexp(2j * pi * k * d / 4) for d in digs) / N
        print(f"        k={k}:  |mean| = {abs(m):.6f}   mean = {m.real:+.5f}{m.imag:+.5f}i")
    print("  (d) same for the carry-free surrogate omega(n) mod 4:")
    for k in (1, 2, 3):
        m = sum(cexp(2j * pi * k * d / 4) for d in om) / N
        print(f"        k={k}:  |mean| = {abs(m):.6f}   mean = {m.real:+.5f}{m.imag:+.5f}i")
    print(f"  digit distribution (true): "
          f"{[round(sum(1 for d in digs if d == j)/N, 4) for j in range(4)]}")


if __name__ == "__main__":
    main()
