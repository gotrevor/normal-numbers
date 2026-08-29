#!/usr/bin/env -S uv run --quiet --with mpmath --with sympy python3
"""Probe: the Wieferich-coincidence census (R3 forcing target, pre-freeze).

The D8 unique-candidate certificate says: a zero-run of length k at position n
with lcm(1..n) < 2^k forces
    lnTwoRes n = ceil(latticeCenter n) = L + A - floor(L * 2^n * ln 2)
(one-run candidate: that - 1), where A = lnTwoNum n, L = lcmRange n.

At n = p-1 the Fermat-quotient bridge (lnTwoNum_modEq_fermatQuotient, proved)
gives A == L * q_p(2) (mod p).  So a super-threshold run at p-1 forces the
per-p WIEFERICH-TYPE COINCIDENCE
    q_p(2) == w_p (mod p),   w_p := (C * L^-1 + floor(A/L)) mod p,
with C the run candidate.  This census computes, for every odd prime p < P_MAX:
  - the actual q_p(2),
  - both forced values w_p (zero-run and one-run candidates),
  - whether the coincidence holds (mod-p shadow of the certificate identity).

Model: w_p is decorrelated from q_p(2), so per-p coincidence probability ~1/p
per run type; expected total ~ 2*sum(1/p) ~ 2*(loglog P + M - 1/2).  The
exclusion node to freeze (LnTwoQuotientMiss) needs only: every dyadic window
(n, 2n] eventually contains a non-coincident prime.

Everything is exact integer arithmetic; ln 2 enters as a fixed-point integer
with a verified guard margin.

Self-tests (teeth):
  1. A_n recurrence vs direct sum at n = 10, 37.
  2. C == ceil(L*(1 - 2^n*(ln2 - S_n))) via independent mpmath at n = 10, 30, 100.
  3. The bridge A == L*q_p(2) (mod p) asserted for EVERY p (exact big-int A).
  4. Elementary short-sum evaluation of A_n mod p for p <= n (n >= p case),
     checked at (n,p) = (100,7), (1000,31), (5000,4999).
"""

import sys
from math import gcd
from sympy import primerange, isprime, factorint
import mpmath

P_MAX = 20_000
N_MAX = P_MAX - 1          # largest n = p-1 we need
B = 51_200                 # fixed-point bits for ln 2 (bits(L<<n) ~ 2.45n + guard)

mpmath.mp.prec = B + 64
LN2_FP = int(mpmath.floor(mpmath.ldexp(mpmath.ln(2), B)))  # floor(2^B * ln 2)


def direct_A(n: int) -> tuple[int, int]:
    """Direct O(n^2) computation of (L_n, A_n) from the definition."""
    L = 1
    for j in range(1, n + 1):
        L = L * j // gcd(L, j)
    A = sum((L // j) * (1 << (n - j)) for j in range(1, n + 1))
    return L, A


def candidate_C(n: int, L: int, A: int) -> tuple[int, int]:
    """(C, guard_bits): C = L + A - floor(L * 2^n * ln2); guard = distance of
    the fixed-point product from an integer, in bits (should be >> 64)."""
    prod = (L << n) * LN2_FP
    T = prod >> B
    frac = prod & ((1 << B) - 1)
    guard = min(frac, (1 << B) - frac).bit_length()
    return L + A - T, guard


def short_sum_A_mod_p(n: int, p: int) -> int:
    """Elementary evaluation of A_n mod p for p <= n: only terms with
    nu_p(j) = nu_p(L_n) survive."""
    e = 1
    while p ** (e + 1) <= n:
        e += 1
    pe = p ** e
    # L_n / pe mod p: build lcm(1..n) with p-part removed
    Lred = 1
    for q in primerange(2, n + 1):
        f = 1
        while q ** (f + 1) <= n:
            f += 1
        if q == p:
            f -= e  # remove the full p-part
        if f > 0:
            Lred = (Lred * pow(q, f, p)) % p
    acc = 0
    m = 1
    while m * pe <= n:
        if m % p != 0:
            j = m * pe
            acc = (acc + Lred * pow(m, -1, p) * pow(2, n - j, p)) % p
        m += 1
    return acc


def main() -> None:
    # --- self-test 1: recurrence vs direct sum -------------------------------
    for n_test in (10, 37):
        Ld, Ad = direct_A(n_test)
        L, A = 1, 0
        for n in range(1, n_test + 1):
            fac = factorint(n)
            r = list(fac)[0] if len(fac) == 1 else 1
            L *= r
            A = 2 * r * A + L // n
        assert (L, A) == (Ld, Ad), f"recurrence broken at n={n_test}"
    print("self-test 1 OK: A_n recurrence matches definition (n=10, 37)")

    # --- self-test 2: C == ceil(latticeCenter) via independent mpmath -------
    with mpmath.workprec(2000):
        for n_test in (10, 30, 100):
            L, A = direct_A(n_test)
            S = mpmath.fsum(mpmath.mpf(1) / (k * mpmath.mpf(2) ** k)
                            for k in range(1, n_test + 1))
            tau = mpmath.mpf(2) ** n_test * (mpmath.ln(2) - S)
            center = L * (1 - tau)
            C, guard = candidate_C(n_test, L, A)
            assert C == int(mpmath.ceil(center)), f"candidate mismatch at n={n_test}"
            assert guard > 64, f"precision guard too thin at n={n_test}"
    print("self-test 2 OK: C = ceil(latticeCenter) at n=10, 30, 100")

    # --- main sweep ----------------------------------------------------------
    L, A = 1, 0
    coincidences = []
    wieferich = []
    n_primes = 0
    sum_inv_p = 0.0
    min_guard = B
    short_sum_checks = {(100, 7), (1000, 31), (5000, 4999)}

    for n in range(1, N_MAX + 1):
        fac = factorint(n)
        r = list(fac)[0] if len(fac) == 1 else 1
        L *= r
        A = 2 * r * A + L // n

        for (nc, pc) in short_sum_checks:
            if n == nc:
                got = short_sum_A_mod_p(nc, pc)
                assert got == A % pc, f"short-sum formula broken at (n,p)=({nc},{pc})"
                print(f"self-test 4 OK: elementary short sum == A_n mod p at (n,p)=({nc},{pc})")

        p = n + 1
        if not isprime(p) or p == 2:
            continue
        n_primes += 1
        sum_inv_p += 1 / p

        q = ((pow(2, p - 1, p * p) - 1) // p) % p
        # self-test 3: the bridge, exactly
        assert (A - L * q) % p == 0, f"bridge FAILED at p={p}"
        if q == 0:
            wieferich.append(p)

        C, guard = candidate_C(n, L, A)
        min_guard = min(min_guard, guard)
        s = A // L
        Linv = pow(L % p, -1, p)
        w_zero = ((C % p) * Linv + s) % p
        w_one = (((C - 1) % p) * Linv + s) % p
        R = A % L
        # consistency: mod-p shadow of the certificate identity
        assert ((R - C) % p == 0) == (q == w_zero)
        assert ((R - (C - 1)) % p == 0) == (q == w_one)
        if q == w_zero:
            coincidences.append((p, "zero-run", q, w_zero))
        if q == w_one:
            coincidences.append((p, "one-run", q, w_one))

    print("self-test 3 OK: bridge A == L*q_p(2) (mod p) exact for all "
          f"{n_primes} odd primes < {P_MAX}")
    print(f"precision: min guard margin {min_guard} bits (need > 64)")
    print()
    print(f"census over {n_primes} odd primes p < {P_MAX}:")
    print(f"  Wieferich primes recovered (q_p(2)=0): {wieferich}")
    exp = 2 * sum_inv_p
    print(f"  expected coincidences (model 2/p per prime): {exp:.2f}")
    print(f"  observed coincidences: {len(coincidences)}")
    for p, kind, q, w in coincidences:
        print(f"    p={p}: {kind} coincidence, q_p(2) = w_p = {q}")
    if not coincidences:
        print("    (none)")
    print()
    print("interpretation: each coincident p is a 'Wieferich prime of the ln-2")
    print("run problem' — the only primes where the R3 exclusion node cannot cap")
    print("runs at p-1.  The node LnTwoQuotientMiss needs one NON-coincident")
    print("prime per dyadic window; count the worst window observed:")
    bad = sorted(p for p, _, _, _ in coincidences)
    if bad:
        for lo in bad:
            window = [b for b in bad if lo < b <= 2 * lo]
            print(f"    window ({lo}, {2*lo}]: {len(window)} coincident of "
                  f"{sum(1 for r in primerange(lo + 1, 2 * lo + 1))} primes")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
