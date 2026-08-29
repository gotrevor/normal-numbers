#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Probe: e enters the kick framework (threshold-kick / factorial machine).

New structure claimed (session 2026-08-29): split e = head + tail at
M(n) := min{m : 2^n < (m+1)!}.  Then

  x_n := frac(2^n * sum_{k<=M} 1/k!) = frac(2^(n-v) * A(M) / odd(M!)),
      A(M) = sum_{k<=M} M!/k!  (OEIS A000522: A(M) = M*A(M-1) + 1,
      A(M) mod p = A(M mod p) mod p — RIGID residues),
  tau_n := 2^n * sum_{k>M} 1/k!  in  [1/(M+1), 1 + 2/(M+1)),
  frac(2^n e) = frac(x_n + tau_n).

tau-floor consequence (the e-dichotomy, all elementary): a zero-run of length
j > log2(M(n)+1) + 1 at position n forces x_n into a width-2^(1-j) window
around 1 - tau_n (mod 1) — the moving sliver.  Threshold ~ log2 n - log2 ln n,
BELOW ln 2's log2(2(n+1)); and the same split works in EVERY base b
(M_b(n) := min{m : b^n < (m+1)!}), unlike BBP machinery which is base-locked.

This probe:
  1. verifies the tau bracket at n = 100, 1000, 10000 (mpmath, exact-side);
  2. verifies A(M) recurrence + mod-p periodicity at random points;
  3. computes 200k binary digits of e, lists record 0/1-runs, len/log2(pos)
     (random model predicts ~1.0), and checks every run against the threshold
     log2(M(n)+1) + 1 — super-threshold runs are the sliver events.
"""

import sys
from math import lgamma, log2, log
import random
import mpmath

B = 200_064  # fixed-point bits (200k usable + guard)


def M_of(n: int, base_log2: float = 1.0) -> int:
    """min m with (m+1)! > 2^(n * base_log2), via lgamma."""
    target = n * base_log2 * log(2)
    m = 1
    # crude doubling then linear walk-back; lgamma(m+2) = ln((m+1)!)
    while lgamma(m + 2) <= target:
        m *= 2
    lo = m // 2
    while lgamma(lo + 2) <= target:
        lo += 1
    return lo


def main() -> None:
    # --- 1. tau bracket -------------------------------------------------------
    print("tau_n = 2^n * sum_{k>M} 1/k!  vs bracket [1/(M+1), 1 + 2/(M+1)):")
    for n in (100, 1000, 10000):
        M = M_of(n)
        with mpmath.workprec(n + 200):
            head = mpmath.fsum(mpmath.mpf(1) / mpmath.factorial(k)
                               for k in range(0, M + 1))
            tau = mpmath.mpf(2) ** n * (mpmath.e - head)
        lo, hi = 1.0 / (M + 1), 1.0 + 2.0 / (M + 1)
        ok = lo <= tau < hi
        print(f"  n={n:>6}: M={M:>5}, tau={float(tau):.6f}, "
              f"bracket [{lo:.6f}, {hi:.6f}) -> {'OK' if ok else 'VIOLATION'}")
        assert ok

    # --- 2. A(M) rigidity -----------------------------------------------------
    random.seed(7)
    for _ in range(5):
        p = random.choice([5, 13, 101, 997])
        M = random.randrange(2 * p, 40 * p)
        a = 1
        for m in range(1, M + 1):
            a = (m * a + 1) % p
        a_small = 1
        for m in range(1, M % p + 1):
            a_small = (m * a_small + 1) % p
        assert a == a_small, f"A(M) mod p periodicity broken at (M,p)=({M},{p})"
    print("A(M) mod p = A(M mod p) mod p: OK (random spot checks)")

    # --- 3. binary digits of e, runs, threshold -------------------------------
    s, t, k = 0, 1 << B, 0
    while t:
        s += t
        k += 1
        t //= k
    frac_fp = s - (2 << B)  # e = 2.71828..., fractional part
    bits = bin(frac_fp)[2:].zfill(B)[: B - 64]  # drop guard bits

    print(f"\nbinary digits of e computed: {len(bits)} bits (terms used: {k})")
    records = {"0": [], "1": []}
    best = {"0": 0, "1": 0}
    sliver_events = []
    i = 0
    n_bits = len(bits)
    while i < n_bits:
        c = bits[i]
        j = i
        while j < n_bits and bits[j] == c:
            j += 1
        run_len, pos = j - i, i + 1  # 1-indexed position of run start
        if run_len > best[c]:
            best[c] = run_len
            records[c].append((pos, run_len))
        if pos > 4:
            thr = log2(M_of(pos) + 1) + 1
            if run_len > thr:
                sliver_events.append((pos, c, run_len, round(thr, 1)))
        i = j

    for c, name in (("0", "0-runs"), ("1", "1-runs")):
        print(f"\nrecord {name} (pos, len, len/log2(pos)):")
        for pos, ln in records[c]:
            ratio = ln / log2(pos) if pos > 1 else float("inf")
            print(f"  ({pos:>7}, {ln:>2})  ratio {ratio:.2f}")

    print(f"\nsliver events (runs exceeding threshold log2(M(n)+1)+1): "
          f"{len(sliver_events)}")
    for pos, c, ln, thr in sliver_events[:20]:
        print(f"  pos {pos:>7}: {ln} {'zeros' if c == '0' else 'ones'} "
              f"(threshold {thr})")
    print("\n(each sliver event = position where the surrogate x_n must sit in")
    print(" the moving window around 1 - tau_n; cf. ln 2's 29 visits/4000 steps)")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
