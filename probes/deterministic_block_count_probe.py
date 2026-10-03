#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Numeric tripwire for `IsDeterministicSeq` (DeterministicBD.lean, B-D 2506.12929v1 Def. 3.8).

Counts p(m) = #distinct length-m blocks in a length-L prefix of three binary sequences and prints
log2 p(m) / m, the block-count exponent that Def. 3.8 asks to be small (C_w(eps, m) < 2^{eps m}).
With S = {} (no exceptional set) p(m) is an upper bound for C_w(eps, m).

  (i)  Fibonacci word (fixed point of 0 -> 01, 1 -> 0), Sturmian: p(m) = m + 1 EXACTLY
       (Morse-Hedlund; hand check m = 1: {0,1}; m = 2: {00,01,10} since 11 never occurs; m = 3:
       {001,010,100,101} since 000, 011, 110, 111 never occur).
  (ii) Thue-Morse t(n) = popcount(n) mod 2.  Hand: p(1) = 2, p(2) = 4 (0110 1001 has 01,11,10,00),
       p(3) = 6 (overlap-free, so 000 and 111 are excluded, the other six all occur in
       0110100110010110).  Reference values p(4..8) = 10, 12, 16, 20, 22 from OEIS A005942
       (Brlek 1989; de Luca-Varricchio 1989), and p(m) <= 4m for m >= 1 (both refs).
  (iii) CONTROL, positive entropy: pseudo-random fair bits (numpy PCG64, seed 20261003).  The
       expected number of distinct blocks among L - m + 1 uniform windows is
       E(m) = 2^m (1 - (1 - 2^-m)^(L-m+1))  (windows are not independent, but the formula is the
       standard occupancy approximation; asserted only to 2%).  So log2 p(m) / m -> 1.

Expected: (i), (ii) exponent -> 0 (deterministic, zero entropy); (iii) exponent ~ 1.
Run: probes/deterministic_block_count_probe.py   (exit 0 = all assertions pass)
"""
import math
import numpy as np

L = 1 << 25          # prefix length
MMAX = 24
TM_REF = {1: 2, 2: 4, 3: 6, 4: 10, 5: 12, 6: 16, 7: 20, 8: 22}  # hand + OEIS A005942


def fibonacci_word(n):
    a, b = np.array([0], np.uint8), np.array([0, 1], np.uint8)  # S0 = 0, S1 = 01, Sk = S(k-1) S(k-2)
    while len(b) < n:
        a, b = b, np.concatenate([b, a])
    return b[:n]


def thue_morse(n):
    idx = np.arange(n, dtype=np.uint32)
    par = np.zeros(n, np.uint8)
    while idx.any():
        par ^= (idx & 1).astype(np.uint8)
        idx >>= 1
    return par


def block_counts(bits, mmax):
    """p(m) for m = 1..mmax, via incremental m-bit window codes and a 2^m bitmap."""
    n = len(bits)
    codes = bits[: n].astype(np.uint32)
    out = {}
    for m in range(1, mmax + 1):
        if m > 1:
            codes = (codes[:-1] << 1) | bits[m - 1:].astype(np.uint32)
        seen = np.zeros(1 << m, dtype=bool)
        seen[codes] = True
        out[m] = int(seen.sum())
    return out


def main():
    rng = np.random.Generator(np.random.PCG64(20261003))
    seqs = {
        "fibonacci": fibonacci_word(L),
        "thue-morse": thue_morse(L),
        "random": rng.integers(0, 2, size=L, dtype=np.uint8),
    }
    # sanity on generators (hand): Fibonacci word starts 0100101001001, Thue-Morse 0110100110010110
    assert "".join(map(str, seqs["fibonacci"][:13])) == "0100101001001"
    assert "".join(map(str, seqs["thue-morse"][:16])) == "0110100110010110"

    counts = {k: block_counts(v, MMAX) for k, v in seqs.items()}
    print(f"L = {L}")
    print(f"{'m':>3} | {'fib p':>6} {'exp':>6} | {'TM p':>6} {'exp':>6} | {'rand p':>9} {'exp':>6} {'E(m)':>10}")
    for m in range(1, MMAX + 1):
        f, t, r = counts["fibonacci"][m], counts["thue-morse"][m], counts["random"][m]
        e = (1 << m) * (1 - (1 - 2.0 ** -m) ** (L - m + 1))
        print(f"{m:>3} | {f:>6} {math.log2(f)/m:6.3f} | {t:>6} {math.log2(t)/m:6.3f} | "
              f"{r:>9} {math.log2(r)/m:6.3f} {e:10.0f}")
        assert f == m + 1, (m, f)                              # Sturmian, exact
        if m in TM_REF:
            assert t == TM_REF[m], (m, t)
        assert t <= 4 * m, (m, t)
        assert r <= min(1 << m, L - m + 1)                     # trivial upper bound
        assert abs(r - e) <= 0.02 * e, (m, r, e)               # occupancy approximation
    # exponents: deterministic ones go to 0, control stays near 1
    assert math.log2(counts["fibonacci"][MMAX]) / MMAX < 0.2
    assert math.log2(counts["thue-morse"][MMAX]) / MMAX < 0.3
    assert all(math.log2(counts["random"][m]) / m > 0.98 for m in range(1, MMAX + 1))
    print("OK: deterministic exponents -> 0, positive-entropy control ~ 1")


if __name__ == "__main__":
    main()
