#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Numeric tripwire for `NormalNumbers.LevinSparse` (base-2 half of the headline).

Levin's alpha (Acta Arith. 88 (1999), Theorem 2, q = 2) is built exactly from eq. (7)-(9):
digit n_m + n*2^m + i of alpha is d_i(n) = XOR_{j : (i-1)&(j-1) = 0} e_j(n)  (Pascal mod 2 via
Lucas, e_j(n) = bit j-1 of n), n_1 = 0, n_m = sum_{r<m} 2^r 2^(2^r).  Orbit points
{2^n x} = .b_{n+1} b_{n+2} ... are read off a 53-bit sliding window of the exact binary digits
(alpha + y is added as big integers, so carries are exact up to the 2^-80 truncation).

Star discrepancy D*_N = sup_{c in [0,1]} |#{n<N : u_n < c}/N - c|  (the Lean `DiscLe`),
computed exactly from the sorted points: max_i max(i/N - u_(i), u_(i) - (i-1)/N).

Rows:
  * levin        : Levin's alpha.  Expect N*D*/log^2 N bounded.
  * champernowne : known-answer control (Schiffer: D* >= K/log N), so N*D*/log^2 N must blow up.
  * levin+sparse : alpha + y, y a fair-coin point of C(S), S = expSet = {ceil(e^{j/100}) : j >= 1}
                   (3 seeds).  Checks the proved-on-paper shift bound
                   D*(alpha+y) <= 2 D*(alpha) + 2/N + #B/N  (`discLe_add_bldPoint`, B exact),
                   and the Lean budget (log2 N + 2) * S(1, N + log2 N + 2) / N.
  * levin+dense  : control, fair coins at all even positions (not sparse), 3 seeds, min shown:
                   D* reverts to the random N^{-1/2} scale (sqrtN*D* = Theta(1)), N*D*/log^2 N grows.
  * levin+cancel : control, y = 2^-M floor(2^M fract(-alpha)) (dense digits cancelling alpha):
                   alpha + y is within 2^-M of an integer, D* ~ 1 (`exists_not_isNormal_two_dense`).

Run: probes/levin_sparse_probe.py [log2_Nmax]   (default 16, ~5 s; 20 takes ~1 min)
"""
import math
import sys

import numpy as np

LOGN = int(sys.argv[1]) if len(sys.argv) > 1 else 16
NMAX = 1 << LOGN
P = 53
M = NMAX + P + 80  # number of binary digits kept


def levin_bits(M):
    bits = np.zeros(M + 1, dtype=np.uint8)  # bits[k] = digit k (weight 2^-k), k >= 1
    m, nm = 1, 0
    while nm < M:
        w = 1 << m  # word length 2^m
        # Pascal mod 2 mask for row i: j with (i-1)&(j-1) == 0
        for n in range(1 << w):
            base = nm + n * w
            if base >= M:
                break
            for i in range(1, w + 1):
                pos = base + i
                if pos > M:
                    break
                acc = 0
                for j in range(1, w + 1):
                    if ((i - 1) & (j - 1)) == 0:
                        acc ^= (n >> (j - 1)) & 1
                bits[pos] = acc
        nm += w * (1 << w)
        m += 1
    return bits


def levin_bits_fast(M):
    """Vectorised version of levin_bits (same output; cross-checked on a prefix below)."""
    bits = np.zeros(M + 1, dtype=np.uint8)
    m, nm = 1, 0
    while nm < M:
        w = 1 << m
        nwords = min(1 << w, (M - nm) // w + 1)
        n = np.arange(nwords, dtype=np.int64)
        e = ((n[:, None] >> np.arange(w)[None, :]) & 1).astype(np.uint8)  # e[:, j-1]
        mask = ((np.arange(w)[:, None] & np.arange(w)[None, :]) == 0).astype(np.uint8)  # [i-1, j-1]
        d = (e @ mask.T) & 1  # d[n, i-1]
        flat = d.reshape(-1)
        lo, hi = nm + 1, min(nm + flat.size, M)
        bits[lo:hi + 1] = flat[: hi - lo + 1]
        nm += w * (1 << w)
        m += 1
    return bits


def champernowne_bits(M):
    s = []
    k = 1
    while len(s) < M:
        s.extend(int(c) for c in bin(k)[2:])
        k += 1
    bits = np.zeros(M + 1, dtype=np.uint8)
    bits[1:] = s[:M]
    return bits


def to_int(bits):
    return int("".join("1" if b else "0" for b in bits[1:]), 2)


def from_int(X):
    X %= 1 << M  # fractional part
    s = bin(X)[2:].zfill(M)
    bits = np.zeros(M + 1, dtype=np.uint8)
    bits[1:] = np.frombuffer(s.encode(), dtype=np.uint8) - 48
    return bits


def orbit(bits):
    w = 0.5 ** np.arange(1, P + 1)
    win = np.lib.stride_tricks.sliding_window_view(bits[1:].astype(np.float64), P)
    return win[:NMAX] @ w  # u_n = {2^n x}, n = 0..NMAX-1


def star_disc(u, N):
    s = np.sort(u[:N])
    i = np.arange(1, N + 1)
    return float(max(np.max(i / N - s), np.max(s - (i - 1) / N)))


def exp_set(limit):
    S, j = set(), 1
    while True:
        k = math.ceil(math.exp(j / 100))
        if k > limit:
            return S
        S.add(k)
        j += 1


def sparse_bits(S, rng):
    bits = np.zeros(M + 1, dtype=np.uint8)
    for k in S:
        if k <= M:
            bits[k] = rng.integers(0, 2)
    return bits


def bad_count(S, N):
    L = int(math.log2(N)) + 1  # Nat.log 2 N + 1
    Sa = np.array(sorted(S))
    B = 0
    for n in range(N):
        lo = np.searchsorted(Sa, n + 1)
        if lo < len(Sa) and Sa[lo] <= n + L:
            B += 1
    return B


def main():
    assert np.array_equal(levin_bits(3000)[:3001], levin_bits_fast(3000)[:3001]), "levin construction mismatch"
    A = levin_bits_fast(M)
    S = exp_set(M)
    Ns = [1 << k for k in range(6, LOGN + 1)]
    uL = orbit(A)
    uC = orbit(champernowne_bits(M))
    XA = to_int(A)
    rng = np.random.default_rng(20261003)
    sparse_u = [orbit(from_int(XA + to_int(sparse_bits(S, rng)))) for _ in range(3)]
    dense_u = []
    for _ in range(3):
        dense = np.zeros(M + 1, dtype=np.uint8)
        dense[2::2] = rng.integers(0, 2, size=dense[2::2].size)
        dense_u.append(orbit(from_int(XA + to_int(dense))))
    uX = orbit(from_int(XA + ((1 << M) - XA)))  # alpha + fract(-alpha) truncated: an integer mod 1
    print(f"log2N  N*D*/log^2N: levin  champ | sparse(max3) dense(min3) cancel |"
          f" sqrtN*D*: levin sparse dense |  D*(a)   D*(a+y)  shift-bound  #B/N   Lean-budget")
    worst_ratio = 0.0
    for N in Ns:
        L2 = math.log(N) ** 2
        dL = star_disc(uL, N)
        dC = star_disc(uC, N)
        dS = max(star_disc(u, N) for u in sparse_u)
        dD = min(star_disc(u, N) for u in dense_u)
        dX = star_disc(uX, N)
        B = bad_count(S, N)
        shift = 2 * dL + 2 / N + B / N
        sIcc = sum(1 for k in S if 1 <= k <= N + int(math.log2(N)) + 2)
        budget = (int(math.log2(N)) + 2) * sIcc / N
        assert dS <= shift + 1e-12, f"shift bound violated at N={N}"
        worst_ratio = max(worst_ratio, dS / shift)
        r = math.sqrt(N)
        print(f"{int(math.log2(N)):5d}  {N*dL/L2:13.3f} {N*dC/L2:7.2f} | {N*dS/L2:12.2f} {N*dD/L2:11.2f}"
              f" {N*dX/L2:7.1f} | {r*dL:15.3f} {r*dS:6.3f} {r*dD:5.3f} |"
              f" {dL:.2e} {dS:.2e} {shift:10.3f} {B/N:6.3f} {budget:9.3f}")
    print(f"shift bound held at every N (max D*(a+y)/bound = {worst_ratio:.3f}); #expSet∩[1,N] at N=2^{LOGN}:"
          f" {sum(1 for k in S if k <= NMAX)} (100 ln N = {100*math.log(NMAX):.0f})")


if __name__ == "__main__":
    main()
