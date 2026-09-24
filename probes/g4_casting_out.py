#!/usr/bin/env -S uv run --quiet --with gmpy2 python3
"""Casting out (b−1) on G4 = Σ_p 1/(bᵖ−1) = Σ_m ω(m) b^(−m)  (2026-09-23).

Identity (hand-derived, casting out nines): for any real x, the base-b digits d_{n+1..n+L} satisfy
    Σ d_i ≡ ⌊b^{n+L}x⌋ − ⌊bⁿx⌋  (mod b−1),
and for x = Σ ω(m) b^(−m), ⌊b^N x⌋ = Σ_{m≤N} ω(m) b^{N−m} + c_N with c_N = ⌊Σ_{m>N} ω(m) b^{N−m}⌋, so
    window digit sum ≡ Σ_{m∈(n,n+L]} ω(m) + c_{n+L} − c_n   (mod b−1).
Carries enter only at the two window ENDS, unlike the digit-parity reading refuted in Maze
("G4 sectors as digit characters").  This probe (1) checks the identity against true digits,
(2) tabulates the carry c_N, (3) prints the residue frequencies of window digit sums mod b−1.
Usage: g4_casting_out.py [N] [b ...] [--divisor]
  --divisor  use d(m) instead of ω(m): the Erdős–Borwein constant Σ_n 1/(bⁿ−1) = Σ_m d(m) b^(−m).
             d(m) is divisible by 2^ω(m) for squarefree-ish m, so for b−1 a power of two the
             window digit sum mod b−1 is carried almost entirely by the boundary carries.
"""
import sys
from collections import Counter
import gmpy2

DIV = "--divisor" in sys.argv
args = [a for a in sys.argv[1:] if not a.startswith("--")]
N = int(args[0]) if args else 200000
BASES = [int(a) for a in args[1:]] or [3, 5]
G = 80  # guard positions
M = N + G

omega = [0] * (M + 2)
if DIV:  # divisor count d(m); the variable keeps its name so the rest of the probe is shared
    for a in range(1, M + 2):
        for k in range(a, M + 2, a):
            omega[k] += 1
else:
    for p in range(2, M + 2):
        if omega[p] == 0:
            for k in range(p, M + 2, p):
                omega[k] += 1


def value(seq, b):
    """Σ seq[i] b^(len−1−i) by divide and conquer."""
    if len(seq) <= 64:
        v = gmpy2.mpz(0)
        for s in seq:
            v = v * b + s
        return v
    h = len(seq) // 2
    return value(seq[:h], b) * gmpy2.mpz(b) ** (len(seq) - h) + value(seq[h:], b)


for b in BASES:
    q = b - 1
    X = value(omega[1:M + 1], b)                  # ⌊b^M x⌋ up to the tail beyond M (< 1 unit)
    s = gmpy2.digits(X, b).rjust(M, "0")
    assert len(s) <= M + 30
    top = len(s) - M                              # integer-part digits (x > 1 possible for b small)
    d = [int(ch, 36) for ch in s[top:top + N]]    # fractional digits d_1..d_N
    # carries from the definition, float tail over 60 terms
    c = [0] * (N + 1)
    for n in range(N + 1):
        t = sum(omega[m] * b ** (n - m) for m in range(n + 1, n + 61))
        c[n] = int(t)
    # (1) identity check at L = 1..8
    bad = 0
    for L in range(1, 9):
        for n in range(0, N - L - 1):
            lhs = sum(d[n:n + L]) % q
            rhs = (sum(omega[n + 1:n + L + 1]) + c[n + L] - c[n]) % q
            bad += lhs != rhs
    cc = Counter(c)
    print(f"b={b}: identity mismatches over L=1..8: {bad};  carry c_N distribution: "
          + ", ".join(f"{k}:{v / (N + 1):.3f}" for k, v in sorted(cc.items())))
    for L in (1, 2, 3, 5, 8):
        n_ = N - L
        r = Counter(sum(d[n:n + L]) % q for n in range(n_))
        print(f"   L={L}: window digit sum mod {q}: " + " ".join(f"{r[k] / n_:.4f}" for k in range(q)))
