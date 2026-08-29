#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Probe: run structure of binary ln 2, and the kick dynamics of the
Bailey-Crandall surrogate orbit.

Questions:
  1. Do maximal 0-runs / 1-runs at position n grow like O(log n)?  (If yes,
     a run-length theorem far stronger than any irrationality-measure bound
     is empirically live.)
  2. Surrogate mechanics: x_{n+1} = fract(2 x_n + 1/(n+1)).  The climb
     argument says x cannot stay in (0, 1/2) longer than ~log2 n steps
     without wrapping through the pre-sliver window [(1-kick)/2, 1/2).
     How often do wraps happen?  Do wrap-loops chain?
  3. Asymmetry: near 1 the kick can *sustain* 1 - x ~ 1/n (a' = 2a - 1
     fixed point at a = 1).  Does the orbit ever ride that channel?

Exact arithmetic throughout: x_n = (A_n mod L_n)/L_n with L_n = lcm(1..n),
A_n = sum_{k<=n} (L_n/k) 2^{n-k}; true digits from mpmath at high precision.
"""

import math
from mpmath import mp

N_DIGITS = 200_000
N_ORBIT = 4_000

# ---------- true binary digits of ln 2 ----------
mp.prec = N_DIGITS + 64
x = mp.log(2)
digits = []
for _ in range(N_DIGITS):
    x = x * 2
    if x >= 1:
        digits.append(1)
        x -= 1
    else:
        digits.append(0)

def runs(digs, val):
    """maximal runs of `val`: list of (start, length)"""
    out, i, n = [], 0, len(digs)
    while i < n:
        if digs[i] == val:
            j = i
            while j < n and digs[j] == val:
                j += 1
            out.append((i, j - i))
            i = j
        else:
            i += 1
    return out

print("== true binary digits of ln 2 ==")
for val in (0, 1):
    rr = runs(digits, val)
    # record-setting runs: longest seen so far as position advances
    best = 0
    records = []
    for (s, ln) in rr:
        if ln > best:
            best = ln
            records.append((s, ln))
    print(f"-- {val}-runs: {len(rr)} total, records (pos, len, len/log2(pos+2)):")
    for (s, ln) in records:
        print(f"   pos {s:>8}  len {ln:>3}  ratio {ln / math.log2(s + 2):.2f}")

# ---------- exact surrogate orbit ----------
print("\n== surrogate orbit (exact rationals) ==")
L = 1
A = 0
wraps = []          # steps where 2x + kick >= 1 while x < 1/2 (wrap from below-half)
top_rides = []      # steps with 1 - x_n < 4/n (riding the top channel)
near_zero = []      # steps with x_n < 1/(2n) (below kick scale)
prev_half = None
for n in range(1, N_ORBIT + 1):
    # update L = lcm(1..n), A = sum_{k<=n} (L/k) 2^{n-k}
    Lnew = L * n // math.gcd(L, n)
    A = A * 2 * (Lnew // L)
    L = Lnew
    A += L // n
    xnum = A % L  # x_n = xnum / L
    # classify
    if 2 * (L - xnum) < L:  # x > 3/4 not needed; top channel check below
        pass
    if (L - xnum) * n < 4 * L:
        top_rides.append(n)
    if 2 * xnum * n < L:
        near_zero.append(n)

print(f"near-zero steps (x_n < 1/(2n)): {len(near_zero)}; first 30: {near_zero[:30]}")
print(f"top-channel steps (1-x_n < 4/n): {len(top_rides)}; first 40: {top_rides[:40]}")

# longest consecutive stretch in each channel
def stretches(idxs):
    out = []
    if not idxs:
        return out
    s = p = idxs[0]
    for i in idxs[1:]:
        if i == p + 1:
            p = i
        else:
            out.append((s, p - s + 1))
            s = p = i
    out.append((s, p - s + 1))
    return sorted(out, key=lambda t: -t[1])[:8]

print(f"longest top-channel stretches (start, len): {stretches(top_rides)}")
print(f"longest near-zero stretches  (start, len): {stretches(near_zero)}")
