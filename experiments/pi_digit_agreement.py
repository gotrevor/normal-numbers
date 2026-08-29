#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Probe: true vs surrogate HEX digits of pi (the Lagarias footnote-1
mechanism for pi, companion to pi_digit_mismatch_boundary in PiBBP.lean).

Mechanism: orbit_n = fract(x_n + tau_n) with the BBP tail
tau_n in [3/(16(n+1)^2), 64/(3(8n+1)^2)] -- QUADRATIC windows, so unlike
ln 2 (harmonic kick, ~2 ln N disagreements) the window sum CONVERGES:
  expected total disagreements ~ sum_n 2*tau_n ~ 1  (finite, tiny).
The theorem: a mismatch at n >= 3 forces fract(16*x_n) within
1024/(3(8n+1)^2) of the wrap.

Surrogate recursion (exact fixed-point): x_{n+1} = fract(16 x_n + 16*kick_n),
16*kick_n = 64/(8n+1) - 32/(8n+4) - 16/(8n+5) - 16/(8n+6).
Precision: P = 4N + 64 bits (each hex step sheds 4 bits; 64 guard bits).
"""

import math
from mpmath import mp

N = 50_000                     # hex positions
P = 4 * N + 64
ONE = 1 << P

mp.prec = P + 32
t = int(mp.floor(mp.frac(mp.pi) * ONE))   # fract(pi) scaled
x = 0                                     # surrogate x_0 = 0 (empty partial sum)

disagreements = []  # (n, d_true, d_sur, fract16x, bound, in_window)
checkpoints = {200, 1000, 5000, 20_000, 50_000}
cum = {}

for n in range(0, N):
    if n >= 1:
        d_true = (16 * t) >> P
        d_sur = (16 * x) >> P
        if d_true != d_sur:
            f16x = ((16 * x) & (ONE - 1)) / ONE
            bound = 1024 / (3 * (8 * n + 1) ** 2)
            in_win = (n < 3) or (f16x >= 1 - bound)
            disagreements.append((n, d_true, d_sur, f16x, bound, in_win))
    if n in checkpoints:
        cum[n] = len(disagreements)
    # advance both orbits to position n+1
    t = (16 * t) & (ONE - 1)
    k = (64 * ONE) // (8 * n + 1) - (32 * ONE) // (8 * n + 4) \
        - (16 * ONE) // (8 * n + 5) - (16 * ONE) // (8 * n + 6)
    x = (16 * x + k) & (ONE - 1)

print(f"== pi: true vs surrogate hex digit disagreement, N = {N} ==")
print(f"total disagreements: {len(disagreements)}")
pred = sum(2 * (64 / (3 * (8 * m + 1) ** 2) + 3 / (16 * (m + 1) ** 2)) / 2
           for m in range(1, N))
print(f"random-model expectation (sum of ~2*avg tau): ~{pred:.2f}")
print()
print("cumulative count at checkpoints:")
for n in sorted(cum):
    print(f"   {n:>7}  {cum[n]:>4}")
print()
viol = [d for d in disagreements if not d[5]]
print(f"window-forcing violations (n>=3): {len(viol)}"
      + (f"  !!! {viol[:5]}" if viol else "  (all in predicted windows)"))
print()
print("all disagreements (n, true, surrogate, fract(16 x_n), window bound):")
for (n, dt, ds, f16x, bound, ok) in disagreements:
    print(f"   n={n:>6}  {dt:>2} vs {ds:>2}  fract16x={f16x:.8f}  "
          f"1-bound={1 - bound:.8f}  in_window={ok}")
