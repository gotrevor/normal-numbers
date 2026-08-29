#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Probe: the Lagarias footnote-1 problem for ln 2 — density of disagreement
between the TRUE binary digits of ln 2 and the SURROGATE digits read off the
Bailey-Crandall orbit x_{n+1} = fract(2 x_n + 1/(n+1)).

Mechanism under test (the bracket identity orbit_n = fract(x_n + tau_n),
tau_n in [1/(2(n+1)), 1/(n+1)]):
  digit_n(true) != digit_n(surrogate)  FORCES  x_n in
      [1/2 - tau_n, 1/2)   (straddle of the digit boundary)   or
      [1 - tau_n, 1)       (wraparound),
  i.e. a window of total width <= 2/(n+1).  Random-like model then predicts
  cumulative disagreements up to N of ~ 2 ln N  ==> density-0 agreement
  failure, with a log rate.

Questions:
  1. Reproduce the BC-2001 datum: 15 disagreements in the first 200 positions
     (mod indexing convention -- both conventions reported).
  2. Does EVERY disagreement satisfy the window forcing?  (Any violation would
     refute the bracket-derived node before it is frozen -- the costume check's
     empirical cousin.)
  3. Cumulative disagreement count at checkpoints vs 2 ln N.

Arithmetic: fixed-point integers scaled by 2^P, P = N + 64.  The surrogate
recursion loses one bit of accuracy per step (doubling), so P - N = 64 guard
bits bound the final error by ~2^-64 -- far below the 1/(n+1) window scales.
"""

import math
from mpmath import mp

N = 200_000
P = N + 64
ONE = 1 << P
HALF = ONE >> 1

# ln 2 to P bits (integer floor(2^P * ln 2) mod 2^P -> fractional part scale)
mp.prec = P + 32
LN2 = int(mp.floor(mp.log(2) * (1 << P)))  # 0 < ln2 < 1, so this IS the fraction

t = LN2            # true orbit: t/2^P ~ fract(2^n ln 2), n = 0
x = 0              # surrogate:  x_1 = fract(2*0 + 1/1) = 0 handled in-loop
disagreements = []  # (n, x_n_float, which_window, in_window, tau_ok)
count_first_200_at_n = None
checkpoints = {200, 1000, 5000, 20_000, 50_000, 100_000, 200_000}
cum = {}

for n in range(1, N + 1):
    # advance: x_n = fract(2 x_{n-1} + 1/n), t at exponent n
    x = (2 * x + ONE // n) & (ONE - 1)
    t = (2 * t) & (ONE - 1)

    d_true = 1 if t >= HALF else 0
    d_sur = 1 if x >= HALF else 0

    if d_true != d_sur:
        # window forcing check: x within 1/(n+1) below 1/2 or below 1
        w = ONE // (n + 1)
        if x < HALF:
            which = "straddle"
            in_win = (HALF - x) <= w
        else:
            which = "wrap"
            in_win = (ONE - x) <= w
        # tau bracket check: tau = (t - x) mod 1 in [1/(2(n+1)), 1/(n+1)]
        tau = (t - x) & (ONE - 1)
        tau_ok = (ONE // (2 * (n + 1)) - 2 <= tau <= w + 2)  # +-2 ulp slack
        disagreements.append((n, x / ONE, which, in_win, tau_ok))

    if n in checkpoints:
        cum[n] = len(disagreements)

print(f"== ln 2: true vs surrogate digit disagreement, N = {N} ==")
print(f"total disagreements: {len(disagreements)}")
print(f"2 ln N = {2 * math.log(N):.1f}")
print()
print("cumulative count at checkpoints (n, count, count / (2 ln n)):")
for n in sorted(cum):
    print(f"   {n:>7}  {cum[n]:>4}  {cum[n] / (2 * math.log(n)):.2f}")
print()
first200 = [d for d in disagreements if d[0] <= 200]
first200_shift = [d for d in disagreements if d[0] <= 201]
print(f"disagreements in first 200 positions (n<=200): {len(first200)}  "
      f"[BC-2001 datum: 15; n<=201 gives {len(first200_shift)}]")
print()
viol_win = [d for d in disagreements if not d[3]]
viol_tau = [d for d in disagreements if not d[4]]
print(f"window-forcing violations: {len(viol_win)}"
      + (f"  !!! {viol_win[:5]}" if viol_win else "  (all in predicted windows)"))
print(f"tau-bracket violations:    {len(viol_tau)}"
      + (f"  !!! {viol_tau[:5]}" if viol_tau else "  (bracket holds at every disagreement)"))
print()
print("all disagreement positions:")
print("   " + " ".join(str(d[0]) for d in disagreements))
print()
print("last 10 disagreements (n, x_n, window):")
for (n, xf, which, in_win, tau_ok) in disagreements[-10:]:
    print(f"   n={n:>7}  x_n={xf:.10f}  {which:<8}  in_window={in_win}")
