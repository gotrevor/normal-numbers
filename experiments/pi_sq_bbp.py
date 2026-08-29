#!/usr/bin/env python3
# Probe: Bailey compendium (2023-04-08) Formula 29 — pi^2 = P(2,16,8,(16,-16,-8,-16,-4,-4,2,0)),
# plus the block-sign check (coefficient sum -30 => blocks negative for k >= 1, so the
# nonneg-kick machine cannot apply; the signed variant is required).  Run 2026-08-29: PASSES (88 digits).
from decimal import Decimal, getcontext
getcontext().prec = 90
# Bailey compendium (2023-04-08) Formula 29: pi^2 = P(2,16,8,(16,-16,-8,-16,-4,-4,2,0))
C = [16, -16, -8, -16, -4, -4, 2, 0]
s = Decimal(0)
for k in range(200):
    blk = sum(Decimal(c) / (Decimal(8*k + j + 1) ** 2) for j, c in enumerate(C))
    s += blk / (Decimal(16) ** k)
# high-precision pi^2 via machin-like arctan (Decimal)
def arctan_inv(x):
    t = Decimal(1) / x; r = t; xx = x*x; n = 3; sgn = -1
    while True:
        t /= xx
        term = t / n
        if term == 0: break
        r += sgn * term; sgn = -sgn; n += 2
    return r
pi = 4 * (4*arctan_inv(Decimal(5)) - arctan_inv(Decimal(239)))
err = abs(s - pi*pi)
print("series =", str(s)[:72]); print("pi^2   =", str(pi*pi)[:72]); print("abs err =", err)
# block sign check
neg = []
for k in range(0, 30):
    blk = sum(Decimal(c) / (Decimal(8*k + j + 1) ** 2) for j, c in enumerate(C))
    if blk < 0: neg.append(k)
print("negative blocks among k<30:", neg[:10], "... (block sum coeff = -30 asymptotically)")
print("PROBE", "PASSES" if err < Decimal(10)**(-60) else "FAILS")
