#!/usr/bin/env python3
"""Gate 5: crude large-base tail (CONDITIONAL on climb <= C; floats, a design estimate, not certified).
Per positive ancestor X (weight >= minpos = 1/3020 of max, children <= 1): windows of base b with
natural level L = X's level + 6c (c <= C) charge X at lag c + j; per natural cell <= 2 windows per stage;
loss at block j <= min(ell 2^(L+6(j+1)) + 2, 128) with ell = 2 r_b b^-n <= 2 r_b 64 2^-L, and zero
until 2^-(L+6(j+1)) <= ell.  usage: tail5_crude.py C B"""
import sys, math
C, B = int(sys.argv[1]), int(sys.argv[2])
SPREAD, G = 3019.56, 1.7 ** 6
def is_pp(b): return any(round(b ** (1 / e)) ** e == b for e in range(2, b.bit_length() + 1))
tot = 0.0
for b in range(B + 1, 200000):
    if is_pp(b): continue
    r = b ** -4.49; stages = math.ceil(6 / math.log2(b))
    s = 0.0
    for j in range(0, 60):
        rel = 2 * r * 64 * 64 ** (j + 1)  # ell * 2^(L+6(j+1)) upper bound
        if rel < 1 and 2 * r * 64 ** (j + 1) < 1 / 64:  # cells surely bigger than the window
            continue
        s += min(rel + 2, 128) / G ** j
    tot += SPREAD * stages * sum(2 * 64 ** c / G ** c for c in range(C + 1)) * s
print(f"C={C} B={B}: crude large-base discounted charge <= {tot:.4g} (budget 9.874655)")
