#!/usr/bin/env python3
"""Gate 5 lap 3: refutation witness for node 1 (APKillUniform449 6 (37/20)) at the concentrated
cell (13, 808).  Its positive Good descendants at level 25 are the 4 consecutive cells 1460..1463
(relative hull 2^-10), so ONE base-5 stage-9 window (spacing 5^-9 > 2^-19 = 2^-(k+6), so s = 6 is
allowed) placed inside that sliver captures far more than C * 2 * 5^-4.49 of the descendant mass.
Exact: Good449 + weights by tail5_measure (integer arithmetic), window radius 5^-4.49 enclosed at
60 digits; the window is placed with a rational offset and only cells CERTAINLY inside count.
usage: tail5_node1_witness.py K
"""
import sys
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, '.')
import tail5_measure as T
from fractions import Fraction
k, a, K = 13, 808, int(ARGS[0])
b, n = 5, 9
D = K - k
cells = []
stack = [(k, a)]
while stack:
    kk, aa = stack.pop()
    if T.sft(kk, aa) == 99: continue
    if kk == K:
        if T.good(kk, aa):
            w = T.weight(kk, aa)
            if w > 0: cells.append((aa, w))
        continue
    stack.append((kk + 1, 2 * aa)); stack.append((kk + 1, 2 * aa + 1))
cells.sort()
tot = sum(w for _, w in cells)
rlo = Fraction(T.rad(b)[0], T.SCALE)          # rational lower bound for 5^-4.49
half = rlo / b ** n                            # window half-width (lower bound): cells inside this are inside the true window
best = (Fraction(0), None)
for i, (c0, _) in enumerate(cells):
    # window [L, L + 2*half] with left end at cell c0's left end
    L = Fraction(c0, 2 ** K)
    cap = sum(w for c, w in cells if Fraction(c, 2 ** K) >= L and Fraction(c + 1, 2 ** K) <= L + 2 * half)
    if cap > best[0]: best = (cap, c0)
C = Fraction(37, 20)
rhi = Fraction(T.rad(b)[1], T.SCALE)
allowed = C * 2 * rhi * tot
print(f"(13,808) level {K}: {len(cells)} positive Good descendants, descMass = {float(tot):.6g}")
print(f"best window (left end at cell {best[1]}): captured {float(best[0]):.6g} = {float(best[0]/tot):.4%} of descMass")
print(f"node-1 bound C*2*5^-4.49*descMass <= {float(allowed):.6g} ({float(allowed/tot):.4%})  ->",
      "REFUTED" if best[0] > allowed else "not refuted")
print("exact: captured =", best[0], "; descMass =", tot, "; AMBIG", T.AMBIG[0])
