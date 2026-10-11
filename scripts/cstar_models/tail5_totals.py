#!/usr/bin/env python3
"""Gate 5: exact TOTAL mass(m) and loss(m) of TailReview (the statement's own quantities), with
tailBad449 restricted to bases 5..B (non-perfect-powers).  This upper-bounds the true surviving mass
but is NOT a lower bound on the true loss (more bases also remove parents).  Parents are all
survivors (Good and Alive), including zero-weight ones (Codex review (n)).  usage: tail5_totals.py B MMAX
Also reports the full per-parent lag-0 ratio max (loss of one parent's children / its weight)."""
import sys
from fractions import Fraction
from tail5_measure import weight, good, sft, rad, is_pp, inside, AMBIG, GAMMA, BUDGET

B, MMAX = int(sys.argv[1]), int(sys.argv[2])
BASES = [(b, rad(b)) for b in range(5, B + 1) if not is_pp(b)]
SCALE = 10 ** 60

def bad(k, a):
    for b, r in BASES:
        n = 0
        while True:
            # window length 2 r b^-n >= 2^-k needed
            if 2 * r[1] * 2 ** k < b ** n * SCALE: break
            # nearest centre A to the cell midpoint
            A = ((2 * a + 1) * b ** n + 2 ** k) // (2 ** (k + 1))
            for AA in (A - 1, A, A + 1):
                if AA >= 0 and inside(k, a, b, n, AA, r): return True
            n += 1
    return False

mass = [Fraction(0)] * (MMAX + 2)
loss = [Fraction(0)] * (MMAX + 1)
pmax = [Fraction(0)] * (MMAX + 1)
mass[0] = Fraction(1)
ZW, ZWL = [0], [Fraction(0)]

def dfs(k, a, alive, m_par, par_w, acc):
    """cell (k,a) with sft alive; alive = Alive tailBad so far; par_w = weight of surviving block
    parent (None if parent at 6m not surviving)."""
    if k % 6 == 0 and k > 0:
        m = k // 6
        w = weight(k, a)
        if par_w is not None and w > 0 and not alive:
            loss[m - 1] += w; acc[0] += w
        if not alive: return
        if good(k, a):
            mass[m] += w
            if m > MMAX: return
            sub = [Fraction(0)]
            for c in (2 * a, 2 * a + 1):
                if sft(k + 1, c) != 99: dfs(k + 1, c, not bad(k + 1, c), m, w, sub)
            if w > 0: pmax[m] = max(pmax[m], sub[0] / w)
            elif sub[0] > 0: ZW[0] += 1; ZWL[0] = max(ZWL[0], sub[0])
            return
        par_w = None
        if m > MMAX: return
    for c in (2 * a, 2 * a + 1):
        if sft(k + 1, c) == 99: continue
        al = alive and not bad(k + 1, c)
        if not al and par_w is None: continue
        dfs(k + 1, c, al, m_par, par_w, acc)

root = [Fraction(0)]
for c in (0, 1): dfs(1, c, not bad(1, c), 0, Fraction(1), root)
pmax[0] = root[0]
for m in range(MMAX + 1):
    print(f"m={m}: mass={float(mass[m]):.6g} loss={float(loss[m]):.6g} "
          f"loss/mass={float(loss[m] / mass[m]):.6g} mass(m+1)/mass(m)={float(mass[m+1] / mass[m]):.6g} "
          f"max parent loss/w={float(pmax[m]):.6g}", flush=True)
print(f"zero-weight surviving parents with positive child loss: {ZW[0]} (max loss {float(ZWL[0]):.6g})")
print(f"ambiguous={AMBIG[0]} budget={float(BUDGET):.6f}  [all numbers: exact values on the finite tree, not suprema]")
