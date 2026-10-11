#!/usr/bin/env python3
"""Gate 5 measurement: WEIGHTED window losses of tail bases on the proved gate-4 core.

Weights are Coherent.wq o Coherent.classify (frozen W449, normalized by maxW), cells are exact
integers, irrational radii r_b = b^-4.49 are enclosed at 60 digits (ambiguous cases counted).

Charging model (the one a proof would use; totals cannot be equidistributed rigorously):
a base-b window of stage n (centre A/b^n) is charged to the level-L ancestor cell, L = smallest
multiple of 6 with 2^L >= b^n (so an ancestor meets <= 2 stage-n windows of base b).  For the
ancestor, lag j >= 0 collects the weight of Good children at level L+6(j+1) killed by the window
(some cell between L+6j+1 and L+6(j+1) inside it) whose parent at L+6j is Good and not yet killed.
Windows are taken in isolation (an upper bound on their joint loss).  Ratio = loss / w(anc).

Budget: sum_j h_j / gamma^j <= (9/5)^6 - gamma, gamma = (17/10)^6  (= 9.874655).

usage: tail5_measure.py MODE [args]
  control-zero         : no tail windows -> all charges 0 (must PASS)
  control-kill         : kill every first-block child -> lag-0 charge >= (9/5)^6 (must FAIL)
  measure B NMAX       : bases 5..B (non-perfect-powers), all stages n <= NMAX, every window
"""
import gzip, sys
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

getcontext().prec = 80
HERE = Path(__file__).parent
N, M = 128, 24
SFT = [(1,13),(2,13),(3,13),(4,13),(99,5),(6,14),(99,7),(99,8),(9,15),(99,10),(99,11),(12,15),(99,13),
       (1,14),(1,15),(1,16),(17,99),(2,18),(19,99),(20,99),(3,21),(22,99),(23,99),(3,24),(1,99)]
W = [int(x) for x in gzip.decompress((HERE / "W449_N128_M24_D6.txt.gz").read_bytes()).split()]
assert len(W) == 25 * N * M
MAXW = 1072633893121
assert max(W) == MAXW
src = (HERE.parent.parent / "src/CertData/Gate4.lean").read_text()
EDGES = [int(t) for t in src.split("def edges : Array Int := #[")[1].split("]")[0].split(",")]
assert len(EDGES) == M - 1

SCALE = 10 ** 60
def rad(b):  # integer enclosure [lo, hi] of b^-4.49 * SCALE
    v = (Decimal(b).ln() * Decimal("-4.49")).exp() * SCALE
    return int(v) - 1, int(v) + 2
R3 = rad(3)
GAMMA = Fraction(17, 10) ** 6
GROW = Fraction(9, 5) ** 6
BUDGET = GROW - GAMMA
AMBIG = [0]
CLIMB = [0]
JJ = 16
THETA = Fraction(__import__('os').environ.get('TAIL5_THETA', '0'))  # climb to weight > THETA

def sft(k, a):
    s = 0
    for i in range(k - 1, -1, -1):
        s = SFT[s][(a >> i) & 1]
        if s == 99: return 99
    return s

def pend(k):  # smallest n with 2 delta3 2^k < 3^n
    n = 0
    while True:
        # 2 r3 2^k < 3^n  <=>  2 * R * 2^k < 3^n * SCALE
        if 2 * R3[1] * 2 ** k < 3 ** n * SCALE: return n
        if 2 * R3[0] * 2 ** k >= 3 ** n * SCALE: n += 1; continue
        AMBIG[0] += 1; return n

def dist_ok(k, a, b, n, r):
    """cell (k,a) disjoint from all closed base-b stage-n windows (radius r) -> True/False."""
    lo, hi = a * b ** n, (a + 1) * b ** n  # in units 2^-k
    q = lo >> k
    # nearest integers: q (below lo) and q+1 .. ; interval [lo,hi] meets [A-r, A+r] ?
    for A in range(q, (hi >> k) + 2):
        c = A << k
        # meet iff lo <= c + r2^k and hi >= c - r2^k
        g = max(lo - c, c - hi, 0)  # gap in 2^-k units
        # meets iff g <= r 2^k
        if g * SCALE <= r[0] * 2 ** k: return False
        if g * SCALE <= r[1] * 2 ** k: AMBIG[0] += 1; return False
    return True

def good(k, a):
    if a >= 2 ** k or sft(k, a) == 99: return False
    n = 0
    while 3 ** n * SCALE <= 2 * R3[1] * 2 ** k:  # possibly resolved stage
        if 3 ** n * SCALE > 2 * R3[0] * 2 ** k: AMBIG[0] += 1
        if not dist_ok(k, a, 3, n, R3): return False
        n += 1
    return True

def weight(k, a):  # wq (classify k a), with Good449 decided above
    if k == 0 and a == 0: return Fraction(1)
    if k < 5 or not good(k, a): return Fraction(0)
    s = sft(k, a)
    p = pend(k)
    x = 3 ** p * a
    ib = (N * (x % 2 ** k)) >> k
    jb = sum(1 for e in EDGES if e * 2 ** k < 3 ** p * 2 ** 90)
    return Fraction(W[s * N * M + ib * M + jb], MAXW)

def inside(k, a, b, n, A, r):  # cell subset of window: certain / ambiguous -> True (upper bound)
    c = A << k
    X = max(c - a * b ** n, (a + 1) * b ** n - c)
    if X * SCALE <= r[0] * 2 ** k: return True
    if X * SCALE <= r[1] * 2 ** k: AMBIG[0] += 1; return True
    return False

def meets(k, a, b, n, A, r):
    c = A << k
    g = max(a * b ** n - c, c - (a + 1) * b ** n, 0)
    return g * SCALE <= r[1] * 2 ** k

SHIFT = int(__import__("os").environ.get("TAIL5_SHIFT", "0"))  # charge SHIFT blocks higher

def anc_level(b, n):
    L = 0
    while 2 ** L < b ** n: L += 6
    return max(L - 6 * SHIFT, 0)

def window_loss(b, n, A, r, L, a0, J):
    """lag profile of the loss of window (b,n,A) under ancestor (L,a0)."""
    loss = [Fraction(0)] * J
    def good_desc(k, a, kt):  # weighted Good descendants at level kt
        if k == kt: return weight(k, a)
        if sft(k, a) == 99: return Fraction(0)
        return good_desc(k + 1, 2 * a, kt) + good_desc(k + 1, 2 * a + 1, kt)
    def walk(k, a, j):  # cell (k,a) alive, meets window, L+6j <= k < L+6(j+1) ... parent block level
        if sft(k, a) == 99: return
        if (k - L) % 6 == 0:
            j = (k - L) // 6
            if j >= J: return
            if not good(k, a): pblock_ok = False
            else: pblock_ok = True
            walk.ok = pblock_ok
        kt = L + 6 * (j + 1)
        for c in (2 * a, 2 * a + 1):
            if not meets(k + 1, c, b, n, A, r): continue
            if inside(k + 1, c, b, n, A, r):
                if walk.ok: loss[j] += good_desc(k + 1, c, kt)
                continue
            if k + 1 == kt:
                saved = walk.ok
                walk(k + 1, c, j + 1)
                walk.ok = saved
            else:
                walk(k + 1, c, j)
    walk.ok = True
    walk(L, a0, 0)
    return loss

def is_pp(b):
    return any(round(b ** (1 / e)) ** e == b for e in range(2, b.bit_length() + 1))

def report(acc, J, label):
    gam = [GAMMA ** j for j in range(J)]
    worst, worstkey = Fraction(0), None
    unch = 0
    lagmax = [Fraction(0)] * J
    for key, (w, prof) in acc.items():
        if w == 0:
            if any(prof): unch += 1
            continue
        rat = [x / w for x in prof]
        for j in range(J): lagmax[j] = max(lagmax[j], rat[j])
        tot = sum(rat[j] / gam[j] for j in range(J))
        if tot > worst: worst, worstkey = tot, key
    disc = sum(lagmax[j] / gam[j] for j in range(J))
    print(f"[{label}] ancestors={len(acc)} ambiguous={AMBIG[0]} max climb={CLIMB[0]}")
    print("  per-lag max ratio h_j:", [f"{float(x):.6g}" for x in lagmax])
    print(f"  sum_j h_j/gamma^j = {float(disc):.6g}   (per-ancestor worst {float(worst):.6g} at {worstkey})")
    print(f"  budget (9/5)^6 - (17/10)^6 = {float(BUDGET):.6f}  ->  {'PASS' if disc <= BUDGET and unch == 0 else 'FAIL'} at gamma=(17/10)^6"
          f" [SAMPLED lower bound on the scheme's supremum, per-window isolation overcount; unchargeable={unch}]")
    return disc

def main():
    mode = sys.argv[1]
    J = 6 + SHIFT
    if mode == "control-zero":
        report({}, J, "control: zero tail")
    elif mode == "control-kill":
        # kill every first-block child: for every Good cell at level L=6m (m <= 2), loss_0 = all Good children
        acc = {}
        for L in (6, 12):
            for a in range(2 ** L):
                w = weight(L, a)
                if w == 0: continue
                ch = sum((weight(L + 6, 64 * a + j) for j in range(64)), Fraction(0))
                acc[(L, a)] = (w, [ch] + [Fraction(0)] * (J - 1))
        report(acc, J, "control: delete every first-block child")
    elif mode == "measure":
        B, NMAX = int(sys.argv[2]), int(sys.argv[3])
        acc = {}
        for b in range(5, B + 1):
            if is_pp(b): continue
            r = rad(b)
            for n in range(NMAX + 1):
                L = anc_level(b, n)
                for A in range(b ** n + 1):
                    # level-L cells meeting the window
                    lo = ((A * SCALE - r[1]) * 2 ** L) // (b ** n * SCALE)
                    for a0 in range(max(lo, 0), min(lo + 3, 2 ** L)):
                        if sft(L, a0) == 99: continue
                        if not meets(L, a0, b, n, A, r): continue
                        prof = window_loss(b, n, A, r, L, a0, J)
                        if not any(prof): continue
                        # a weight-0 (non-Good) ancestor is not in mass: climb to the nearest Good
                        # block ancestor, one extra lag per block climbed
                        LL, aa, off = L, a0, 0
                        while weight(LL, aa) <= THETA: LL, aa, off = LL - 6, aa >> 6, off + 1
                        CLIMB[0] = max(CLIMB[0], off)
                        key = (LL, aa)
                        if key not in acc: acc[key] = (weight(LL, aa), [Fraction(0)] * JJ)
                        for j in range(J): acc[key][1][j + off] += prof[j]
            print(f"base {b} done (n <= {NMAX})", flush=True)
            report(acc, JJ, f"bases 5..{b}, n <= {NMAX}")
    else:
        raise SystemExit(__doc__)

if __name__ == "__main__":
    main()
