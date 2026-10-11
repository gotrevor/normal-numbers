#!/usr/bin/env python3
# Host probe (Ren, 2026-10-08) for the "tighten the beam" c* lane.
# Survivors of ||b^n xi|| > b^-c over all bases 2<=b<=B and all n with b^n <= CAP, as a union of
# intervals in [0,1].  Constraints are applied in increasing order of the scale s = b^n, so pruning
# bites early.  Floating point: it only chooses a gate; a Lean certificate must be exact.
# Usage: uniformbad_cstar_probe_scaled.py B CAP [c ...]   (no c: bisect the threshold)
import math, os, sys
from fractions import Fraction
def constraints(B, cap):
    out = []
    cap2 = int(float(os.environ.get('CAP2', cap)))  # deeper horizon for base 2 (and its powers)
    for b in range(2, B + 1):
        s = 1
        while s <= (cap2 if b & (b - 1) == 0 else cap):
            out.append((s, b)); s *= b
    out.sort()
    return out
EXACT = os.environ.get('EXACT') == '1'  # Fraction endpoints: needed once s*eps ~ 1e-6, i.e. s > ~1e9
def survivors(c, B, cap, cons=None):
    iv = [(Fraction(0), Fraction(1))] if EXACT else [(0.0, 1.0)]
    for s, b in (cons or constraints(B, cap)):
        d = Fraction(b ** (-c)) if EXACT else b ** (-c); out = []
        for lo, hi in iv:
            k0 = math.floor(lo * s - d); k1 = math.ceil(hi * s + d)
            cur = lo
            for k in range(k0, k1 + 1):
                a, bb = (k - d) / s, (k + d) / s
                if bb <= cur or a >= hi: continue
                if a > cur: out.append((cur, min(a, hi)))
                cur = max(cur, bb)
                if cur >= hi: break
            if cur < hi: out.append((cur, hi))
        iv = []
        for x in out:
            if x[1] <= x[0]: continue
            if iv and x[0] <= iv[-1][1]: iv[-1] = (iv[-1][0], max(iv[-1][1], x[1]))
            else: iv.append(x)
        if not iv: return []
        if len(iv) > int(os.environ.get("MAXIV", 2_000_000)): return iv  # blowup: report as surviving (heuristic)
    return iv
if __name__ == "__main__":
    B, cap = int(sys.argv[1]), int(float(sys.argv[2]))
    cons = constraints(B, cap)
    if len(sys.argv) > 3:
        for c in map(float, sys.argv[3:]):
            iv = survivors(c, B, cap, cons)
            print(f"c={c}: {len(iv)} intervals, measure {sum(h-l for l,h in iv):.3e}")
            for l, h in iv[:40]: print(f"  [{l:.10f}, {h:.10f}]  ~ {Fraction((l+h)/2).limit_denominator(int(1e5))}")
    else:
        lo, hi = (float(os.environ.get('LO', 2.4)), float(os.environ.get('HI', 2.8)))
        for _ in range(22):
            mid = (lo + hi) / 2
            if survivors(mid, B, cap, cons): hi = mid
            else: lo = mid
        iv = survivors(hi, B, cap, cons)
        pts = sorted({Fraction((l+h)/2).limit_denominator(int(1e5)) for l, h in iv})
        print(f"B={B} cap={cap:g}: threshold ~ {hi:.5f}; survivors there ~ {[str(p) for p in pts[:8]]}")
