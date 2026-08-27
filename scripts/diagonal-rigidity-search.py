#!/usr/bin/env -S uv run --quiet python3
"""Exhaustive search for a real whose first b base-b digits are a permutation of {0..b-1}.

The set K_B = {x : the constraint holds for every b <= B} is a finite union of intervals
with exact rational endpoints, and K_2 ⊇ K_3 ⊇ ...  So this is a DECIDABLE finite question
at each level, and the search settles the infinite question in one direction outright:

  * K_B empty for some B  =>  a FINITE CERTIFICATE that no such real exists (from b=2 up).
  * K_B nonempty for all B, each compact  =>  nested compact sets, intersection nonempty
    by Cantor, so a witness EXISTS.

Digit convention matches NormalNumbers.digitOf: x = sum_i d_i / b^(i+1), so the first b
digits are the base-b representation of floor(x * b^b), most significant first.
"""
from fractions import Fraction
import sys

def digits_of(k: int, b: int) -> list[int]:
    out = []
    for _ in range(b):
        out.append(k % b)
        k //= b
    return out[::-1]

def search(max_b: int, max_defects=lambda b: 0, cap: int = 400_000):
    cands = [(Fraction(0), Fraction(1))]
    for b in range(2, max_b + 1):
        scale = b ** b
        allow = max_defects(b)
        new = []
        scanned = 0
        for lo, hi in cands:
            k0 = (lo * scale).__floor__()
            k1 = -((-hi * scale).__floor__())      # ceil
            for k in range(k0, k1):
                scanned += 1
                if scanned > cap:
                    print(f"  b={b}: CAP hit ({cap} cells scanned) — inconclusive")
                    return b, None
                clo, chi = Fraction(k, scale), Fraction(k + 1, scale)
                a, z = max(lo, clo), min(hi, chi)
                if a >= z:
                    continue
                ds = digits_of(k, b)
                counts = [0] * b
                for d in ds:
                    counts[d] += 1
                defects = sum(abs(c - 1) for c in counts)
                if defects <= allow:
                    new.append((a, z))
        measure = sum(z - a for a, z in new)
        print(f"  b={b:2d}: {len(new):>7d} surviving interval(s), "
              f"measure {float(measure):.3e}, cells scanned {scanned}")
        cands = new
        if not cands:
            print(f"  >>> EMPTY at b={b}: finite certificate that NO real satisfies "
                  f"the constraint for all 2<=b'<={b}")
            return b, []
    return max_b, cands

print("=== EXACT permutation (zero defects) ===")
search(int(sys.argv[1]) if len(sys.argv) > 1 else 11)

def search_from(b0: int, max_b: int, allow_fn, cap=2_000_000, quiet=True):
    cands = [(Fraction(0), Fraction(1))]
    for b in range(b0, max_b + 1):
        scale = b ** b; allow = allow_fn(b); new = []; scanned = 0
        for lo, hi in cands:
            k0 = (lo * scale).__floor__(); k1 = -((-hi * scale).__floor__())
            for k in range(k0, k1):
                scanned += 1
                if scanned > cap:
                    return ("CAP", b, len(cands))
                clo, chi = Fraction(k, scale), Fraction(k + 1, scale)
                a, z = max(lo, clo), min(hi, chi)
                if a >= z: continue
                counts = [0] * b
                for d in digits_of(k, b): counts[d] += 1
                if sum(abs(c - 1) for c in counts) <= allow:
                    new.append((a, z))
        cands = new
        if not cands:
            return ("EMPTY", b, 0)
    return ("SURVIVED", max_b, len(cands))
