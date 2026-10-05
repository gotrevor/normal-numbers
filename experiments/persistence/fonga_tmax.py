#!/usr/bin/env -S uv run --quiet python3
"""Fonga Thm 4.1 (base 10, p = 2): exact max v2(y) over y in A_10(nu), plus the
explicit Cor. 3.2 bound, plus Brier-style enumeration sizes, for every family.

usage: fonga_tmax.py [time_budget_s_per_family]
"""
import json, math, sys, time
from functools import lru_cache


def v2(n):
    return (n & -n).bit_length() - 1 if n else 10**9

class Timeout(Exception):
    pass

def tmax_exact(D, deadline):
    """D: dict digit->count.  Returns max v2 over the family (Fonga Thm 4.1), and a witness."""
    digits = sorted(d for d, c in D.items() if c)
    best = [0, None]
    seen = {}
    calls = [0]

    def rec(M, a, T, path):
        calls[0] += 1
        if calls[0] & 0xFFF == 0 and time.time() > deadline:
            raise Timeout
        v = v2(T)
        if v > best[0]:
            best[0] = v; best[1] = path
        key = (M, a, T)
        if key in seen:
            return
        seen[key] = 1
        if sum(M) == 0:
            for L in range(a + 1, v + 1):
                w = v2(T + 10 ** L)
                if w > best[0]:
                    best[0] = w; best[1] = path + (("L", L),)
            return
        for t in range(a + 1, v + 1):
            for i, d in enumerate(digits):
                if M[i]:
                    M2 = M[:i] + (M[i] - 1,) + M[i + 1:]
                    rec(M2, t, T + 9 * (d - 1) * 10 ** t, path + ((d, t),))

    M0 = tuple(D[d] for d in digits)
    for i, d in enumerate(digits):
        if d % 2 == 0 and M0[i]:
            M = M0[:i] + (M0[i] - 1,) + M0[i + 1:]
            rec(M, 0, 9 * (d - 1) - 1, ((d, 0),))
    return best[0], best[1], calls[0]

def cor32(D):
    q = sum(D.values())
    B = 1 + 9 * sum((d - 1) * c for d, c in D.items())
    c = math.log2(10)
    if D.get(2): rho = 3
    elif D.get(6): rho = 2
    elif D.get(4) or D.get(8): rho = 1
    else: return 0
    return math.floor(rho * c ** q + (c ** q - 1) / (c - 1) * math.log2(B))

def log10_multiset(D):
    # a0 free mod 12; identical digits -> multisets of residues mod 12
    r = math.log10(12)
    for d, c in D.items():
        r += math.log10(math.comb(c + 11, 11))
    return r

if __name__ == "__main__":
    BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0
    data = json.load(open("families.json"))
    rows = []
    for delta, v in data.items():
        for s, nu, kp1 in v["fams"]:
            D = {int(k): c for k, c in nu.items() if c}
            t0 = time.time()
            try:
                tm, wit, calls = tmax_exact(D, t0 + BUDGET)
                ok = True
            except Timeout:
                tm, wit, calls, ok = None, None, None, False
            rows.append(dict(delta=int(delta), s=s, D=D, kp1=kp1, tmax=tm, ok=ok,
                             secs=round(time.time() - t0, 4), cor32_log10=round(math.log10(max(cor32(D), 1)), 1),
                             naive_log10=round(kp1 * math.log10(12), 1), multiset_log10=round(log10_multiset(D), 1)))
    json.dump(rows, open("family_metrics.json", "w"))
    import statistics
    for delta in (2, 4, 6, 8):
        R = [r for r in rows if r["delta"] == delta]
        done = [r for r in R if r["ok"]]
        print(f"delta={delta}: families={len(R)} tmax computed for {len(done)} (budget {BUDGET}s each); "
              f"max tmax={max((r['tmax'] for r in done), default=None)}; "
              f"sum naive 12^(k+1) = 10^{math.log10(sum(10**r['naive_log10'] for r in R)):.1f}; "
              f"sum multiset = 10^{math.log10(sum(10**r['multiset_log10'] for r in R)):.1f}; "
              f"max Cor3.2 bound = 10^{max(r['cor32_log10'] for r in R)}")
        for thr in (6, 9, 12, 15):
            n = sum(1 for r in R if r["multiset_log10"] <= thr)
            print(f"     families with multiset count <= 1e{thr}: {n}")
