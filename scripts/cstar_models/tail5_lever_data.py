#!/usr/bin/env python3
"""Gate 5 lever probe, data for (L2) MASS charging: per-ANCESTOR descendant run sums, exact, exhaustive.

For every core-alive cell a at level k (alive = Good or not inside a base-3 window, as tail5_layercake.py)
and lag l >= 1, with the descendant parents p of a at level k + 6(l-1):
  fa_l(a)[R] = max over such p and contiguous runs of R of p's 64 children of sum W (Good children only),
  F2a_l(a)[R] = max_{R1+R2=R, Ri<=63} fa[R1] + fa[R2]   (a kill is at most two partial parents),
together with W(a) (0 if a is not Good) and D_j(a) = sum of Good W at level k+6j below a (core cells,
so an UPPER bound on a's tail-alive descendant mass).  Integers in units of MAXW.  Exhaustive over the levels run.
Output: tail5_out/lever/anc_k{k}_l{l}.pkl = list of ((W(a), D_1(a)..D_l(a)), F2a tuple of 127) with dominated rows removed.
usage: tail5_lever_data.py KCHILDMAX   (all (k, l) with k >= 5 and k + 6l <= KCHILDMAX)
"""
import sys, pickle
from pathlib import Path
from multiprocessing import Pool
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, str(Path(__file__).parent))
import tail5_comb as C
OUT = Path(__file__).parent / 'tail5_out' / 'lever'

def job(kl):
    k, l = kl
    kp = k + 6 * (l - 1)
    acc, good, w = C.load(kp + 6)
    kids = {}
    for a, g, x in zip(acc, good, w):
        if g: kids.setdefault(a >> 6, [0] * 64)[a & 63] = x
    fa = {}
    sh = 6 * (l - 1)
    for p, v in kids.items():
        pre = [0]
        for x in v: pre.append(pre[-1] + x)
        r = [max(pre[i + R] - pre[i] for i in range(65 - R)) for R in range(64)]
        q = p >> sh
        cur = fa.get(q)
        fa[q] = r if cur is None else [max(s, t) for s, t in zip(cur, r)]
    D = []                                   # D[j-1][a] = sum of Good W at level k+6j below a, j = 1..l
    for j in range(1, l + 1):
        acc2, good2, w2 = (acc, good, w) if j == l else C.load(k + 6 * j)
        d = {}
        for a2, g2, x2 in zip(acc2, good2, w2):
            if g2: d[a2 >> (6 * j)] = d.get(a2 >> (6 * j), 0) + x2
        D.append(d)
    accK, goodK, wK = C.load(k)
    rows = []
    for a, g, x in zip(accK, goodK, wK):
        if not g and C.inside3(k, a): continue
        f = fa.get(a, [0] * 64)
        F2 = tuple(max(f[r1] + f[R - r1] for r1 in range(max(0, R - 63), min(R, 63) + 1)) for R in range(127))
        rows.append(((x if g else 0,) + tuple(d.get(a, 0) for d in D), F2))
    # drop rows dominated by another with W' <= W and F2' >= F2 componentwise (cannot raise any max)
    rows.sort(key=lambda t: (t[0], [-v for v in t[1]]))
    keep = []
    for W, F2 in rows:
        if any(all(s2 <= s1 for s2, s1 in zip(W2, W)) and all(u >= v for u, v in zip(F22, F2)) for W2, F22 in keep[-200:]): continue
        keep.append((W, F2))
    pickle.dump(keep, open(OUT / f'anc_k{k}_l{l}.pkl', 'wb'))
    return k, l, len(rows), len(keep)

def main():
    kc = int(ARGS[0])
    OUT.mkdir(exist_ok=True)
    todo = [(k, l) for l in range(1, 5) for k in range(5, kc - 6 * l + 1)]
    with Pool(12) as P:
        for r in P.imap_unordered(job, sorted(todo, key=lambda t: -(t[0] + 6 * t[1]))):
            print("k=%d l=%d ancestors=%d kept=%d" % r, flush=True)

if __name__ == '__main__':
    main()
