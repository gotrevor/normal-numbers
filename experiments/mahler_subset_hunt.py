"""Find minimal-ambient subsets of {1..M} whose base-g single-track adder
family collapses for EVERY digit w.  Ambient = product of the multipliers, so a
small subset gives a much cheaper Lean certificate for `M(g,1) <= M`.
Pure Python (the box has no egress for numpy/scipy)."""
import sys
from itertools import combinations
from collections import defaultdict

sys.setrecursionlimit(1 << 20)

def preds_of(g, mults, w):
    S = 1
    for a in mults: S *= a
    strides = []; acc = 1
    for a in mults: strides.append(acc); acc *= a
    preds = []
    for x in range(g):
        row = [-1] * S
        for sp in range(S):
            t = 0; ok = True
            for a, st in zip(mults, strides):
                v = a * x + ((sp // st) % a)
                if v % g == w: ok = False; break
                t += (v // g) * st
            if ok: row[sp] = t
        preds.append(row)
    return S, preds

def collapses(g, mults, w):
    S, preds = preds_of(g, mults, w)
    edges = [(preds[x][sp], x, sp) for x in range(g) for sp in range(S) if preds[x][sp] >= 0]
    alive = [True] * S
    while True:
        out = [0] * S
        for s, x, sp in edges:
            if alive[s] and alive[sp]: out[s] += 1
        dying = [s for s in range(S) if alive[s] and out[s] == 0]
        if not dying: break
        for s in dying: alive[s] = False
    if not any(alive): return True, 0
    adj = defaultdict(list)
    for s, x, sp in edges:
        if alive[s] and alive[sp]: adj[s].append(sp)
    # iterative Tarjan
    index = {}; low = {}; onstk = {}; stk = []; comp = {}; cnt = [0]; nc = [0]
    for root in range(S):
        if not alive[root] or root in index: continue
        work = [(root, 0)]
        while work:
            u, pi = work[-1]
            if pi == 0:
                index[u] = low[u] = cnt[0]; cnt[0] += 1
                stk.append(u); onstk[u] = True
            rec = False
            for i in range(pi, len(adj[u])):
                v = adj[u][i]
                if v not in index:
                    work[-1] = (u, i + 1); work.append((v, 0)); rec = True; break
                elif onstk.get(v): low[u] = min(low[u], index[v])
            if rec: continue
            if low[u] == index[u]:
                while True:
                    z = stk.pop(); onstk[z] = False; comp[z] = nc[0]
                    if z == u: break
                nc[0] += 1
            work.pop()
            if work:
                pu = work[-1][0]; low[pu] = min(low[pu], low[u])
    intra = defaultdict(int)
    for s, x, sp in edges:
        if alive[s] and alive[sp] and comp[s] == comp[sp]: intra[s] += 1
    if any(intra[s] > 1 for s in range(S) if alive[s]):
        return False, sum(alive)
    return True, sum(alive)

def main():
    g = int(sys.argv[1]); M = int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 60000
    cands = []
    for r in range(1, M + 1):
        for sub in combinations(range(1, M + 1), r):
            p = 1
            for a in sub: p *= a
            if p <= cap: cands.append((p, sub))
    cands.sort()
    for p, sub in cands:
        good = True
        for w in range(g):
            ok, nl = collapses(g, list(sub), w)
            if not ok: good = False; break
        if good:
            print(f"COLLAPSES ambient={p:8d} subset={sub}", flush=True)
            return
    print("none under cap", cap)

main()
