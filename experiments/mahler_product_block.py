#!/usr/bin/env -S uv run --quiet --with scipy --with numpy python3
"""Product blocks (the shape of the ternary {2, 11}), any base g: exact checker + lower bounds.

A PRODUCT BLOCK is a finite S such that for every irrational x, ONE m in S has every base-g
digit infinitely often in m*x.  Lean: NormalNumbers.Adder.IsProductBlock
(src/NormalNumbers/MahlerProductBlock.lean).  Write-up: docs/base5-product-block-2026-10-05.md.

EXACT CHECKER (upper side).  Channel (m, d): x's tail t_n, carry s_n = floor(m t_n) in [0, m-1],
    s_n = (m x_n + s_{n+1}) // g,   digit_n(m x) = (m x_n + s_{n+1}) % g  (must != d).
A joint-avoidance tail is an infinite path in the product graph on carry tuples.  CORE(chans)
= states in an SCC with an internal edge; CORE(chans + [c]) lies inside CORE(chans) x [0, m_c),
so we refine channel by channel and the state set stays small.  COLLAPSE = every core SCC is a
simple cycle, so every avoiding tail is eventually periodic, so x is rational.  Collapse of a
PREFIX proves the whole assignment.  S is a block iff every assignment S -> digits collapses
on some prefix.  Same verdicts as mahler_minimal_sets.py / adder_baseg_emit.py (C2 certs).

LIOUVILLE FILTER (lower side).  x = B * sum g^(-n_k), gaps -> inf: digit d != 0 is i.o. in m*x
iff d is a base-g digit of m*B.  So a block needs, for EVERY B >= 1, some m in S whose product
m*B uses every nonzero digit (IsProductBlock.liouville_cover).  Necessary, loose (base 3: 87
pairs <= 40 pass, 2 are blocks).

Usage:
  mahler_product_block.py check G m1,m2,...      exact verdict (+ first failing assignment)
  mahler_product_block.py filter G m1,... BMAX   uncovered B <= BMAX
  mahler_product_block.py ilp G MMAX BMAX        exact min |S| passing the filter (HiGHS)
"""
import sys
from functools import lru_cache


def make_trans(g, m, d):
    """T[s][x] = tuple of s_next with digit != d."""
    T = []
    for s in range(m):
        row = []
        for x in range(g):
            row.append(tuple(s2 for s2 in range(m)
                             if (m * x + s2) // g == s and (m * x + s2) % g != d))
        T.append(row)
    return T


_TR = {}


def trans(g, m, d):
    k = (g, m, d)
    if k not in _TR:
        _TR[k] = make_trans(g, m, d)
    return _TR[k]


def sccs(nodes, adj):
    """Tarjan, iterative.  nodes: list; adj: dict node -> list of (label, node)."""
    idx, low, onst, st, out = {}, {}, set(), [], []
    c = 0
    for r in nodes:
        if r in idx:
            continue
        idx[r] = low[r] = c; c += 1; st.append(r); onst.add(r)
        work = [(r, 0)]
        while work:
            v, i = work[-1]
            nb = adj[v]
            if i < len(nb):
                work[-1] = (v, i + 1)
                w = nb[i][1]
                if w not in idx:
                    idx[w] = low[w] = c; c += 1; st.append(w); onst.add(w)
                    work.append((w, 0))
                elif w in onst:
                    low[v] = min(low[v], idx[w])
            else:
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == idx[v]:
                    comp = []
                    while True:
                        w = st.pop(); onst.discard(w); comp.append(w)
                        if w == v:
                            break
                    out.append(comp)
    return out


def refine(g, core, m, d):
    """core: (nodes, adj) with labelled edges.  Returns (new_core, collapsed)."""
    nodes, adj = core
    T = trans(g, m, d)
    nn = [(v, s) for v in nodes for s in range(m)]
    nadj = {}
    for (v, s) in nn:
        lst = []
        for x, w in adj[v]:
            for s2 in T[s][x]:
                lst.append((x, (w, s2)))
        nadj[(v, s)] = lst
    comps = sccs(nn, nadj)
    keep = set()
    collapsed = True
    for comp in comps:
        cs = set(comp)
        e = sum(1 for v in comp for _, w in nadj[v] if w in cs)
        if e == 0:
            continue
        keep |= cs
        if e > len(comp):
            collapsed = False
    kn = [v for v in nn if v in keep]
    kadj = {v: [(x, w) for x, w in nadj[v] if w in keep] for v in kn}
    return (kn, kadj), collapsed


def root(g):
    return ([()], {(): [(x, ()) for x in range(g)]})


def failing(g, S, limit=None, sym=True):
    """List failing full assignments (as digit tuples).  Stops after `limit`."""
    bad = []

    def rec(j, core, ds):
        if limit is not None and len(bad) >= limit:
            return
        if j == len(S):
            bad.append(tuple(ds)); return
        digs = range(g)
        if sym and j == 0:
            digs = range((g + 1) // 2)  # d -> g-1-d is x -> -x
        for d in digs:
            nc, col = refine(g, core, S[j], d)
            if col:
                continue
            rec(j + 1, nc, ds + [d])

    rec(0, root(g), [])
    return bad


def per_digit(g, S, d):
    core = root(g)
    for m in S:
        core, col = refine(g, core, m, d)
        if col:
            return True
    return False


# --- Liouville filter ---
def digits(n, g):
    s=set()
    while n: s.add(n%g); n//=g
    return s
def covers(m, B, g): return set(range(1,g)) <= digits(m*B, g)
def uncovered(S, g, Bmax):
    return [B for B in range(1,Bmax+1) if B%g and not any(covers(m,B,g) for m in S)]
def greedy_hit(g, Mmax, Bmax, seed=()):
    S=list(seed); U=set(uncovered(S,g,Bmax))
    cands=[m for m in range(1,Mmax+1) if m%g]
    cov={m:{B for B in U if covers(m,B,g)} for m in cands}
    while U:
        m=max(cands,key=lambda m:(len(cov[m]&U),-m))
        if not cov[m]&U: return S,U
        S.append(m); U-=cov[m]
    return S,U


def ilp(g, Mmax, Bmax):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    Bs = [B for B in range(1, Bmax + 1) if B % g]
    ms = [m for m in range(1, Mmax + 1) if m % g]
    A = lil_matrix((len(Bs), len(ms)))
    for j, m in enumerate(ms):
        for i, B in enumerate(Bs):
            if covers(m, B, g):
                A[i, j] = 1
    r = milp(c=np.ones(len(ms)), constraints=LinearConstraint(A.tocsr(), lb=1, ub=np.inf),
             integrality=np.ones(len(ms)), bounds=Bounds(0, 1))
    S = [m for j, m in enumerate(ms) if r.x is not None and r.x[j] > .5]
    return r.status, S


if __name__ == "__main__":
    cmd, g = sys.argv[1], int(sys.argv[2])
    if cmd == "check":
        S = [int(t) for t in sys.argv[3].split(",")]
        b = failing(g, S, limit=1)
        print("BLOCK" if not b else "NOT A BLOCK (certificate method); first failing assignment %s" % (b[0],))
    elif cmd == "filter":
        S = [int(t) for t in sys.argv[3].split(",")]
        print("uncovered B:", uncovered(S, g, int(sys.argv[4]))[:20])
    elif cmd == "ilp":
        st, S = ilp(g, int(sys.argv[3]), int(sys.argv[4]))
        print("status", st, "min |S| =", len(S), "e.g.", S)
