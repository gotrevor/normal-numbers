#!/usr/bin/env python3
"""Reduced-state certificate emitter for single-track, word-length-1 base-g
families (the 2026-09-16 carry-consistency reduction).

For channels `(m_i, 0, [d])` the joint state at step n is
    s(t) = Σ_i ⌊m_i t⌋ · stride_i,   t = fract(X·g^n) ∈ [0,1),
so only `#{(⌊m_i t⌋)_i : t}` ≤ Σ(m_i−1)+1 of the `∏ m_i` ambient states are ever
reached.  With `N = lcm(m_i)` we have `⌊m_i t⌋ = (m_i·⌊N t⌋)/N`, so the reachable
set is the image of `k ↦ Σ_i ((m_i·k)/N)·stride_i` over `k < N`.

Emits the reduced automaton (state list `L`, relabelled pred, live/rho/omega/
forced) as json for `emit_reduced_lean.py`.
"""
import json, sys
from math import gcd
from pathlib import Path

CERTS = Path(__file__).parent / "certs"


def lcm_all(ms):
    L = 1
    for m in ms:
        L = L * m // gcd(L, m)
    return L


def build(name, g, ms, d):
    n = len(ms)
    strides, acc = [], 1
    for m in ms:
        strides.append(acc); acc *= m
    S = acc
    N = lcm_all(ms)
    def stateOfK(k):
        return sum(((m * k) // N) * st for m, st in zip(ms, strides))
    L = sorted({stateOfK(k) for k in range(N)})
    idx = {s: i for i, s in enumerate(L)}
    print(f"[{name}] ambient {S}, N {N}, reduced states {len(L)}")
    # relabelled pred: pred(x, L[j])
    def pred(x, j):
        sp = L[j]
        s = 0
        for m, st in zip(ms, strides):
            cprime = (sp // st) % m
            v = m * x + cprime
            z = v % g
            c = v // g
            if z == d:
                return -1
            s += c * st
        return idx[s]
    A = g
    M = len(L)
    P = [[pred(x, j) for j in range(M)] for x in range(A)]
    edges = [(P[x][j], j, x) for x in range(A) for j in range(M) if P[x][j] >= 0]
    alive = [True] * M
    omega = [0] * M
    rnd = 0
    while True:
        out = [0] * M
        for (s, sp, _) in edges:
            if alive[s] and alive[sp]:
                out[s] += 1
        dying = [s for s in range(M) if alive[s] and out[s] == 0]
        if not dying:
            break
        for s in dying:
            omega[s] = rnd; alive[s] = False
        rnd += 1
    nlive = sum(alive)
    print(f"[{name}] live {nlive} (rounds {rnd})")
    if nlive == 0:
        raise SystemExit(f"[{name}] EMPTY live set")
    ledges = [(s, sp, x) for (s, sp, x) in edges if alive[s] and alive[sp]]
    adj = {}
    for (s, sp, _) in ledges:
        adj.setdefault(s, []).append(sp)
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "emit", Path(__file__).parent / "adder_baseg_emit.py")
    em = importlib.util.module_from_spec(spec); spec.loader.exec_module(em)
    _, lab = em.tarjan_scc(M, adj)
    intra = [0] * M
    for (s, sp, _) in ledges:
        if lab[s] == lab[sp]:
            intra[s] += 1
    mem = {}
    for s in range(M):
        if alive[s]:
            mem.setdefault(lab[s], []).append(s)
    selfl = {s for (s, sp, _) in ledges if s == sp}
    for c, Ms in mem.items():
        if len(Ms) > 1 or Ms[0] in selfl:
            if not all(intra[s] == 1 for s in Ms):
                raise SystemExit(f"[{name}] SCC not a simple cycle — NON-COLLAPSE")
    fsig = [-1] * M; fdst = [-1] * M
    for (s, sp, x) in ledges:
        if lab[s] == lab[sp] and intra[s] == 1:
            if fsig[s] >= 0:
                raise SystemExit(f"[{name}] two intra edges at {s}")
            fsig[s] = x; fdst[s] = sp
    cedges = {}
    for (s, sp, _) in ledges:
        if lab[s] != lab[sp]:
            cedges.setdefault(lab[s], set()).add(lab[sp])
    memo = {}
    def height(u0):
        stack = [(u0, False)]
        while stack:
            u, done = stack.pop()
            if done:
                memo[u] = max((memo[v] + 1 for v in cedges.get(u, ())), default=0); continue
            if u in memo: continue
            stack.append((u, True))
            for v in cedges.get(u, ()):
                if v not in memo: stack.append((v, False))
        return memo[u0]
    rho = [0] * M
    for s in range(M):
        if alive[s]:
            rho[s] = height(lab[s])
    fail = 0
    for x in range(A):
        for sp in range(M):
            s = P[x][sp]
            if s < 0: continue
            if alive[s]:
                if alive[sp]:
                    ok = rho[sp] < rho[s] or (fsig[s] == x and fdst[s] == sp and rho[sp] == rho[s])
                    if not ok: fail += 1
            else:
                if alive[sp] or omega[sp] >= omega[s]: fail += 1
    for s in range(M):
        if fsig[s] >= 0:
            if P[fsig[s]][fdst[s]] != s or not alive[fdst[s]] or not alive[s]: fail += 1
    if fail:
        raise SystemExit(f"[{name}] {fail} condition failures — REFUSING")
    print(f"[{name}] C1/C1'/C3' verified: OK  (rho max {max(rho)}, omega max {max(omega)})")
    out = {"name": name, "g": g, "ms": ms, "digit": d, "ambient": S, "N": N,
           "L": L, "M": M, "alphabet": A, "n_live": nlive,
           "live": [int(a) for a in alive], "rho": rho, "omega": omega,
           "forced_sig": fsig, "forced_dst": fdst}
    CERTS.mkdir(exist_ok=True)
    (CERTS / f"adder_cert_{name}.json").write_text(json.dumps(out))
    print(f"[{name}] emitted")


if __name__ == "__main__":
    name, g, msv, d = sys.argv[1:5]
    build(name, int(g), [int(x) for x in msv.split(',')], int(d))
