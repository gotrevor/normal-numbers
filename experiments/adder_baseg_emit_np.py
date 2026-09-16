#!/usr/bin/env python3
"""Vectorized (numpy) certificate emitter for large single-track base-g families.

Same automaton, same four certificate conditions (C1/C1'/C3') as
`adder_baseg_emit.py`, but the ambient sweep is done with numpy arrays so
families with millions of states (the `(6,1)` hitting set is 9067520) are
reachable.  Output is the SPARSE json the Lean emitter wants:
  {name, g, channels, ambient, alphabet, n_live,
   live_k, rho_k, rho_v, omega_k, omega_v, forced_k, forced_s, forced_d}

Usage: adder_baseg_emit_np.py <name> <g> <m1,m2,...> <word digits, e.g. 0 or 0,1>
"""
import json, sys
from pathlib import Path
import numpy as np

CERTS = Path(__file__).parent / "certs"


def build(name, g, ms, word):
    ell = len(word)
    wsz = g ** (ell - 1)
    wordval = 0
    for d in reversed(word):
        wordval = d + g * wordval
    sizes = [m * wsz for m in ms]
    strides = []
    acc = 1
    for n in sizes:
        strides.append(acc)
        acc *= n
    S = acc
    A = g
    print(f"[{name}] ambient {S}, alphabet {A}", flush=True)
    sp = np.arange(S, dtype=np.int64)
    preds = np.empty((A, S), dtype=np.int64)
    for x in range(A):
        s = np.zeros(S, dtype=np.int64)
        bad = np.zeros(S, dtype=bool)
        for m, n, stride in zip(ms, sizes, strides):
            code = (sp // stride) % n
            cprime = code // wsz
            wprime = code % wsz
            v = m * x + cprime
            z = v % g
            c = v // g
            full = z + g * wprime
            bad |= (full == wordval)
            s += (c * wsz + full % wsz) * stride
        preds[x] = np.where(bad, -1, s)
    # backward pruning: s dies when it has no live out-edge s -> s'
    alive = np.ones(S, dtype=bool)
    omega = np.zeros(S, dtype=np.int64)
    rnd = 0
    while True:
        out = np.zeros(S, dtype=np.int64)
        for x in range(A):
            P = preds[x]
            ok = (P >= 0) & alive & alive[np.maximum(P, 0)]
            out += np.bincount(P[ok], minlength=S)
        dying = alive & (out == 0)
        if not dying.any():
            break
        omega[dying] = rnd
        alive[dying] = False
        rnd += 1
    n_live = int(alive.sum())
    print(f"[{name}] live {n_live} (rounds {rnd})", flush=True)
    if n_live == 0:
        raise SystemExit(f"[{name}] EMPTY live set")
    live_idx = np.nonzero(alive)[0]
    pos = {int(s): i for i, s in enumerate(live_idx)}
    ledges = []
    for x in range(A):
        P = preds[x]
        sub = P[live_idx]
        for i, (spv, sv) in enumerate(zip(live_idx, sub)):
            if sv >= 0 and alive[sv]:
                ledges.append((int(sv), int(spv), x))
    # SCC on the live subgraph (tiny)
    adj = {}
    for (s, spv, _) in ledges:
        adj.setdefault(pos[s], []).append(pos[spv])
    lab = tarjan(len(live_idx), adj)
    intra = [0] * len(live_idx)
    for (s, spv, _) in ledges:
        if lab[pos[s]] == lab[pos[spv]]:
            intra[pos[s]] += 1
    mem = {}
    for i in range(len(live_idx)):
        mem.setdefault(lab[i], []).append(i)
    selfl = {pos[s] for (s, spv, _) in ledges if s == spv}
    cycles = 0
    for c, M in mem.items():
        if len(M) > 1 or M[0] in selfl:
            if not all(intra[i] == 1 for i in M):
                raise SystemExit(f"[{name}] SCC not a simple cycle — NON-COLLAPSE")
            cycles += 1
    forced_sig = {}
    forced_dst = {}
    for (s, spv, x) in ledges:
        if lab[pos[s]] == lab[pos[spv]] and intra[pos[s]] == 1:
            if int(s) in forced_sig:
                raise SystemExit(f"[{name}] two intra edges at {s}")
            forced_sig[int(s)] = x
            forced_dst[int(s)] = int(spv)
    # component DAG heights -> rho
    cedges = {}
    for (s, spv, _) in ledges:
        if lab[pos[s]] != lab[pos[spv]]:
            cedges.setdefault(lab[pos[s]], set()).add(lab[pos[spv]])
    memo = {}

    def height(u):
        stack = [(u, False)]
        while stack:
            v, done = stack.pop()
            if done:
                memo[v] = max((memo[w] + 1 for w in cedges.get(v, ())), default=0)
                continue
            if v in memo:
                continue
            stack.append((v, True))
            for w in cedges.get(v, ()):
                if w not in memo:
                    stack.append((w, False))
        return memo[u]

    rho = np.zeros(S, dtype=np.int64)
    for i, s in enumerate(live_idx):
        rho[s] = height(lab[i])
    print(f"[{name}] cycles {cycles}, rho max {rho.max()}, omega max {omega.max()}",
          flush=True)
    # verification, vectorized
    fsig = np.full(S, -1, dtype=np.int64)
    fdst = np.full(S, -1, dtype=np.int64)
    for s, x in forced_sig.items():
        fsig[s] = x
        fdst[s] = forced_dst[s]
    fail = 0
    for x in range(A):
        P = preds[x]
        m = P >= 0
        s = np.maximum(P, 0)
        ls = alive[s] & m
        # live target
        bad1 = ls & alive & ~((rho < rho[s]) | ((fsig[s] == x) & (fdst[s] == sp)
                              & (rho == rho[s])))
        # dead target
        bad2 = m & ~alive[s] & (alive | (omega >= omega[s]))
        fail += int(bad1.sum()) + int(bad2.sum())
    for s, x in forced_sig.items():
        d = forced_dst[s]
        if preds[x][d] != s or not alive[d] or not alive[s]:
            fail += 1
    if fail:
        raise SystemExit(f"[{name}] {fail} condition failures — REFUSING")
    print(f"[{name}] C1/C1'/C3' verified: OK", flush=True)
    rk = np.nonzero(rho)[0]
    ok_ = np.nonzero(omega)[0]
    fk = sorted(forced_sig)
    out = {
        "name": name, "g": g, "ms": list(ms), "word": list(word),
        "ambient": S, "alphabet": A, "n_live": n_live, "sparse": True,
        "live_k": [int(v) for v in live_idx],
        "rho_k": [int(v) for v in rk], "rho_v": [int(rho[v]) for v in rk],
        "omega_k": [int(v) for v in ok_], "omega_v": [int(omega[v]) for v in ok_],
        "forced_k": fk, "forced_s": [forced_sig[s] for s in fk],
        "forced_d": [forced_dst[s] for s in fk],
    }
    CERTS.mkdir(exist_ok=True)
    (CERTS / f"adder_cert_{name}.json").write_text(json.dumps(out))
    print(f"[{name}] emitted (omega nz {len(ok_)})", flush=True)


def tarjan(n, adj):
    index = [-1] * n; low = [0] * n; on = [False] * n
    st = []; lab = [-1] * n; cnt = [0]; nc = [0]
    for root in range(n):
        if index[root] != -1:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = cnt[0]; cnt[0] += 1
                st.append(v); on[v] = True
            rec = False
            nb = adj.get(v, ())
            for i in range(pi, len(nb)):
                w = nb[i]
                if index[w] == -1:
                    work[-1] = (v, i + 1); work.append((w, 0)); rec = True; break
                elif on[w]:
                    low[v] = min(low[v], index[w])
            if rec:
                continue
            if low[v] == index[v]:
                while True:
                    w = st.pop(); on[w] = False; lab[w] = nc[0]
                    if w == v:
                        break
                nc[0] += 1
            work.pop()
            if work:
                u, _ = work[-1]
                low[u] = min(low[u], low[v])
    return lab


if __name__ == "__main__":
    name, g, msv, wv = sys.argv[1:5]
    build(name, int(g), [int(x) for x in msv.split(',')],
          [int(x) for x in wv.split(',')])
