#!/usr/bin/env python3
"""Reduced-state certificate emitter for single-track base-g families with
word length ell >= 1 (the 2026-09-16 carry-consistency reduction, window case).

For channels (a_i, 0, w) the state at step m is a function of just TWO
parameters: r = floor(X g^m) mod g (the previous digit of X) and
t = fract(X g^m):

  carry_i   = floor(a_i t)
  digit_j_i = (a_i g^j F + floor(a_i g^j t)) mod g      (j < ell-1)
  chanCode_i = carry_i * g^(ell-1) + sum_j digit_j_i * g^j

so with N = lcm{a_i g^j} the whole state is a function of (r, k=floor(N t)).
The reachable set is enumerated exactly by walking the breakpoints of t.
The emitted state list L is then closed under pred (all letters).
"""
import json, sys
from fractions import Fraction
from math import gcd, floor
from pathlib import Path

CERTS = Path(__file__).parent / "certs"


def lcm_all(xs):
    L = 1
    for x in xs:
        L = L * x // gcd(L, x)
    return L


def build(name, g, ms, word):
    ell = len(word)
    W = g ** (ell - 1)
    wordval = 0
    for d in reversed(word):
        wordval = d + g * wordval
    sizes = [a * W for a in ms]
    strides, acc = [], 1
    for n in sizes:
        strides.append(acc); acc *= n
    S = acc
    N = lcm_all([a * g ** j for a in ms for j in range(ell)])
    def state(t):
        """gfamState as a function of t = fract(X g^m) alone:
        carry = floor(a t), and the j-th window digit is
        gdigit g (aX) (m+j) = floor(a g^(j+1) t) - g*floor(a g^j t)."""
        s = 0
        for a, st in zip(ms, strides):
            code = floor(a * t) * W
            for j in range(ell - 1):
                code += (floor(a * g ** (j + 1) * t) - g * floor(a * g ** j * t)) * g ** j
            s += code * st
        return s
    # breakpoints of t
    bps = {Fraction(0)}
    for a in ms:
        for j in range(ell):
            q = a * g ** j
            for p in range(1, q):
                bps.add(Fraction(p, q))
    bl = sorted(bps)
    samples = []
    for i, b in enumerate(bl):
        hi = bl[i + 1] if i + 1 < len(bl) else Fraction(1)
        samples.append((b + hi) / 2)
        samples.append(b)
    reach = set()
    for t in samples:
        reach.add(state(t))
    print(f"[{name}] ambient {S}, N {N}, reachable {len(reach)} "
          f"(breakpoints {len(bl)})", flush=True)

    def pred(x, sp):
        s = 0
        for a, n, st in zip(ms, sizes, strides):
            code = (sp // st) % n
            cprime = code // W
            wprime = code % W
            v = a * x + cprime
            z = v % g
            c = v // g
            full = z + g * wprime
            if full == wordval:
                return -1
            s += (c * W + full % W) * st
        return s
    # self-test: the state map must intertwine with pred along real walks
    #   t_{m+1} = fract(g t),  sigma = floor(g t)
    bad = 0
    for t in samples:
        t1 = g * t - floor(g * t)
        sig = floor(g * t)
        got = pred(sig, state(t1))
        if got != -1 and got != state(t):
            bad += 1
    if bad:
        raise SystemExit(f"[{name}] state/pred intertwining FAILED on {bad} samples")
    print(f"[{name}] state/pred intertwining: OK on {len(samples)} samples", flush=True)
    # close under pred
    L = set(reach)
    frontier = list(reach)
    while frontier:
        nxt = []
        for sp in frontier:
            for x in range(g):
                s = pred(x, sp)
                if s >= 0 and s not in L:
                    L.add(s); nxt.append(s)
        frontier = nxt
    L = sorted(L)
    idx = {s: i for i, s in enumerate(L)}
    M = len(L)
    print(f"[{name}] pred-closed state list: {M}", flush=True)
    A = g
    P = [[(lambda v: idx[v] if v >= 0 else -1)(pred(x, L[j])) for j in range(M)]
         for x in range(A)]
    edges = [(P[x][j], j, x) for x in range(A) for j in range(M) if P[x][j] >= 0]
    alive = [True] * M; omega = [0] * M; rnd = 0
    while True:
        out = [0] * M
        for (s, sp, _) in edges:
            if alive[s] and alive[sp]: out[s] += 1
        dying = [s for s in range(M) if alive[s] and out[s] == 0]
        if not dying: break
        for s in dying: omega[s] = rnd; alive[s] = False
        rnd += 1
    nlive = sum(alive)
    print(f"[{name}] live {nlive} (rounds {rnd})", flush=True)
    if nlive == 0: raise SystemExit(f"[{name}] EMPTY live set")
    ledges = [(s, sp, x) for (s, sp, x) in edges if alive[s] and alive[sp]]
    adj = {}
    for (s, sp, _) in ledges: adj.setdefault(s, []).append(sp)
    import importlib.util
    spec = importlib.util.spec_from_file_location("emit", Path(__file__).parent / "adder_baseg_emit.py")
    em = importlib.util.module_from_spec(spec); spec.loader.exec_module(em)
    _, lab = em.tarjan_scc(M, adj)
    intra = [0] * M
    for (s, sp, _) in ledges:
        if lab[s] == lab[sp]: intra[s] += 1
    mem = {}
    for s in range(M):
        if alive[s]: mem.setdefault(lab[s], []).append(s)
    selfl = {s for (s, sp, _) in ledges if s == sp}
    for c, Ms in mem.items():
        if len(Ms) > 1 or Ms[0] in selfl:
            if not all(intra[s] == 1 for s in Ms):
                raise SystemExit(f"[{name}] SCC size {len(Ms)} not a simple cycle — NON-COLLAPSE")
    fsig = [-1] * M; fdst = [-1] * M
    for (s, sp, x) in ledges:
        if lab[s] == lab[sp] and intra[s] == 1:
            if fsig[s] >= 0: raise SystemExit(f"[{name}] two intra edges at {s}")
            fsig[s] = x; fdst[s] = sp
    cedges = {}
    for (s, sp, _) in ledges:
        if lab[s] != lab[sp]: cedges.setdefault(lab[s], set()).add(lab[sp])
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
        if alive[s]: rho[s] = height(lab[s])
    fail = 0
    for x in range(A):
        for sp in range(M):
            s = P[x][sp]
            if s < 0: continue
            if alive[s]:
                if alive[sp]:
                    if not (rho[sp] < rho[s] or (fsig[s] == x and fdst[s] == sp and rho[sp] == rho[s])):
                        fail += 1
            else:
                if alive[sp] or omega[sp] >= omega[s]: fail += 1
    for s in range(M):
        if fsig[s] >= 0 and (P[fsig[s]][fdst[s]] != s or not alive[fdst[s]] or not alive[s]):
            fail += 1
    if fail: raise SystemExit(f"[{name}] {fail} condition failures — REFUSING")
    print(f"[{name}] C1/C1'/C3' verified: OK (rho max {max(rho)}, omega max {max(omega)})", flush=True)
    out = {"name": name, "g": g, "ms": ms, "word": word, "ambient": S, "N": N,
           "L": L, "M": M, "alphabet": A, "n_live": nlive,
           "live": [int(a) for a in alive], "rho": rho, "omega": omega,
           "forced_sig": fsig, "forced_dst": fdst}
    CERTS.mkdir(exist_ok=True)
    (CERTS / f"adder_cert_{name}.json").write_text(json.dumps(out))
    print(f"[{name}] emitted")


if __name__ == "__main__":
    name, g, msv, wv = sys.argv[1:5]
    build(name, int(g), [int(x) for x in msv.split(',')], [int(x) for x in wv.split(',')])
