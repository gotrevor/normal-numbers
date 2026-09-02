"""Emit Lean certificates for `signed_engine_g_single`: the Mahler collapse
`M(g,1) <= M`.  Channels are `a = 1..M`, each avoiding the single digit `w`.

State encoding matches `AdderBaseG.gfamPred` exactly for ell = 1, b = 0:
per channel `a`, gwinSize = 1, carrySize = a, off = 0,
  gpred a x c' = none            if (a*x + c') % g == w
               = some ((a*x+c') / g)  otherwise
family state = sum_i c_i * prod_{j<i} a_j.
"""
import sys, json
from collections import defaultdict

def build(g, mults, w):
    sizes = list(mults)                      # carrySize = a
    S = 1
    for a in sizes: S *= a
    strides = []
    acc = 1
    for a in sizes:
        strides.append(acc); acc *= a
    preds = []                               # preds[sigma][s'] = s or -1
    for x in range(g):
        row = [-1] * S
        for sp in range(S):
            s = 0; ok = True
            for a, st in zip(mults, strides):
                cp = (sp // st) % a
                v = a * x + cp
                if v % g == w: ok = False; break
                s += (v // g) * st
            row[sp] = s if ok else -1
        preds.append(row)
    return S, preds

def certificate(g, mults, w):
    S, preds = build(g, mults, w)
    edges = [(preds[x][sp], x, sp) for x in range(g) for sp in range(S) if preds[x][sp] >= 0]
    alive = [True] * S
    omega = [0] * S
    rnd = 0
    while True:
        out = [0] * S
        for s, x, sp in edges:
            if alive[s] and alive[sp]: out[s] += 1
        dying = [s for s in range(S) if alive[s] and out[s] == 0]
        if not dying: break
        for s in dying: omega[s] = rnd; alive[s] = False
        rnd += 1
    live = alive
    nlive = sum(live)
    if nlive == 0:
        return dict(S=S, nlive=0, live=[], rho={}, omega={s: omega[s] for s in range(S) if omega[s]},
                    forced={}, omega_all=omega)
    ledges = [(s, x, sp) for s, x, sp in edges if live[s] and live[sp]]
    # Tarjan SCC
    import sys as _s; _s.setrecursionlimit(1 << 20)
    adj = defaultdict(list)
    for s, x, sp in ledges: adj[s].append(sp)
    index = {}; low = {}; onstk = {}; stk = []; comp = {}; counter = [0]; ncomp = [0]
    def strong(v):
        work = [(v, 0)]
        while work:
            u, pi = work[-1]
            if pi == 0:
                index[u] = low[u] = counter[0]; counter[0] += 1
                stk.append(u); onstk[u] = True
            recurse = False
            for i in range(pi, len(adj[u])):
                v2 = adj[u][i]
                if v2 not in index:
                    work[-1] = (u, i + 1); work.append((v2, 0)); recurse = True; break
                elif onstk.get(v2):
                    low[u] = min(low[u], index[v2])
            if recurse: continue
            if low[u] == index[u]:
                while True:
                    z = stk.pop(); onstk[z] = False; comp[z] = ncomp[0]
                    if z == u: break
                ncomp[0] += 1
            work.pop()
            if work:
                pu = work[-1][0]; low[pu] = min(low[pu], low[u])
    for s in range(S):
        if live[s] and s not in index: strong(s)
    same = lambda s, sp: comp[s] == comp[sp]
    intra_out = defaultdict(int)
    for s, x, sp in ledges:
        if same(s, sp): intra_out[s] += 1
    members = defaultdict(list)
    for s in range(S):
        if live[s]: members[comp[s]].append(s)
    forced = {}
    for c, ms in members.items():
        cyc = len(ms) > 1 or any(same(ms[0], ms[0]) and sp == ms[0] and s == ms[0]
                                 for s, x, sp in ledges)
        if len(ms) == 1 and intra_out[ms[0]] == 0: continue
        if not all(intra_out[s] == 1 for s in ms):
            raise SystemExit(f"SCC size {len(ms)} not a simple cycle: "
                             f"{sorted(set(intra_out[s] for s in ms))}  (g={g},w={w})")
    for s, x, sp in ledges:
        if same(s, sp) and intra_out[s] == 1:
            if s in forced: raise SystemExit("multi-label forced")
            forced[s] = (x, sp)
    # rho = condensation height
    cadj = defaultdict(set)
    for s, x, sp in ledges:
        if not same(s, sp): cadj[comp[s]].add(comp[sp])
    memo = {}
    def h(u):
        if u in memo: return memo[u]
        memo[u] = 0
        best = 0
        for v in cadj.get(u, ()): best = max(best, h(v) + 1)
        memo[u] = best; return best
    rho = {s: h(comp[s]) for s in range(S) if live[s]}
    # re-verify exactly as Lean's checkCertA will
    for x in range(g):
        for sp in range(S):
            s = preds[x][sp]
            if s < 0: continue
            if live[s]:
                if live[sp]:
                    drop = rho[sp] < rho[s]
                    forc = forced.get(s) == (x, sp) and rho[sp] == rho[s]
                    if not (drop or forc):
                        raise SystemExit(f"C1 FAIL g={g} w={w} s={s} x={x} sp={sp}")
            else:
                if live[sp] or omega[sp] >= omega[s]:
                    raise SystemExit(f"C3 FAIL g={g} w={w} s={s} x={x} sp={sp}")
    for s, (x, sp) in forced.items():
        if preds[x][sp] != s or not live[sp] or not live[s]:
            raise SystemExit(f"C1' FAIL s={s}")
    return dict(S=S, nlive=nlive,
                live=[s for s in range(S) if live[s]],
                rho={s: rho[s] for s in range(S) if live[s] and rho[s]},
                omega={s: omega[s] for s in range(S) if not live[s] and omega[s]},
                forced=forced)

if __name__ == "__main__":
    g = int(sys.argv[1]); M = int(sys.argv[2])
    mults = list(range(1, M + 1))
    for w in range(g):
        c = certificate(g, mults, w)
        print(f"g={g} M={M} w={w}: ambient={c['S']} live={c['nlive']} "
              f"rho_nz={len(c['rho'])} omega_nz={len(c['omega'])} forced={len(c['forced'])}",
              flush=True)

def emit_lean(g, M, tag):
    """Emit Lean defs (C6-style sparse assoc lists) for base g, channels 1..M."""
    mults = list(range(1, M + 1))
    out = []
    for w in range(g):
        c = certificate(g, mults, w)
        L = ", ".join(str(s) for s in c['live'])
        R = ", ".join(f"({s}, {v})" for s, v in sorted(c['rho'].items()))
        O = ", ".join(f"({s}, {v})" for s, v in sorted(c['omega'].items()))
        F = ", ".join(f"({s}, ({x}, {sp}))" for s, (x, sp) in sorted(c['forced'].items()))
        out.append(f"""
def {tag}live{w} : ℕ → Bool := fun s => [{L}].contains s

def {tag}rho{w} : ℕ → ℕ := fun s =>
  (([{R}] : List (ℕ × ℕ)).lookup s).getD 0

def {tag}omega{w} : ℕ → ℕ := fun s =>
  (([{O}] : List (ℕ × ℕ)).lookup s).getD 0

def {tag}forced{w} : ℕ → Option (ℕ × ℕ) := fun s =>
  ([{F}] : List (ℕ × ℕ × ℕ)).lookup s
""")
        print(f"-- w={w}: ambient {c['S']}, live {c['nlive']}", file=sys.stderr)
    return "\n".join(out)
