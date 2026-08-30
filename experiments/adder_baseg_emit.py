#!/usr/bin/env python3
"""Pure-stdlib certificate emitter for BASE-g adder families
(BRIEF-adder-tower phase B/C).

Mirrors AdderBaseG.lean bit-for-bit:

  * carry T in [-(a-+b-), a++b+-1]; encoded c = T + off, off = a-+b-;
    carrySize = max(a+ + b+ + off, 1)  (radix-independent, as in Lean).
  * gwinSize = g^(ell-1); word value = LSD-first base-g fold (digitsValG).
  * gpred: v = a*x + b*y + (c'(s') - off); z = v % g, T_out = v // g
    (Python % // are floor division, matching Int.emod/Int.ediv for
    positive modulus); encoded out-carry = T_out + off;
    full = z + g*w'; dies iff full == wordVal; else
    code = (T_out + off)*gwinSize + full % gwinSize.
  * mixed radix over the channel list, channel 0 least significant
    (gfamPred/gfamSize).
  * alphabet: two-track sigma = x + g*y < g^2; single-track sigma = x < g
    (signed_engine_g_single, Y := 0).

The certificate algorithm (prune -> SCC -> simple-cycle check -> forced ->
rho by condensation height -> C1/C1'/C3' re-verification, REFUSING on
failure) is verbatim adder_signed_emit.py.

Usage: adder_baseg_emit.py [c3|c2|c1|c4|c5|c6]
"""

import json
import sys
from pathlib import Path

# name -> (g, single_track?, channels [(a, b, word-digit-list MSD-first…)])
# Words are given as digit LISTS in stream order (first digit = shallowest),
# matching the Lean `word : List ℕ` (LSD-first in the fold = word[0] is the
# digit at the occurrence position).
FAMILIES = {
    # C1 (cross-check vs the hand-built Lean certs): x, 2x avoid d, base 3
    "c1": (3, True, [[(1, 0, [d]), (2, 0, [d])] for d in range(3)],
           ["d0", "d1", "d2"]),
    # C3: x, 5x avoid d, base 3
    "c3": (3, True, [[(1, 0, [d]), (5, 0, [d])] for d in range(3)],
           ["d0", "d1", "d2"]),
    # C2 product block: 2x avoids d1, 11x avoids d2, base 3 (9 certs)
    "c2": (3, True, [[(2, 0, [d1]), (11, 0, [d2])]
                     for d1 in range(3) for d2 in range(3)],
           [f"d{d1}{d2}" for d1 in range(3) for d2 in range(3)]),
    # C4: base-3 four-channel two-track single-digit family
    "c4": (3, False, [[(0, 1, [0]), (0, 3, [2]), (3, 1, [0]), (1, 1, [2])]],
           ["main"]),
    # C5: escape from Cantor (two-track, base 3, all avoid digit 1)
    "c5": (3, False, [[(0, 1, [1]), (0, 2, [1]), (1, 4, [1]),
                       (2, 0, [1]), (4, 0, [1])]],
           ["main"]),
    # C6: base-4 positioned-binary family (two-track)
    "c6": (4, False, [[(1, 0, [3]), (1, 3, [1]), (1, 4, [3]),
                       (2, -1, [2]), (2, 0, [0]), (2, 2, [0])]],
           ["main"]),
}


def neg(t):
    return max(-t, 0)


def pos(t):
    return max(t, 0)


class FamilyG:
    def __init__(self, g, channels, single):
        self.g = g
        self.single = single
        self.A = g if single else g * g
        self.channels = channels
        self.ells = [len(w) for _, _, w in channels]
        self.offs = [neg(a) + neg(b) for a, b, _ in channels]
        self.pos_sums = [pos(a) + pos(b) for a, b, _ in channels]
        for a, b, _ in channels:
            assert pos(a) + pos(b) >= 1, (a, b)
        for _, _, w in channels:
            assert all(0 <= d < g for d in w), w
        self.carry_sizes = [max(p + o, 1)
                            for p, o in zip(self.pos_sums, self.offs)]
        self.win_sizes = [g ** (e - 1) for e in self.ells]
        self.sizes = [c * w for c, w in zip(self.carry_sizes, self.win_sizes)]
        S = 1
        for n in self.sizes:
            S *= n
        self.S = S
        # digitsValG: LSD-first fold d0 + g*(d1 + g*(...))
        self.words = []
        for _, _, w in channels:
            v = 0
            for d in reversed(w):
                v = d + g * v
            self.words.append(v)

    def pred(self, sigma, sp):
        """pred[sigma][s'] -> s or -1 (illegal)."""
        g = self.g
        if self.single:
            x, y = sigma, 0
        else:
            x, y = sigma % g, sigma // g
        s, mult, rem = 0, 1, sp
        for (a, b, _), wsz, word, n, off, csz in zip(
                self.channels, self.win_sizes, self.words, self.sizes,
                self.offs, self.carry_sizes):
            code = rem % n
            rem //= n
            cprime = code // wsz
            wprime = code % wsz
            v = a * x + b * y + (cprime - off)
            z = v % g
            c = (v // g) + off
            assert 0 <= c < csz, (a, b, c)
            full = z + g * wprime
            if full == word:
                return -1
            s += (c * wsz + full % wsz) * mult
            mult *= n
        return s

    def pred_tables(self):
        return [[self.pred(sig, sp) for sp in range(self.S)]
                for sig in range(self.A)]


def tarjan_scc(n_nodes, adj):
    index = [-1] * n_nodes
    low = [0] * n_nodes
    on_stack = [False] * n_nodes
    stack = []
    labels = [-1] * n_nodes
    counter = [0]
    n_comp = [0]
    for root in range(n_nodes):
        if index[root] != -1:
            continue
        work = [(root, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = counter[0]
                counter[0] += 1
                stack.append(v)
                on_stack[v] = True
            recurse = False
            nbrs = adj.get(v, ())
            for i in range(pi, len(nbrs)):
                w = nbrs[i]
                if index[w] == -1:
                    work[-1] = (v, i + 1)
                    work.append((w, 0))
                    recurse = True
                    break
                elif on_stack[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    labels[w] = n_comp[0]
                    if w == v:
                        break
                n_comp[0] += 1
            work.pop()
            if work:
                u, _ = work[-1]
                low[u] = min(low[u], low[v])
    return n_comp[0], labels


def build_certificate(name, g, channels, single):
    fam = FamilyG(g, channels, single)
    S, A = fam.S, fam.A
    preds = fam.pred_tables()
    print(f"[{name}] ambient states: {S}, alphabet: {A}")

    edges = []
    for sig in range(A):
        p = preds[sig]
        for sp in range(S):
            if p[sp] >= 0:
                edges.append((p[sp], sp, sig))

    alive = [True] * S
    omega = [0] * S
    rnd = 0
    while True:
        out_deg = [0] * S
        for (s, sp, _) in edges:
            if alive[s] and alive[sp]:
                out_deg[s] += 1
        dying = [s for s in range(S) if alive[s] and out_deg[s] == 0]
        if not dying:
            break
        for s in dying:
            omega[s] = rnd
            alive[s] = False
        rnd += 1
    live = alive
    n_live = sum(live)
    print(f"[{name}] live states after pruning: {n_live} (rounds: {rnd})")
    if n_live == 0:
        raise SystemExit(f"[{name}] EMPTY live set — no certificate; "
                         "NON-COLLAPSE would be the other verdict, but an "
                         "empty live set means the family dies outright "
                         "(vacuous walk) — report upstream")

    ledges = [(s, sp, sig) for (s, sp, sig) in edges if live[s] and live[sp]]
    adj = {}
    for (s, sp, _) in ledges:
        adj.setdefault(s, []).append(sp)
    n_comp, labels = tarjan_scc(S, adj)

    intra_out = [0] * S
    for (s, sp, _) in ledges:
        if labels[s] == labels[sp] and labels[s] != -1:
            intra_out[s] += 1

    comp_members = {}
    for s in range(S):
        if live[s]:
            comp_members.setdefault(labels[s], []).append(s)
    self_loops = {s for (s, sp, _) in ledges if s == sp}
    forced_sig = [-1] * S
    forced_dst = [-1] * S
    cycles = 0
    periods = set()
    for comp, members in comp_members.items():
        is_cycle = len(members) > 1 or members[0] in self_loops
        if not is_cycle:
            if intra_out[members[0]] != 0:
                raise SystemExit(f"[{name}] singleton SCC oddity")
            continue
        if not all(intra_out[s] == 1 for s in members):
            raise SystemExit(f"[{name}] SCC size {len(members)} not a simple "
                             "cycle — NON-COLLAPSE FINDING, refusing")
        cycles += 1
        periods.add(len(members))
    for (s, sp, sig) in ledges:
        if labels[s] == labels[sp] and intra_out[s] == 1:
            if forced_sig[s] >= 0:
                raise SystemExit(f"[{name}] state {s}: two intra edges — "
                                 "refusing")
            forced_sig[s] = sig
            forced_dst[s] = sp
    print(f"[{name}] cycles: {cycles}, periods: {sorted(periods)}")

    comp_edges = {}
    for (s, sp, _) in ledges:
        if labels[s] != labels[sp]:
            comp_edges.setdefault(labels[s], set()).add(labels[sp])
    memo = {}

    def height(u0):
        order = [(u0, False)]
        while order:
            u, done = order.pop()
            if done:
                memo[u] = max((memo[v] + 1 for v in comp_edges.get(u, ())),
                              default=0)
                continue
            if u in memo:
                continue
            order.append((u, True))
            for v in comp_edges.get(u, ()):
                if v not in memo:
                    order.append((v, False))
        return memo[u0]

    rho = [0] * S
    for s in range(S):
        if live[s]:
            rho[s] = height(labels[s])
    om_max = max((omega[s] for s in range(S) if not live[s]), default=0)
    print(f"[{name}] rho range: 0..{max(rho)}, omega range: 0..{om_max}")

    failures = 0
    for sig in range(A):
        p = preds[sig]
        for sp in range(S):
            s = p[sp]
            if s < 0:
                continue
            if live[s]:
                if live[sp]:
                    ok = rho[sp] < rho[s] or (
                        forced_sig[s] == sig and forced_dst[s] == sp
                        and rho[sp] == rho[s])
                    if not ok:
                        failures += 1
            else:
                if live[sp] or omega[sp] >= omega[s]:
                    failures += 1
    for s in range(S):
        if forced_sig[s] >= 0:
            sig, d = forced_sig[s], forced_dst[s]
            if preds[sig][d] != s or not live[d] or not live[s]:
                failures += 1
    if failures:
        raise SystemExit(f"[{name}] {failures} condition failures — REFUSING")
    print(f"[{name}] C1/C1'/C3' verified in Python: OK")

    out = {
        "name": name, "g": g, "single": single,
        "channels": [{"a": a, "b": b, "word": w} for a, b, w in channels],
        "sizes": fam.sizes, "ambient": S, "alphabet": A,
        "n_live": n_live, "cycles": cycles, "periods": sorted(periods),
        "live": [int(v) for v in live], "rho": rho, "omega": omega,
        "forced_sig": forced_sig, "forced_dst": forced_dst,
    }
    d = Path(__file__).parent / "certs"
    d.mkdir(exist_ok=True)
    path = d / f"adder_cert_{name}.json"
    path.write_text(json.dumps(out))
    print(f"[{name}] emitted {path} ({path.stat().st_size} bytes)")
    # compact Lean-ready summary for small certs
    if S <= 600:
        lv = [s for s in range(S) if live[s]]
        print(f"  live_list := {lv}")
        print(f"  rho_list  := {[(s, rho[s]) for s in lv if rho[s] != 0]}")
        print(f"  omega_list:= {[(s, omega[s]) for s in range(S) if not live[s] and omega[s] != 0]}")
        print(f"  forced    := {[(s, forced_sig[s], forced_dst[s]) for s in range(S) if forced_sig[s] >= 0]}")
    return out


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "c3"
    g, single, variants, tags = FAMILIES[which]
    for chans, tag in zip(variants, tags):
        build_certificate(f"{which}_{tag}", g, chans, single)
    print("done.")


if __name__ == "__main__":
    main()
