#!/usr/bin/env python3
"""Pure-stdlib certificate emitter for SIGNED adder families
(BRIEF-adder-signed-engine objective 3).

Reimplements adder_certificate_emit.py without numpy/scipy (no egress on
this box), extended to signed coefficients with the offset carry encoding
of AdderSigned.lean, mirrored bit-for-bit:

  * carry T in [-(a-+b-), a++b+-1]; encoded c = T + off, off = a-+b-;
    carrySize = max(a+ + b+ + off, 1).
  * pred: v = a*x + b*y + (c'(s') - off);  z = v & 1, T_out = v >> 1
    (Python & / >> floor-match Int.emod/Int.ediv at modulus 2);
    encoded out-carry = T_out + off.
  * everything else (window encoding, mixed radix, legality test) as in
    the unsigned emitter.

Cross-check: running on "main" must reproduce experiments/certs/
adder_cert_main.json field-for-field (the unsigned fibre has off = 0).

The emitter REFUSES to write a certificate failing its own C1/C1'/C3'
re-verification.

Usage: adder_signed_emit.py [main|musical|crosscheck]
"""

import json
import sys
from pathlib import Path

FAMILIES = {
    "main": [(1, 0, "00"), (0, 1, "001"), (1, 1, "11"),
             (1, 2, "001"), (2, 1, "010"), (1, 3, "000")],
    # constants ln2, ln3, ln(3/2), ln(4/3), ln(9/8), ln6
    "musical": [(1, 0, "00"), (0, 1, "11"), (-1, 1, "100"),
                (2, -1, "11"), (-3, 2, "00"), (1, 1, "010")],
}


def neg(t):
    return max(-t, 0)


def pos(t):
    return max(t, 0)


class Family:
    def __init__(self, channels):
        self.channels = channels
        self.ells = [len(w) for _, _, w in channels]
        self.offs = [neg(a) + neg(b) for a, b, _ in channels]
        self.pos_sums = [pos(a) + pos(b) for a, b, _ in channels]
        for a, b, _ in channels:
            assert pos(a) + pos(b) >= 1, (a, b)
        self.carry_sizes = [max(p + o, 1)
                            for p, o in zip(self.pos_sums, self.offs)]
        self.win_sizes = [2 ** (e - 1) for e in self.ells]
        self.sizes = [c * w for c, w in zip(self.carry_sizes, self.win_sizes)]
        S = 1
        for n in self.sizes:
            S *= n
        self.S = S
        self.words = [int(w[::-1], 2) for _, _, w in channels]

    def pred(self, sigma, sp):
        """pred[sigma][s'] -> s or -1 (illegal)."""
        x, y = sigma & 1, sigma >> 1
        s, mult, rem = 0, 1, sp
        for (a, b, _), wsz, word, n, off, csz in zip(
                self.channels, self.win_sizes, self.words, self.sizes,
                self.offs, self.carry_sizes):
            code = rem % n
            rem //= n
            cprime = code // wsz
            wprime = code % wsz
            v = a * x + b * y + (cprime - off)
            z = v & 1
            c = (v >> 1) + off
            assert 0 <= c < csz, (a, b, c)
            full = z + 2 * wprime
            if full == word:
                return -1
            s += (c * wsz + full % wsz) * mult
            mult *= n
        return s

    def pred_tables(self):
        return [[self.pred(g, sp) for sp in range(self.S)] for g in range(4)]


def tarjan_scc(n_nodes, adj):
    """Iterative Tarjan; returns labels (list, -1 for unvisited-irrelevant)."""
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


def build_certificate(name, channels):
    fam = Family(channels)
    S = fam.S
    preds = fam.pred_tables()
    print(f"[{name}] ambient states: {S}")

    edges = []  # (src, dst, sigma)
    for g in range(4):
        p = preds[g]
        for sp in range(S):
            if p[sp] >= 0:
                edges.append((p[sp], sp, g))

    # prune
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
        raise SystemExit(f"[{name}] EMPTY live set — no certificate")

    # live subgraph SCCs
    ledges = [(s, sp, g) for (s, sp, g) in edges if live[s] and live[sp]]
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
                             "cycle — REFUSING")
        cycles += 1
        periods.add(len(members))
    for (s, sp, g) in ledges:
        if labels[s] == labels[sp] and intra_out[s] == 1:
            if forced_sig[s] >= 0:
                raise SystemExit(f"[{name}] state {s}: two intra edges — REFUSING")
            forced_sig[s] = g
            forced_dst[s] = sp
    print(f"[{name}] cycles: {cycles}, periods: {sorted(periods)}")

    # rho: condensation height, iterative memo DFS over comp DAG
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

    # re-verify C1/C1'/C3'
    failures = 0
    for g in range(4):
        p = preds[g]
        for sp in range(S):
            s = p[sp]
            if s < 0:
                continue
            if live[s]:
                if live[sp]:
                    ok = rho[sp] < rho[s] or (
                        forced_sig[s] == g and forced_dst[s] == sp
                        and rho[sp] == rho[s])
                    if not ok:
                        failures += 1
            else:
                if live[sp] or omega[sp] >= omega[s]:
                    failures += 1
    for s in range(S):
        if forced_sig[s] >= 0:
            g, d = forced_sig[s], forced_dst[s]
            if preds[g][d] != s or not live[d] or not live[s]:
                failures += 1
    if failures:
        raise SystemExit(f"[{name}] {failures} condition failures — REFUSING")
    print(f"[{name}] C1/C1'/C3' verified in Python: OK")

    out = {
        "name": name,
        "channels": [{"a": a, "b": b, "word": [int(c) for c in w]}
                     for a, b, w in channels],
        "sizes": fam.sizes,
        "ambient": S,
        "n_live": n_live,
        "cycles": cycles,
        "periods": sorted(periods),
        "live": [int(v) for v in live],
        "rho": rho,
        "omega": omega,
        "forced_sig": forced_sig,
        "forced_dst": forced_dst,
    }
    d = Path(__file__).parent / "certs"
    d.mkdir(exist_ok=True)
    path = d / f"adder_cert_{name}.json"
    path.write_text(json.dumps(out))
    print(f"[{name}] emitted {path} ({path.stat().st_size} bytes)")
    return out


def crosscheck():
    """Re-derive 'main' and compare with the frozen numpy-emitted JSON."""
    ref_path = Path(__file__).parent / "certs" / "adder_cert_main.json"
    ref = json.loads(ref_path.read_text())
    got = build_certificate("main_stdlib", FAMILIES["main"])
    for k in ["sizes", "ambient", "n_live", "cycles", "periods",
              "live", "rho", "omega", "forced_sig", "forced_dst"]:
        assert got[k] == ref[k], f"crosscheck MISMATCH on {k}"
    (Path(__file__).parent / "certs" / "adder_cert_main_stdlib.json").unlink()
    print("crosscheck vs numpy-emitted main certificate: IDENTICAL")


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "musical"
    if which == "crosscheck":
        crosscheck()
    else:
        build_certificate(which, FAMILIES[which])
    print("done.")


if __name__ == "__main__":
    main()
