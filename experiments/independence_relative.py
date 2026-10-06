#!/usr/bin/env -S uv run --quiet python3
"""Independence-relative certificates for two-track adder families (Ren, 2026-10-05).

A two-track family (channels `(a, b, word)`, base g) *collapses* when every live strongly
connected component of its carry automaton is a simple cycle: then any (X, Y) whose channels
all avoid their words has eventually periodic joint digits, so X and Y are rational.

A family that does NOT collapse can still be a theorem for every pair with 1, X, Y linearly
independent over Q.  It suffices that every non-cycle live SCC is DEGENERATE: some integer
combination aX + bY (not both zero) has an eventually periodic digit stream on every path
through it.  Any avoiding pair ends in one SCC, so it is either rational-rational or satisfies
aX + bY in Q.

Degeneracy test (sound, not complete): product of the SCC with the carry transducer of
aX + bY, then for each product SCC with a cycle, a phase assignment that makes the output
a single periodic word.  A consistent phase means zero-entropy, eventually periodic output.

Usage:
  independence_relative.py check G "a,b,w a,b,w ..."   (w = digits, e.g. 0 or 01)
  independence_relative.py search G K COEF [LIMIT]     random families, K channels
"""

import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from adder_baseg_emit import FamilyG, tarjan_scc  # noqa: E402


def live_graph(fam):
    S, A = fam.S, fam.A
    edges = []
    for sig in range(A):
        for sp in range(S):
            s = fam.pred(sig, sp)
            if s >= 0:
                edges.append((s, sp, sig))
    alive = [True] * S
    while True:
        out = [0] * S
        for s, sp, _ in edges:
            if alive[s] and alive[sp]:
                out[s] += 1
        dying = [s for s in range(S) if alive[s] and out[s] == 0]
        if not dying:
            break
        for s in dying:
            alive[s] = False
    ledges = [(s, sp, sig) for s, sp, sig in edges if alive[s] and alive[sp]]
    return alive, ledges


def sccs_with_cycles(nodes, edges):
    """nodes: iterable of hashables; edges: (u, v, label).  Returns list of (members, intra)."""
    idx = {u: i for i, u in enumerate(nodes)}
    adj = {}
    for u, v, _ in edges:
        adj.setdefault(idx[u], []).append(idx[v])
    _, labels = tarjan_scc(len(idx), adj)
    comps = {}
    for u, i in idx.items():
        comps.setdefault(labels[i], []).append(u)
    out = []
    for c, members in comps.items():
        mset = set(members)
        intra = [(u, v, l) for u, v, l in edges if u in mset and v in mset
                 and labels[idx[u]] == c]
        if intra:
            out.append((members, intra))
    return out


def periodic_output(members, intra):
    """True iff every bi-infinite path through this SCC emits one periodic output word
    (phase-consistent).  intra edges carry output labels."""
    start = members[0]
    adj = {}
    for u, v, o in intra:
        adj.setdefault(u, []).append((v, o))
    # find a cycle through start to get the candidate period word
    # BFS tree from start, then any edge back to start closes a cycle
    parent = {start: None}
    order = [start]
    for u in order:
        for v, o in adj.get(u, []):
            if v not in parent:
                parent[v] = (u, o)
                order.append(v)
    cyc = None
    for u in order:
        for v, o in adj.get(u, []):
            if v == start:
                path = [o]
                w = u
                while parent[w] is not None:
                    pu, po = parent[w]
                    path.append(po)
                    w = pu
                cyc = path[::-1]
                break
        if cyc:
            break
    if cyc is None:
        return False
    # primitive root of the cycle word
    n = len(cyc)
    p = next(d for d in range(1, n + 1) if n % d == 0 and cyc == cyc[:d] * (n // d))
    root = cyc[:p]
    phase = {start: 0}
    stack = [start]
    while stack:
        u = stack.pop()
        for v, o in adj.get(u, []):
            if o != root[phase[u]]:
                return False
            ph = (phase[u] + 1) % p
            if v in phase:
                if phase[v] != ph:
                    return False
            else:
                phase[v] = ph
                stack.append(v)
    return True


def degenerate_for(g, members, intra_sig, a, b):
    """Is a*X + b*Y eventually periodic on every path through this joint SCC?"""
    lo = -(max(-a, 0) + max(-b, 0))
    hi = max(a, 0) + max(b, 0)  # carries lie in [lo, hi - 1] (or {0} if hi = 0 and lo = 0)
    carries = list(range(lo, max(hi, lo + 1)))
    nodes = [(s, t) for s in members for t in carries]
    edges = []
    for s, sp, sig in intra_sig:
        x, y = sig % g, sig // g
        for tp in carries:
            v = a * x + b * y + tp
            t = v // g
            if t in carries:
                edges.append(((s, t), (sp, tp), v % g))
    for comp, intra in sccs_with_cycles(nodes, edges):
        if not periodic_output(comp, intra):
            return False
    return True


def combos(cmax):
    out = []
    for a in range(-cmax, cmax + 1):
        for b in range(-cmax, cmax + 1):
            if (a, b) == (0, 0):
                continue
            from math import gcd
            if gcd(abs(a), abs(b)) != 1:
                continue
            if a < 0 or (a == 0 and b < 0):
                continue  # sign symmetry: -Z rational iff Z rational
            out.append((a, b))
    return out


def classify(g, channels, cmax=3):
    """Returns ('collapse'|'dies'|'indep'|'open', detail)."""
    fam = FamilyG(g, channels, False)
    alive, ledges = live_graph(fam)
    if not any(alive):
        return "dies", None
    live_nodes = [s for s in range(fam.S) if alive[s]]
    comps = sccs_with_cycles(live_nodes, ledges)
    witnesses = []
    any_fat = False
    for members, intra in comps:
        simple = all(sum(1 for u, _, _ in intra if u == m) == 1 for m in members)
        if simple:
            continue
        any_fat = True
        found = None
        for a, b in combos(cmax):
            if degenerate_for(g, members, intra, a, b):
                found = (a, b)
                break
        if found is None:
            return "open", len(members)
        witnesses.append(found)
    if not any_fat:
        return "collapse", None
    return "indep", sorted(set(witnesses))


def parse(spec):
    chans = []
    for tok in spec.split():
        a, b, w = tok.split(",")
        chans.append((int(a), int(b), [int(c) for c in w]))
    return chans


def single_combo_trivial(channels, witnesses):
    """A family is 'trivially independent' if each witness direction is the direction of
    some channel: then the theorem is just 'an irrational number has some digit i.o.'."""
    dirs = set()
    for a, b, _ in channels:
        from math import gcd
        d = gcd(abs(a), abs(b))
        a2, b2 = a // d, b // d
        if a2 < 0 or (a2 == 0 and b2 < 0):
            a2, b2 = -a2, -b2
        dirs.add((a2, b2))
    return all(w in dirs for w in witnesses)


def block_verdict(g, k, dirs, cmax=3):
    """Product-block test: for EVERY assignment of one avoided length-k word per channel,
    classify the family.  Returns ('universal'|'relative'|'fail', witnesses, first_failure).
    'relative' = every assignment collapses, dies or is degenerate, and at least one is
    degenerate: then for every pair off the witness lines, some channel shows ALL length-k
    words infinitely often (transversal lemma, as for C2)."""
    words = [list(w) for w in itertools.product(range(g), repeat=k)]
    wit = set()
    for assign in itertools.product(range(len(words)), repeat=len(dirs)):
        chans = [(a, b, words[i]) for (a, b), i in zip(dirs, assign)]
        verdict, detail = classify(g, chans, cmax)
        if verdict == "open":
            return "fail", None, [words[i] for i in assign]
        if verdict == "indep":
            wit.update(detail)
    return ("relative" if wit else "universal"), sorted(wit), None


def block_search(g, k, cmax_dir, sizes):
    pool = [(a, b) for a in range(-cmax_dir, cmax_dir + 1)
            for b in range(-cmax_dir, cmax_dir + 1)
            if max(a, 0) + max(b, 0) >= 1]
    tally = {}
    for m in sizes:
        for dirs in itertools.combinations(pool, m):
            v, wit, fail = block_verdict(g, k, list(dirs))
            tally[(m, v)] = tally.get((m, v), 0) + 1
            if v != "fail":
                print(f"{v.upper()} m={m} {dirs} witnesses={wit}", flush=True)
    print("tally", tally)


def main():
    if sys.argv[1] == "block":
        g, k = int(sys.argv[2]), int(sys.argv[3])
        dirs = [tuple(int(c) for c in t.split(",")) for t in sys.argv[4].split()]
        print(block_verdict(g, k, dirs))
        return
    if sys.argv[1] == "blocksearch":
        g, k, cm = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        sizes = [int(s) for s in sys.argv[5].split(",")]
        block_search(g, k, cm, sizes)
        return
    if sys.argv[1] == "check":
        g = int(sys.argv[2])
        print(classify(g, parse(sys.argv[3])))
    elif sys.argv[1] == "search":
        g, k, cm = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        limit = int(sys.argv[5]) if len(sys.argv) > 5 else 2000
        rng = random.Random(20261005)
        seen = set()
        tally = {}
        for _ in range(limit):
            chans = []
            while len(chans) < k:
                a, b = rng.randint(-cm, cm), rng.randint(-cm, cm)
                if max(a, 0) + max(b, 0) < 1:
                    continue
                chans.append((a, b, [rng.randrange(g)]))
            key = tuple(sorted((a, b, tuple(w)) for a, b, w in chans))
            if key in seen:
                continue
            seen.add(key)
            verdict, detail = classify(g, chans)
            tally[verdict] = tally.get(verdict, 0) + 1
            if verdict == "indep" and not single_combo_trivial(chans, detail):
                spec = " ".join(f"{a},{b},{''.join(map(str, w))}" for a, b, w in chans)
                print(f"INDEP {spec}  witnesses={detail}", flush=True)
        print("tally", tally)


if __name__ == "__main__":
    main()
