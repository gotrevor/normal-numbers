#!/usr/bin/env python3
"""Hitting-set search on the REDUCED (carry-consistent) state space.

`hitting_set_search.py` runs the ambient product automaton: states are
(shared window of k-1 digits of alpha, one carry c_m in [0,m) per multiplier),
so the state count is g^(k-1) * prod_{m in S} m and even a 9-element set at
base 2 is out of reach.

The 2026-09-16 carry-consistency reduction (`HittingSetReduced.lean`,
`adder_reduced_emit_ell.py`) removes the product.  Every channel reads the SAME
alpha, so writing t for the value of the unread tail of alpha, the carry of
channel m into the current position is exactly

    c_m = floor(m * t),

i.e. the carry VECTOR lies on a one-parameter curve and there are at most
1 + sum_{m in S} (m-1) of them, not prod m.  Equivalently (and this is what the
code does, so no analytic argument is needed): the states reachable from the
all-zero carry by the transition c_m |-> (m*d + c_m) // g are exactly the
realizable ones, because t |-> (d+t)/g generates the g-adic rationals, which are
dense in every interval between the breakpoints p/m where floor(m t) jumps.
So a forward BFS from ((0,...,0) window, zero carry vector) IS the reduced
state space.  At (2,4) that is 520 states against 4.6e15 ambient.

Restricting the automaton to reachable states is sound for the hitting
question: an escaping alpha is an infinite path read from the deep positions
upward, so it starts at carry floor(m*t) for the tail t and never leaves the
reachable set.  A block W is HIT by S iff the W-avoiding subgraph on the
reachable states has no nontrivial SCC (|E| > |V| inside the component); a lone
cycle is one eventually periodic digit string, i.e. a rational.

Usage:
  hitting_set_search_reduced.py --selftest            # the known rows, exactly
  hitting_set_search_reduced.py check G K M1,M2,...   # is this set hitting?
  hitting_set_search_reduced.py odd G K NMAX          # least n with {1,3,..,2n-1} hitting
  hitting_set_search_reduced.py first G K SIZE MMAX   # first hitting SIZE-set (lex), brute
"""
import sys, os, time
from itertools import product, combinations
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mahler_exact_M import chan_digits


def reduced_space(g, k, S):
    """BFS the reachable (window, carry-vector) states.

    Returns (nodes, trans, blocked) with
      nodes   : list of (window tuple of length k-1, carry tuple)
      trans   : trans[i][x] = index of the successor on digit x
      blocked : blocked[i][x] = frozenset of k-blocks emitted by some channel
    """
    n = len(S)
    start = ((0,) * (k - 1), (0,) * n)
    idx = {start: 0}
    nodes = [start]
    trans, blocked = [], []
    qi = 0
    while qi < len(nodes):
        (w, cs) = nodes[qi]
        row, brow = [], []
        for x in range(g):
            xs = (x,) + w
            nw = xs[:k - 1]
            ncs = tuple((m * xs[-1] + c) // g for m, c in zip(S, cs))
            emitted = frozenset(tuple(chan_digits(m, list(xs), c, g))
                                for m, c in zip(S, cs))
            t = (nw, ncs)
            j = idx.get(t)
            if j is None:
                j = len(nodes); idx[t] = j; nodes.append(t)
            row.append(j); brow.append(emitted)
        trans.append(row); blocked.append(brow)
        qi += 1
    return nodes, trans, blocked


def has_nontrivial_scc(adj):
    """adj: list of lists of successor indices.  True iff some SCC has |E| > |V|."""
    n = len(adj)
    index = [-1] * n; low = [0] * n; onst = [False] * n
    st = []; comp = [-1] * n; cnt = 0; ncomp = 0
    for root in range(n):
        if index[root] != -1:
            continue
        stack = [(root, 0)]
        index[root] = low[root] = cnt; cnt += 1; st.append(root); onst[root] = True
        while stack:
            v, pi = stack[-1]
            if pi < len(adj[v]):
                stack[-1] = (v, pi + 1)
                w = adj[v][pi]
                if index[w] == -1:
                    index[w] = low[w] = cnt; cnt += 1
                    st.append(w); onst[w] = True; stack.append((w, 0))
                elif onst[w]:
                    low[v] = min(low[v], index[w])
                continue
            stack.pop()
            if stack:
                low[stack[-1][0]] = min(low[stack[-1][0]], low[v])
            if low[v] == index[v]:
                while True:
                    u = st.pop(); onst[u] = False; comp[u] = ncomp
                    if u == v:
                        break
                ncomp += 1
    size = [0] * ncomp; ec = [0] * ncomp
    for v in range(n):
        size[comp[v]] += 1
        for w in adj[v]:
            if comp[w] == comp[v]:
                ec[comp[v]] += 1
    return any(ec[c] > size[c] for c in range(ncomp))


class Reduced:
    def __init__(self, g, k, S):
        self.g, self.k, self.S = g, k, tuple(S)
        self.nodes, self.trans, self.blocked = reduced_space(g, k, S)

    def hits_block(self, W):
        W = tuple(W)
        adj = [[t for x, t in enumerate(row) if W not in brow[x]]
               for row, brow in zip(self.trans, self.blocked)]
        return not has_nontrivial_scc(adj)

    def misses(self):
        """The blocks NOT hit by S (empty iff S is a per-block hitting set)."""
        return [W for W in product(range(self.g), repeat=self.k)
                if not self.hits_block(W)]


def is_hitting(g, k, S, report=False):
    t0 = time.time()
    R = Reduced(g, k, S)
    bad = next((W for W in _block_order(g, k) if not R.hits_block(W)), None)
    if report:
        print(f"g={g} k={k} S={list(S)}: {len(R.nodes)} reduced states, "
              f"{'HITTING' if bad is None else 'fails at ' + ''.join(map(str, bad))} "
              f"[{time.time()-t0:.1f}s]", flush=True)
    return bad is None


def _block_order(g, k):
    """Constant blocks first (thinnest), then the rest; one per complement pair is NOT
    sound here (we need every block), so all blocks, just reordered."""
    blocks = list(product(range(g), repeat=k))
    return ([W for W in blocks if len(set(W)) == 1]
            + [W for W in blocks if len(set(W)) > 1])


# ---------------------------------------------------------------- self-test

def selftest():
    from mahler_hitting_set import hits_block as ambient_hits
    ok = True
    # (a) block-by-block agreement with the ambient automaton on small rows
    for (g, k, S) in [(3, 1, (1, 2)), (3, 1, (2, 11)), (3, 1, (1,)), (2, 1, (1,)),
                      (2, 2, (1, 3)), (2, 2, (1, 2)), (4, 1, (1, 2, 3)),
                      (2, 3, (1, 3, 5, 7)), (2, 3, (1, 3, 5)), (3, 2, (1, 2, 4, 5, 7, 8)),
                      (5, 1, (1, 2, 3, 4, 6)), (6, 1, (1, 8, 11, 14, 16, 20, 23))]:
        R = Reduced(g, k, S)
        for W in product(range(g), repeat=k):
            a, b = ambient_hits(g, k, S, W), R.hits_block(W)
            if a != b:
                print(f"MISMATCH g={g} k={k} S={S} W={W}: ambient {a}, reduced {b}")
                ok = False
        print(f"selftest ({g},{k}) S={list(S)}: {len(R.nodes)} reduced states "
              f"(ambient {g**(k-1)}*{'*'.join(map(str,S))}), all {g**k} blocks agree", flush=True)
    # (b) the published rows, exactly: minimal hitting sets stay minimal / stay hitting
    rows = [((2, 4), (1, 3, 5, 7, 9, 11, 13, 15, 17), True),
            ((3, 2), (1, 2, 4, 5, 7, 8), True),
            ((6, 1), (1, 8, 11, 14, 16, 20, 23), True),
            ((7, 1), (1, 2, 3, 4, 5, 6, 13), True),
            ((7, 1), (1, 2, 3, 4, 5, 6, 8), False),
            ((7, 1), (1, 2, 3, 4, 5, 6), False),
            ((7, 1), (1, 2, 3, 4, 5, 6, 8, 9), True),
            ((4, 1), (1, 10, 14), True),
            ((4, 1), (2, 5, 7), True),
            ((2, 2), (1, 11), True),
            ((2, 3), (1, 5, 7, 11), True),
            ((2, 4), (1, 3, 5, 7, 9, 11, 13, 15), False),
            ((5, 1), (1, 2, 3, 4, 6), True),
            ((5, 1), (1, 2, 3, 4), False),
            ((2, 3), (1, 3, 5, 7), True),
            ((2, 3), (1, 3, 5), False)]
    for (g, k), S, want in rows:
        got = is_hitting(g, k, S)
        flag = "ok" if got == want else "MISMATCH"
        if got != want:
            ok = False
        print(f"selftest ({g},{k}) {list(S)} hitting={got} (expected {want}) [{flag}]", flush=True)
    # (c) every proper subset of the published minimal sets must FAIL (minimality)
    for (g, k), S in [((2, 3), (1, 3, 5, 7)), ((5, 1), (1, 2, 3, 4, 6)),
                      ((7, 1), (1, 2, 3, 4, 5, 6, 13)),
                      ((3, 2), (1, 2, 4, 5, 7, 8)), ((6, 1), (1, 8, 11, 14, 16, 20, 23))]:
        bad = [T for T in combinations(S, len(S) - 1) if is_hitting(g, k, T)]
        if bad:
            print(f"MISMATCH ({g},{k}) {list(S)} not minimal: {bad}")
            ok = False
        print(f"selftest ({g},{k}) {list(S)}: minimal (all {len(S)} proper subsets fail)", flush=True)
    print("selftest ok" if ok else "SELFTEST FAILED")
    return ok


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[:1] == ["--selftest"]:
        sys.exit(0 if selftest() else 1)
    cmd = args[0]
    if cmd == "check":
        g, k = int(args[1]), int(args[2])
        S = tuple(int(x) for x in args[3].split(","))
        is_hitting(g, k, S, report=True)
    elif cmd == "odd":
        g, k, nmax = int(args[1]), int(args[2]), int(args[3])
        for n in range(1, nmax + 1):
            S = tuple(range(1, 2 * n, 2))
            if is_hitting(g, k, S, report=True):
                print(f"least odd prefix: n={n}, S={list(S)}")
                break
    elif cmd == "shrink":
        # greedy minimisation by inclusion from a starting hitting set, several orders
        import random
        g, k = int(args[1]), int(args[2])
        S0 = tuple(int(x) for x in args[3].split(","))
        tries = int(args[4]) if len(args) > 4 else 8
        if not is_hitting(g, k, S0, report=True):
            sys.exit("start set is not hitting")
        best = None
        rng = random.Random(20260916)
        for r in range(tries):
            order = list(S0)
            if r:
                rng.shuffle(order)
            cur = list(S0)
            for m in order:
                T = tuple(x for x in cur if x != m)
                if T and is_hitting(g, k, T):
                    cur = list(T)
            cur = tuple(cur)
            if best is None or len(cur) < len(best):
                best = cur
            print(f"  [{r}] minimal-by-inclusion size {len(cur)}: {list(cur)}", flush=True)
        print(f"g={g} k={k}: best minimal-by-inclusion size {len(best)}: {list(best)}")
    elif cmd == "first":
        g, k, size, mmax = (int(x) for x in args[1:5])
        cands = [m for m in range(1, mmax + 1) if m % g]
        for T in combinations(cands, size):
            if gcd(*T) if size > 1 else 1:
                pass
            if is_hitting(g, k, T):
                print(f"g={g} k={k}: hitting {size}-set {list(T)}")
                break
        else:
            print(f"g={g} k={k}: no hitting {size}-set of g-free m <= {mmax}")
