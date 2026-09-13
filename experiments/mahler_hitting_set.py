#!/usr/bin/env python3
"""Hitting-set invariant S(g,k): the least CARDINALITY of a multiplier set S such that every
irrational alpha has every k-block occurring infinitely often in the base-g expansion of m*alpha for
some m in S (the multiplier may depend on the block: the PER-BLOCK variant).  Contrast M(g,k), the
least M such that the initial segment {1..M} works (mahler_exact_M.py): S need not be an initial
segment - {2, 11} forces all ternary digits (AdderTowerC2.lean) as does Berend-Boshernitzan's {1, 2}.

Instrument: the channel-product adder automaton of mahler_exact_M.py, run on an arbitrary set S
instead of 1..M.  A block W is HIT by S iff the trimmed product of the channel graphs for m in S
has no nontrivial SCC (a lone cycle = one eventually periodic digit string = a rational, and is
trimmed; a branching SCC = uncountably many escaping irrationals).  S is a per-block hitting set
iff every W is hit.  The DISJUNCTIVE variant (one m in S serving all blocks of a given alpha) is
the stronger condition: for every choice (W_m)_{m in S} the product of channel(m, W_m) collapses.

Layered search (default for the per-block variant): hitting is monotone in S, so the blocks hit by
S include every block hit by an (|S|-1)-subset; a layer caches, per subset, the bitmask of blocks it
hits, and the product automaton runs only on (S, W) with W hit by NO proper subset.  Scaling: c*S
hits iff S hits (alpha -> alpha/c), so a non-primitive S copies the mask of S/gcd.  Known-answer
controls (the naive search, 2026-09-13): 151 hitting pairs at (2,2) below 60, 35 hitting triples
at (4,1) below 60, 162 pairs at (3,1) below 40.

Usage:
  mahler_hitting_set.py G K MMAX [SMAX]                minimal per-block hitting size over S subset [1..MMAX] (layered)
  mahler_hitting_set.py G K MMAX [SMAX] --naive [--all] the same by brute force (every subset, every block)
  mahler_hitting_set.py G K MMAX --disjunctive [SMAX]  the disjunctive variant (brute force)
  mahler_hitting_set.py --selftest                     S(3,1)=2 with {1,2} and {2,11} among the pairs; layered == naive
"""
import sys, os, time
from math import gcd
from itertools import product, combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mahler_exact_M import channel_graph, prod_graph, nontrivial_scc_trim


def product_collapses(g, k, channels):
    """channels: list of (m, W).  True iff the trimmed product has no nontrivial SCC."""
    m0, W0 = channels[0]
    n1, e1 = channel_graph(g, k, m0, tuple(W0))
    nodes = [(w, (c,)) for (w, c) in n1]
    edges = {(w, (c,)): [(l, (t[0], (t[1],))) for (l, t) in e1[(w, c)]] for (w, c) in n1}
    nodes, edges = nontrivial_scc_trim(nodes, edges)
    for m, W in channels[1:]:
        if not nodes:
            return True
        nodes, edges = prod_graph((nodes, edges), channel_graph(g, k, m, tuple(W)))
        nodes, edges = nontrivial_scc_trim(nodes, edges)
    return not nodes


def hits_block(g, k, S, W):
    return product_collapses(g, k, [(m, W) for m in S])


def is_hitting(g, k, S):
    return all(hits_block(g, k, S, W) for W in product(range(g), repeat=k))


def is_disjunctive_hitting(g, k, S):
    """For every assignment of a block W_m to each m in S, the product collapses."""
    blocks = list(product(range(g), repeat=k))
    return all(product_collapses(g, k, list(zip(S, choice)))
               for choice in product(blocks, repeat=len(S)))


def minimal_hitting_layered(g, k, mmax, smax=5):
    """Least s with a per-block hitting s-subset of [1..mmax], and all such subsets; layered cache."""
    blocks = list(product(range(g), repeat=k)); full = (1 << len(blocks)) - 1
    prev = {}
    for s in range(1, smax + 1):
        t0 = time.time(); prods = 0; cur = {}; found = []
        for T in combinations(range(1, mmax + 1), s):
            d = gcd(*T)
            if d > 1:
                mask = cur[tuple(t // d for t in T)]          # lex-earlier, already computed
            else:
                mask = 0
                for T2 in combinations(T, s - 1):
                    mask |= prev.get(T2, 0)
                for i, W in enumerate(blocks):
                    if not (mask >> i) & 1:
                        prods += 1
                        if hits_block(g, k, T, W):
                            mask |= 1 << i
            cur[T] = mask
            if mask == full:
                found.append(T)
        print(f"g={g} k={k} per-block size {s} over [1..{mmax}]: {len(found)} hitting set(s)"
              f"{': ' + str(found[:12]) if found else ''} [{prods} products of {len(cur) * len(blocks)}, "
              f"{time.time() - t0:.1f}s]", flush=True)
        if found:
            return s, found
        prev = cur
    return None, []


def minimal_hitting(g, k, mmax, smax=4, disjunctive=False, all_sets=False):
    test = is_disjunctive_hitting if disjunctive else is_hitting
    for s in range(1, smax + 1):
        found = []
        t0 = time.time()
        for S in combinations(range(1, mmax + 1), s):
            if test(g, k, S):
                found.append(S)
                if not all_sets:
                    break
        print(f"g={g} k={k} {'disjunctive' if disjunctive else 'per-block'} size {s} over [1..{mmax}]: "
              f"{len(found)} hitting set(s){': ' + str(found[:12]) if found else ''} [{time.time()-t0:.1f}s]", flush=True)
        if found:
            return s, found
    return None, []


if __name__ == "__main__":
    args = sys.argv[1:]
    if args == ["--selftest"]:
        s, found = minimal_hitting(3, 1, 12, smax=2, all_sets=True)
        assert s == 2 and (1, 2) in found and (2, 11) in found, found
        assert not is_hitting(3, 1, (1,)) and is_hitting(2, 1, (1,))
        s2, found2 = minimal_hitting_layered(3, 1, 12, smax=2)
        assert (s2, found2) == (s, found), (found2, found)
        s3, found3 = minimal_hitting_layered(2, 2, 20, smax=2)
        assert s3 == 2 and found3 == minimal_hitting(2, 2, 20, smax=2, all_sets=True)[1], found3
        print("selftest: S(3,1)=2 per-block, {1,2} and {2,11} hit; {1} does not; S(2,1)=1; layered == naive at (3,1) and (2,2)")
    else:
        g, k, mmax = int(args[0]), int(args[1]), int(args[2])
        disj = "--disjunctive" in args
        rest = [a for a in args[3:] if not a.startswith("--")]
        smax = int(rest[0]) if rest else 4
        if disj or "--naive" in args:
            minimal_hitting(g, k, mmax, smax=smax, disjunctive=disj, all_sets="--all" in args)
        else:
            minimal_hitting_layered(g, k, mmax, smax=smax)
