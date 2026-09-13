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

Usage:
  mahler_hitting_set.py G K MMAX [SMAX] [--all]        minimal per-block hitting size over S subset [1..MMAX]
  mahler_hitting_set.py G K MMAX --disjunctive [SMAX]  same for the disjunctive variant
  mahler_hitting_set.py --selftest                     S(3,1)=2 with {1,2} and {2,11} among the pairs
"""
import sys, os, time
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
        print("selftest: S(3,1)=2 per-block, {1,2} and {2,11} hit; {1} does not; S(2,1)=1")
    else:
        g, k, mmax = int(args[0]), int(args[1]), int(args[2])
        disj = "--disjunctive" in args
        rest = [a for a in args[3:] if not a.startswith("--")]
        smax = int(rest[0]) if rest else 4
        minimal_hitting(g, k, mmax, smax=smax, disjunctive=disj, all_sets="--all" in args)
