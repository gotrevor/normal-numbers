"""Per-DIGIT minimal collapsing subsets: for each base-g digit w, the smallest
subset of {1..M} whose single-track adder family collapses.  The Mahler upper
bound M(g,1) <= M only needs, for each w SEPARATELY, some subset of {1..M} to
collapse -- so different digits may use different (much smaller) families than
the common subset that `mahler_subset_hunt.py` looks for."""
import sys
from itertools import combinations
sys.path.insert(0, __import__('os').path.dirname(__file__))
from mahler_subset_hunt import collapses

def main():
    g = int(sys.argv[1]); M = int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 60000
    cands = []
    for r in range(1, M + 1):
        for sub in combinations(range(1, M + 1), r):
            p = 1
            for a in sub: p *= a
            if p <= cap: cands.append((p, sub))
    cands.sort()
    total = 1
    for w in range(g):
        found = None
        for p, sub in cands:
            ok, nl = collapses(g, list(sub), w)
            if ok:
                found = (p, sub, nl); break
        if found:
            print(f"w={w}: ambient={found[0]:7d} subset={found[1]} live={found[2]}", flush=True)
            total += found[0]
        else:
            print(f"w={w}: NONE under cap {cap}", flush=True)
    print("sum of ambients:", total)

main()
