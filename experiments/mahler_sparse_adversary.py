#!/usr/bin/env python3
"""Sparse adversaries for the hitting-set invariant: an elementary LOWER-BOUND construction.

For alpha = sum_j B_j g^(-n_j) with integers B_j >= 1 and gaps n_(j+1) - n_j growing, the base-g
expansion of m*alpha is the digit string of the integer m*B_j at position n_j, padded by zeros, for
every m (once the gaps exceed len(m B_j) + k the blocks never interact).  So a k-block W != 0^k
occurs infinitely often in m*alpha iff W is a substring of 0^(k-1) digits_g(m B_j) 0^(k-1) for
infinitely many j.  Hence: if for a set S some block W != 0^k is avoided by 0^(k-1) digits(m B) 0^(k-1)
for every m in S and ONE B >= 1, then S is not a per-block hitting set: take B_j = B for all j;
alpha is irrational because the gaps grow (arbitrarily long zero runs, so no eventual period).
Berend-Boshernitzan 1994 s3 is the case B = 1 (blocks of m*alpha are the digits of m).  (An earlier
docstring asked for infinitely many B; one suffices.)

Prime base, k = 1 (proved 2026-09-13): the last nonzero digit of m*B is m'*B' mod p (primes = the
p-free parts), so if the p-free residues of S cover every nonzero class, the last digits of {m*B}
already show every nonzero digit for every B, and S has NO sparse adversary.  Base 5, quads <= 30:
the 2857 sets with no avoider below 4096 are exactly the 2857 residue-covering ones.  Conjecture
(data: every non-covering quad <= 30 at base 5, 391 random non-covering 5-sets <= 40 at base 7):
the converse - a set whose p-free residues miss a class has a sparse adversary - which would give
S(p,1) >= p-1 for every prime p.

This is a probe, not a proof: it counts B <= BMAX and reports the block with the most avoiders;
a uniform construction of B in terms of S is what a theorem needs.  Soundness control against the exact automaton (mahler_hitting_set.hits_block): every
(S, W) the sparse family defeats must be reported not hit by the automaton - checked on every set
the probe visits (--check).

Usage:  mahler_sparse_adversary.py G K SIZE MMAX [BMAX] [--check]
  enumerates every SIZE-subset of [1..MMAX] with gcd 1, prints the best block and its avoider count,
  and lists the subsets the sparse family does NOT defeat within BMAX (candidates for a genuinely
  non-sparse adversary, or for a hitting set).
"""
import sys, os, time
from math import gcd
from itertools import product, combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def digits(n, g):
    out = []
    while n:
        out.append(n % g); n //= g
    return tuple(reversed(out)) or (0,)


def padded_blocks(n, g, k):
    d = (0,) * (k - 1) + digits(n, g) + (0,) * (k - 1)
    return {d[i:i + k] for i in range(len(d) - k + 1)}


def avoiders(g, k, S, bmax):
    """For each block W != 0^k: the list of B <= bmax such that no m in S has W in the padded digits of m*B."""
    blocks = [W for W in product(range(g), repeat=k) if any(W)]
    out = {W: [] for W in blocks}
    for B in range(1, bmax + 1):
        seen = set()
        for m in S:
            seen |= padded_blocks(m * B, g, k)
        for W in blocks:
            if W not in seen:
                out[W].append(B)
    return out


def probe(g, k, size, mmax, bmax, check=False):
    if check:
        from mahler_hitting_set import hits_block
    t0 = time.time(); undefeated = []; n = 0; worst = None
    for S in combinations(range(1, mmax + 1), size):
        if gcd(*S) != 1:
            continue
        n += 1
        av = avoiders(g, k, S, bmax)
        W, Bs = max(av.items(), key=lambda kv: len(kv[1]))
        if check:
            for W2, Bs2 in av.items():
                if Bs2:                         # sparse family defeats (S, W2) => automaton must agree
                    assert not hits_block(g, k, S, W2), (S, W2, Bs2[:5])
        if not Bs:
            undefeated.append(S)
        elif worst is None or len(Bs) < worst[1]:
            worst = (S, len(Bs), W, Bs[:6])
    print(f"g={g} k={k} size {size} over [1..{mmax}], B <= {bmax}: {n} primitive sets, "
          f"{len(undefeated)} not defeated by any sparse family; thinnest defeated: {worst} [{time.time()-t0:.1f}s]", flush=True)
    if undefeated:
        print("  undefeated:", undefeated[:20], flush=True)
    return undefeated


if __name__ == "__main__":
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    g, k, size, mmax = map(int, a[:4]); bmax = int(a[4]) if len(a) > 4 else 4096
    probe(g, k, size, mmax, bmax, check="--check" in sys.argv)
