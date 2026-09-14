#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Hitting-set search, second instrument: channel reduction, sparse prefilter, constant blocks first.

Three facts the naive search (mahler_hitting_set.py) did not use:

1. Channel `g*m` is channel `m` shifted one digit, so a multiplier divisible by `g` adds nothing to a
   set that has (or could have) `m`; and `c*S` hits iff `S` hits (alpha -> alpha/c).  So the
   candidates are the `m <= mmax` with `g` not dividing `m`, and only primitive sets (gcd 1) are
   enumerated.  The counts are then CHANNEL-DISTINCT: the "928 hitting 4-sets below 60" of the naive
   search at (2,3) were `{1,3,5,7}` and its relatives with elements doubled, and the "unique below 40"
   entries in the 2026-09-13 doc came from early-exit runs, not from counts.
2. Complement symmetry: alpha -> 1 - alpha complements every digit of every m*alpha, so `S` hits `W`
   iff `S` hits the complement of `W`; half the blocks need no automaton.
3. A sparse adversary (SparseAdversary.lean, node N1) defeats `S` at a block `W != 0^k` as soon as one
   `B >= 1` has `W` in no padded digit string of `m*B`, `m in S`.  Per multiplier and block that is a
   bitmask over `B <= bmax`; a set is defeated iff the AND of its masks is nonzero for some block,
   one numpy op per set along the lexicographic enumeration (prefix ANDs are reused).  Only the
   survivors of that filter go to the product automaton, constant blocks first (they are the
   thinnest in every row of the table), stopping at the first block the set fails.

The automaton verdict is the theorem-grade one (`checkCertA` / `escape_lower_bound`); the sparse
filter only decides "not hitting" and only for `B <= bmax`, so a survivor is not a hitter until the
automaton says so.  Known-answer control: `--selftest` reduces the naive search's families at
(3,1), (2,2), (4,1) by channel and scaling and checks they equal this instrument's.

Usage:
  hitting_set_search.py G K SIZE MMAX [--bmax B] [--sizes S1,S2,...]
  hitting_set_search.py --selftest
"""
import sys, os, time
from functools import reduce
from itertools import product, combinations
from math import gcd
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mahler_hitting_set import hits_block, minimal_hitting
from mahler_sparse_adversary import padded_blocks


def candidates(g, mmax):
    return [m for m in range(1, mmax + 1) if m % g]


def block_order(g, k):
    """All k-blocks, constant blocks first, one representative per complement pair."""
    blocks = list(product(range(g), repeat=k))
    const = [W for W in blocks if len(set(W)) == 1]
    rest = [W for W in blocks if len(set(W)) > 1]
    seen, order = set(), []
    for W in const + rest:
        if W in seen:
            continue
        order.append(W)
        seen.add(W); seen.add(tuple(g - 1 - d for d in W))
    return order


def sparse_masks(g, k, cands, bmax):
    """m -> packed uint8 array [nonzero blocks, bits over B in 0..bmax]; bit set iff W absent from m*B."""
    nz = [W for W in product(range(g), repeat=k) if any(W)]
    idx = {W: i for i, W in enumerate(nz)}
    masks = {}
    for m in cands:
        arr = np.ones((len(nz), bmax + 1), dtype=bool)
        arr[:, 0] = False
        for B in range(1, bmax + 1):
            for W in padded_blocks(m * B, g, k):
                if any(W):
                    arr[idx[W], B] = False
        masks[m] = np.packbits(arr, axis=1)
    return masks


def search(g, k, size, mmax, bmax=1 << 15, verbose=True):
    """All primitive channel-distinct hitting `size`-sets of candidates <= mmax.  Returns (found, stats)."""
    t0 = time.time()
    cands = candidates(g, mmax)
    masks = sparse_masks(g, k, cands, bmax)
    order = block_order(g, k)
    t1 = time.time()
    n_sets = n_prim = n_surv = 0
    found, failed_at = [], {}
    prev, pref = None, [None] * size
    for T in combinations(cands, size):
        n_sets += 1
        d = 0
        if prev is not None:
            while d < size and T[d] == prev[d]:
                d += 1
        for j in range(d, size):
            pref[j] = masks[T[j]] if j == 0 else pref[j - 1] & masks[T[j]]
        prev = T
        if reduce(gcd, T) != 1:
            continue
        n_prim += 1
        if pref[size - 1].any():
            continue
        n_surv += 1
        bad = next((W for W in order if not hits_block(g, k, T, W)), None)
        if bad is None:
            found.append(T)
        else:
            failed_at[bad] = failed_at.get(bad, 0) + 1
    stats = dict(sets=n_sets, primitive=n_prim, survivors=n_surv, hitting=len(found),
                 mask_s=t1 - t0, total_s=time.time() - t0, failed_at=failed_at)
    if verbose:
        print(f"g={g} k={k} size {size}, candidates <= {mmax} (g-free: {len(cands)}), bmax={bmax}: "
              f"{n_prim} primitive sets, {n_surv} pass the sparse filter, {len(found)} hitting"
              f"{': ' + str(found[:12]) if found else ''}; automaton failures by block "
              f"{ {''.join(map(str, W)): c for W, c in failed_at.items()} } "
              f"[masks {t1-t0:.0f}s, total {time.time()-t0:.0f}s]", flush=True)
    return found, stats


def reduce_family(g, sets, size):
    """Channel- and scaling-reduce a family of the naive search; keep those still of the given size."""
    out = set()
    for S in sets:
        red = []
        for m in S:
            while m % g == 0:
                m //= g
            red.append(m)
        red = sorted(set(red))
        if len(red) != size:
            continue
        d = reduce(gcd, red)
        out.add(tuple(x // d for x in red))
    return out


def selftest():
    for (g, k, size, mmax) in [(3, 1, 2, 12), (2, 2, 2, 20), (4, 1, 3, 20), (2, 1, 1, 6)]:
        _, naive = minimal_hitting(g, k, mmax, smax=size, all_sets=True)
        want = reduce_family(g, naive, size)
        got, _ = search(g, k, size, mmax, bmax=2000, verbose=False)
        assert set(got) == want, (g, k, size, mmax, sorted(want), sorted(got))
        print(f"selftest ({g},{k}) size {size} <= {mmax}: {len(got)} channel-distinct sets == reduced naive family")
    got, st = search(2, 3, 4, 20, bmax=2000, verbose=False)
    assert (1, 3, 5, 7) in got, got
    got3, st3 = search(2, 3, 3, 20, bmax=2000, verbose=False)
    assert got3 == [] and st3["survivors"] == 0, (got3, st3)
    print(f"selftest (2,3): {{1,3,5,7}} found among {len(got)} 4-sets <= 20; no triple survives the sparse filter")
    print("selftest ok")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args == ["--selftest"]:
        selftest()
    else:
        g, k, size, mmax = map(int, args[:4])
        bmax = int(args[args.index("--bmax") + 1]) if "--bmax" in args else 1 << 15
        sizes = [int(x) for x in args[args.index("--sizes") + 1].split(",")] if "--sizes" in args else [size]
        for s in sizes:
            found, _ = search(g, k, s, mmax, bmax=bmax)
            if found:
                break
