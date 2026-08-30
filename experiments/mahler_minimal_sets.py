#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: minimal Mahler sets - single-track machine, exhaustive (Babel #4c).

Mahler 1973 / Berend-Boshernitzan 1994: for irrational alpha, base g, word w,
some multiple m*alpha (m <= 2g^(k+1)) contains w i.o.  This probe runs the
adder machine in Mahler's own single-track setting (channels m*x, digit
v mod g, carry v div g, carry range [0, m]) and EXHAUSTIVELY enumerates the
minimal multiple sets for single digits in base 3:

    which sets S of multiples force "digit d occurs i.o. in m*x for some
    m in S, for EVERY irrational x"?

A set collapses (exact h = 0) iff joint avoidance kills all aperiodic
streams.  Exhaustive over S subset of {1..M_MAX}, |S| <= 4, per digit d.
Regression owed to the two-track wing: {1,2,4,5} for digit 1 (the y=x
instance of the escape-from-Cantor collapse) must collapse here too (the
diagonal is a subvariety, so its entropy is <= the two-track system's).

The finding either way: the exact minimal-set landscape vs the B-B bounds
(upper 2g^(k+1) = 18, lower g^k - 1 = 2 for their adversary-word problem).
"""

import sys
import time
from itertools import combinations
from math import log2
import numpy as np

G = 3
M_MAX = 12
MAX_SIZE = 4
STATE_CAP = 4_000_000
POWER_ITERS = 100


class Mult:
    """Channel m*x avoiding digit d, single track, base G."""

    def __init__(self, m: int, d: int):
        self.m, self.d = m, d
        n_carry = m + 1  # carries 0..m (fixed point of ((G-1)m + c)/G)
        self.n_states = n_carry
        nxt = np.full((n_carry, G), -1, dtype=np.int64)
        for c in range(n_carry):
            for x in range(G):
                v = m * x + c
                z = v % G
                c2 = v // G
                if c2 > m or z == d:
                    continue
                nxt[c, x] = c2
        self.nxt = nxt


def build_nxts(channels):
    sizes = [ch.n_states for ch in channels]
    S = int(np.prod(sizes)) if channels else 1
    idx = np.arange(S, dtype=np.int64)
    digits = []
    rem = idx
    for ch in channels:
        digits.append(rem % ch.n_states)
        rem = rem // ch.n_states
    nxts = []
    for sym in range(G):
        nx = np.zeros(S, dtype=np.int64)
        dead = np.zeros(S, dtype=bool)
        mult = 1
        for dg, ch in zip(digits, channels):
            step = ch.nxt[dg, sym]
            dead |= step < 0
            nx += np.where(step < 0, 0, step) * mult
            mult *= ch.n_states
        nx[dead] = -1
        nxts.append(nx)
    return S, nxts


def entropy(channels):
    S = int(np.prod([c.n_states for c in channels])) if channels else 1
    if S > STATE_CAP:
        return float("nan")
    S, nxts = build_nxts(channels)
    v = np.ones(S, dtype=np.float64)
    growth = []
    for _ in range(POWER_ITERS):
        w = np.zeros(S, dtype=np.float64)
        for nx in nxts:
            live = nx >= 0
            np.add.at(w, nx[live], v[live])
        total = w.sum()
        if total == 0:
            return float("-inf")
        growth.append(total / v.sum() if v.sum() else 0)
        v = w / total * S
    lam = float(np.median(growth[-15:]))
    return log2(lam) if lam > 0 else float("-inf")


def exact_zero(channels):
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import connected_components

    S, nxts = build_nxts(channels)
    alive = np.ones(S, dtype=bool)
    while True:
        out_deg = np.zeros(S, dtype=np.int64)
        for nx in nxts:
            ok = (nx >= 0) & alive
            ok[ok] &= alive[nx[ok]]
            out_deg += ok
        new_alive = alive & (out_deg > 0)
        if new_alive.sum() == alive.sum():
            break
        alive = new_alive
    rows, cols = [], []
    for nx in nxts:
        ok = (nx >= 0) & alive
        ok[ok] &= alive[nx[ok]]
        src = np.flatnonzero(ok)
        rows.append(src)
        cols.append(nx[src])
    rows, cols = np.concatenate(rows), np.concatenate(cols)
    if len(rows) == 0:
        return True
    g = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)),
                   shape=(S, S))
    n_comp, labels = connected_components(g, directed=True, connection="strong")
    same = labels[rows] == labels[cols]
    intra_out = np.bincount(rows[same], minlength=S)
    comp_size = np.bincount(labels[alive], minlength=n_comp)
    for comp in np.flatnonzero(comp_size > 0):
        members = np.flatnonzero((labels == comp) & alive)
        intra = intra_out[members]
        if len(members) == 1 and intra[0] == 0:
            continue
        if not (intra == 1).all():
            return False
    return True


def main() -> None:
    # self-tests: full shift log2(3); single channel m=1 avoid d leaves a
    # full shift on 2 digits (log2 2); regression {1,2,4,5} digit 1.
    assert abs(entropy([]) - log2(3)) < 1e-9
    h1 = entropy([Mult(1, 1)])
    assert abs(h1 - 1.0) < 1e-3, h1
    reg = [Mult(m, 1) for m in (1, 2, 4, 5)]
    hreg = entropy(reg)
    assert hreg <= 1e-3 and exact_zero(reg), \
        f"regression: {{1,2,4,5}} digit-1 single-track h={hreg}"
    print(f"self-tests OK (log2 3, m=1 leaves 1 bit, {{1,2,4,5}}/digit-1 "
          f"collapses single-track too)\n")

    for d in range(G):
        print(f"=== digit {d}: exhaustive over S in {{1..{M_MAX}}}, "
              f"|S| <= {MAX_SIZE} ===")
        minimal = []
        t0 = time.time()
        for size in range(1, MAX_SIZE + 1):
            hits = []
            for S_ in combinations(range(1, M_MAX + 1), size):
                if any(set(m).issubset(S_) for m in minimal):
                    continue  # not minimal
                chans = [Mult(m, d) for m in S_]
                h = entropy(chans)
                if np.isnan(h) or h > 1e-3:
                    continue
                if h == float("-inf"):
                    continue  # empty automaton: vacuous, not a theorem
                if exact_zero(chans):
                    hits.append(S_)
            for S_ in hits:
                minimal.append(set(S_))
                print(f"  MINIMAL collapse: {set(S_)}")
            if hits and size == min(len(m) for m in minimal):
                pass
        if minimal:
            k = min(len(m) for m in minimal)
            print(f"  -> smallest set size for digit {d}: {k}  "
                  f"[{time.time()-t0:.0f}s]\n")
        else:
            print(f"  -> NO collapsing set within range "
                  f"[{time.time()-t0:.0f}s]\n")
    print("done.  (Every set above is a theorem: for ANY irrational x, some "
          "m in S has digit d i.o. in base 3 of m*x - explicit Mahler sets.)")


if __name__ == "__main__":
    sys.exit(main())
