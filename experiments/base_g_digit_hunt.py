#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: single-digit adder collapses in base g (g = 4, 5, ... ) - Babel #4b.

Generalizes base3_digit_hunt.py: digit = v mod g, carry = v div g, carry
range [a^- + b^-, a^+ + b^+] (same fixed-point/superset soundness).  The
open frontier is single digits for every g >= 3.

Interesting bits per base:
  g=4: avoiding a base-4 digit = avoiding a 2-bit binary word at EVEN-ALIGNED
       positions - a positioned-binary currency the base-2 machine cannot
       express.  Cut/channel log2(4/3) = 0.415; ~10 channels predicted.
  g=5: central digit 2 is the involution fixed point (escape from the base-5
       Cantor set); cut/channel log2(5/4) = 0.322, ~14 channels predicted -
       the wing where "base 3 is the sweet spot" gets quantified.

Method: general greedy (channel + digit free), then beam over (channel-set,
digit-assignment) pairs.  Hits exact-checked (integer graph); floors are
one-sided (beam is a heuristic).

Usage: base_g_digit_hunt.py G [BEAM] [MAX_K]
"""

import sys
import time
from math import log2
import numpy as np


def make_base(G):
    NSYM = G * G

    class ChannelG:
        def __init__(self, a, b, digit):
            self.a, self.b, self.word = a, b, str(digit)
            d = int(digit)
            c_min = min(a, 0) + min(b, 0)
            c_max = max(a, 0) + max(b, 0)
            self.c_min, self.c_max = c_min, c_max
            n_carry = c_max - c_min + 1
            self.n_states = n_carry
            nxt = np.full((n_carry, NSYM), -1, dtype=np.int64)
            for ci in range(n_carry):
                c = c_min + ci
                for sym in range(NSYM):
                    x, y = sym % G, sym // G
                    v = a * x + b * y + c
                    z = v % G
                    c2 = v // G
                    if not (c_min <= c2 <= c_max):
                        continue
                    if z == d:
                        continue  # emitted the avoided digit: dead
                    nxt[ci, sym] = c2 - c_min
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
        for sym in range(NSYM):
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

    return ChannelG, build_nxts, NSYM


STATE_CAP = 4_000_000
POWER_ITERS = 100


def entropy(build_nxts, channels, iters=POWER_ITERS):
    S = int(np.prod([c.n_states for c in channels])) if channels else 1
    if S > STATE_CAP:
        return float("nan")
    S, nxts = build_nxts(channels)
    v = np.ones(S, dtype=np.float64)
    growth = []
    for _ in range(iters):
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


def exact_zero(build_nxts, channels):
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
        return True, 0
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
            return False, int(alive.sum())
    return True, int(alive.sum())


def main() -> None:
    G = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    BEAM = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    MAX_K = int(sys.argv[3]) if len(sys.argv) > 3 else 16
    ChannelG, build_nxts, NSYM = make_base(G)

    # self-tests
    h0 = entropy(build_nxts, [])
    assert abs(h0 - 2 * log2(G)) < 1e-9, h0
    h1 = entropy(build_nxts, [ChannelG(1, 0, G - 1)])
    assert abs(h1 - log2((G - 1) * G)) < 1e-3, h1
    ha = entropy(build_nxts, [ChannelG(1, 2, 0), ChannelG(2, 1, 1)])
    hb = entropy(build_nxts, [ChannelG(1, 2, G - 1), ChannelG(2, 1, G - 2)])
    assert abs(ha - hb) < 5e-3, (ha, hb)
    print(f"base {G} self-tests OK (2log2({G}), one-track, involution "
          f"{ha:.4f}={hb:.4f}); predicted channels ~ "
          f"{2 * log2(G) / log2(G / (G - 1)):.1f}\n")

    pool = [(a, b) for a in range(5) for b in range(5) if (a, b) != (0, 0)]
    pool += [(-1, 1), (2, -1), (-3, 2)]

    print(f"beam over (channel set, digit assignment), beam {BEAM}:")
    t0 = time.time()
    frontier = [(entropy(build_nxts, [ChannelG(a, b, d)]), ((a, b, d),))
                for (a, b) in pool for d in range(G)]
    frontier = [(h, s) for h, s in frontier if not np.isnan(h)]
    frontier.sort(key=lambda t: t[0])
    frontier = frontier[:BEAM]
    for k in range(2, MAX_K + 1):
        seen = set()
        nxt = []
        capped = 0
        for _, subset in frontier:
            used = {(a, b) for a, b, _ in subset}
            for cand in pool:
                if cand in used:
                    continue
                for d in range(G):
                    s2 = tuple(sorted(subset + ((cand[0], cand[1], d),)))
                    if s2 in seen:
                        continue
                    seen.add(s2)
                    h = entropy(build_nxts,
                                [ChannelG(a, b, dd) for a, b, dd in s2])
                    if np.isnan(h):
                        capped += 1
                        continue
                    if h == float("-inf"):
                        continue
                    nxt.append((h, s2))
        if not nxt:
            print(f"  k={k}: everything capped; stopping at the cap wall")
            break
        nxt.sort(key=lambda t: t[0])
        frontier = nxt[:BEAM]
        h, s = frontier[0]
        print(f"  k={k}: best h = {h:.4f}  ({capped} capped)  "
              f"[{time.time()-t0:.0f}s]")
        if h <= 1e-3:
            ok, live = exact_zero(build_nxts,
                                  [ChannelG(a, b, d) for a, b, d in s])
            if ok:
                print(f"\n*** EXACT COLLAPSE, base {G} ({live} live) ***")
                print("*** for any reals X, Y not both rational, at least one "
                      f"holds (base-{G} digits): ***")
                for a, b, d in s:
                    print(f"    digit {d} i.o. in {a}*X + {b}*Y   "
                          f"(instance ln(2^{a} 3^{b}))")
            else:
                print("float zero but exact FAILED")
            return
    print(f"\nbase {G}: no single-digit collapse reached; best floor "
          f"{frontier[0][0]:.4f} at {frontier[0][1]}")
    print("(one-sided: beam + cap; the floor-vs-base curve is the finding)")


if __name__ == "__main__":
    sys.exit(main())
