#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: Pythagorean closure - non-greedy word search on the musical family.

The superparticular (borrow) channel set
    ln 2      (1, 0)      ln 3      (0, 1)
    ln 3/2    (-1, 1)     ln 4/3    (2, -1)
    ln 9/8    (-3, 2)     ln 6      (1, 1)
stalled at h = 0.0080 under GREEDY word assignment (adder_family_enum).
Greedy is not exhaustive: this probe runs a BEAM search over open-word
assignments (complement-involution deduped - f and ~f have equal entropy,
so only canonical representatives are scored), exact-checking every float
zero.  If the six-set won't close, the best floors get a seventh Pythagorean
channel: ln 16/9 = (4, -2), ln 32/27 = (5, -3).

A hit is the musical disjunction theorem: for ANY reals X, Y not both
rational, at least one word of the tuple occurs i.o. in one of the
interval-lattice channels.  A miss maps the floor properly (W3 currency:
the entropy budget of joint pathology across the circle of fifths).

Beam is a heuristic (misses are inconclusive); hits are exact (integer
graph).  One-sided soundness, per the operating rules.
"""

import sys
import time
from math import log2
import numpy as np
from adder_collapse_hunt import build_nxts, joint_entropy
from adder_family_enum import GenChannel, exact_zero

MUSICAL = [(1, 0), (0, 1), (-1, 1), (2, -1), (-3, 2), (1, 1)]
SEVENTHS = [(4, -2), (5, -3)]
WORDS_OPEN = ["00", "11", "000", "001", "010", "011", "100", "101", "110", "111"]
COMP = str.maketrans("01", "10")
BEAM = 300
STATE_CAP = 2_000_000
SCREEN_ITERS = 40


def comp_tuple(ws):
    return tuple(w.translate(COMP) for w in ws)


def entropy_screen(channels, iters=SCREEN_ITERS) -> float:
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
    lam = float(np.median(growth[-10:]))
    return log2(lam) if lam > 0 else float("-inf")


def beam_search(abset, beam_width=BEAM):
    """Beam over word assignments channel-by-channel; returns sorted final
    (h, words) list.  Canonical dedupe via the complement involution."""
    frontier = [(0.0, tuple())]
    for (a, b) in abset:
        seen = set()
        nxt_frontier = []
        for _, ws in frontier:
            for w in WORDS_OPEN:
                ws2 = ws + (w,)
                canon = min(ws2, comp_tuple(ws2))
                if canon in seen:
                    continue
                seen.add(canon)
                chans = [GenChannel(aa, bb, ww)
                         for (aa, bb), ww in zip(abset, ws2)]
                h = entropy_screen(chans)
                if np.isnan(h) or h == float("-inf"):
                    continue  # cap or empty (empty = vacuous, not a theorem)
                nxt_frontier.append((h, ws2))
        nxt_frontier.sort(key=lambda t: t[0])
        frontier = nxt_frontier[:beam_width]
        if not frontier:
            return []
    return frontier


def report_hit(abset, ws) -> bool:
    chans = [GenChannel(a, b, w) for (a, b), w in zip(abset, ws)]
    ok, live, periods = exact_zero(chans)
    if not ok:
        return False
    print(f"\n*** EXACT COLLAPSE ({live} live states, periods {periods}) ***")
    for (a, b), w in zip(abset, ws):
        print(f"    2^{a} 3^{b} avoids '{w}'")
    return True


def main() -> None:
    # self-tests: regression + involution on a borrow family (empirical)
    base = [(1, 0, "00"), (0, 1, "001"), (1, 1, "11"),
            (1, 2, "001"), (2, 1, "010"), (1, 3, "000")]
    ok, _, _ = exact_zero([GenChannel(*t) for t in base])
    assert ok, "regression: base family lost its collapse"
    hb = joint_entropy([GenChannel(-1, 1, "001"), GenChannel(2, -1, "11")])
    hbc = joint_entropy([GenChannel(-1, 1, "110"), GenChannel(2, -1, "00")])
    assert abs(hb - hbc) < 5e-3, f"involution off on borrows: {hb} vs {hbc}"
    print(f"self-tests OK (regression; borrow involution {hb:.4f}={hbc:.4f})\n")

    t0 = time.time()
    print(f"beam search on the musical six (beam {BEAM}, canonical only):")
    finals = beam_search(MUSICAL)
    print(f"  beam done in {time.time()-t0:.0f}s; best floors:")
    for h, ws in finals[:8]:
        print(f"    h = {h:.4f}  {ws}")
    hit = False
    for h, ws in finals:
        if h <= 1e-3 and report_hit(MUSICAL, ws):
            hit = True
            break
    if hit:
        print("\n🎵 the musical disjunction closes on six channels")
        return

    print(f"\nno six-channel closure (floor {finals[0][0]:.4f}); "
          "trying sevenths:")
    for seventh in SEVENTHS:
        abset7 = MUSICAL + [seventh]
        best7 = None
        for h6, ws in finals[:50]:
            for w in WORDS_OPEN:
                chans = [GenChannel(a, b, ww)
                         for (a, b), ww in zip(abset7, ws + (w,))]
                h = entropy_screen(chans)
                if np.isnan(h) or h == float("-inf"):
                    continue
                if best7 is None or h < best7[0]:
                    best7 = (h, ws + (w,))
                if h <= 1e-3 and report_hit(abset7, ws + (w,)):
                    print(f"\n🎵 the musical disjunction closes with "
                          f"seventh channel 2^{seventh[0]} 3^{seventh[1]}")
                    return
        if best7:
            print(f"  seventh {seventh}: floor h = {best7[0]:.4f} "
                  f"at {best7[1]}")
    print("\nno closure; the floors above are the finding (W3 budget of the "
          "circle of fifths).  done.")


if __name__ == "__main__":
    sys.exit(main())
