#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: beam over CHANNEL SETS for the escape-from-Cantor collapse.

The greedy all-avoid-digit-1 hunt (base3_digit_hunt.py) stalled at
h = 0.0068 after 10 channels.  The musical closure taught us greedy floors
are myopia-prone, so: beam search over channel subsets (word fixed = "1" on
every channel), pool widened to a,b <= 4 plus superparticular borrows.

A collapse proves: for ANY reals X, Y not both rational, at least one
channel a*X + b*Y contains ternary digit 1 infinitely often - no channel
family can be jointly Cantor-like (middle-thirds-avoiding).
"""

import sys
import time
import numpy as np
from base3_digit_hunt import Channel3, entropy3, exact_zero3

POOL = [(a, b) for a in range(5) for b in range(5) if (a, b) != (0, 0)]
POOL += [(-1, 1), (2, -1), (-3, 2), (4, -2)]
BEAM = 60
MAX_K = 14


def main() -> None:
    t0 = time.time()
    frontier = [(entropy3([Channel3(a, b, "1")]), ((a, b),))
                for (a, b) in POOL]
    frontier = [(h, s) for h, s in frontier if not np.isnan(h)]
    frontier.sort(key=lambda t: t[0])
    frontier = frontier[:BEAM]
    for k in range(2, MAX_K + 1):
        seen = set()
        nxt = []
        for _, subset in frontier:
            for cand in POOL:
                if cand in subset:
                    continue
                s2 = tuple(sorted(subset + (cand,)))
                if s2 in seen:
                    continue
                seen.add(s2)
                h = entropy3([Channel3(a, b, "1") for a, b in s2])
                if np.isnan(h) or h == float("-inf"):
                    continue
                nxt.append((h, s2))
        if not nxt:
            print("pool/cap exhausted")
            break
        nxt.sort(key=lambda t: t[0])
        frontier = nxt[:BEAM]
        h, s = frontier[0]
        print(f"k={k}: best h = {h:.4f}  {s}  [{time.time()-t0:.0f}s]")
        if h <= 1e-3:
            ok, live, periods = exact_zero3(
                [Channel3(a, b, "1") for a, b in s])
            if ok:
                print(f"\n*** EXACT COLLAPSE ({live} live, periods {periods}) "
                      "***")
                print("*** CANDIDATE THEOREM (escape from Cantor): for any "
                      "reals X, Y not both rational, at least one of the "
                      "channels below contains ternary digit 1 i.o.: ***")
                for a, b in s:
                    print(f"      {a}*X + {b}*Y   (instance ln(2^{a} 3^{b}))")
            else:
                print("float zero but exact check FAILED")
            return
    print(f"\nno Cantor collapse through k={MAX_K}; floor {frontier[0][0]:.4f}"
          f" at {frontier[0][1]} - the finding (W3 budget of joint "
          "middle-thirds pathology).  done.")


if __name__ == "__main__":
    sys.exit(main())
