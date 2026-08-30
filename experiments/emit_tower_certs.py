#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Emit per-channel transition tables + verdicts for the 2026-08-29 tower claims.

Output: certs/tower-2026-08-29.json - one entry per claim from
EVIDENCE-2026-08-29-tower-formalization.md, each RE-VERIFIED (exact
integer-graph check) at emission time.  Per-channel tables only (the joint
graph is their product; joint live counts included for cross-checking).

Table format per channel: {a, b, word, base, n_states, c_min,
nxt: [ [next_state or -1 per symbol] per state ]}.
Symbol encoding: two-track sym = x + base*y; single-track sym = x.
State encoding: state = (carry - c_min) * len(word) + kmp  (kmp=0 for digits).
"""

import json
import sys
import numpy as np
from adder_family_enum import GenChannel, exact_zero as xz2
from base3_digit_hunt import Channel3, exact_zero3
from base_g_digit_hunt import make_base, exact_zero as xzg
from mahler_minimal_sets import Mult, exact_zero as xzm

OUT = "certs/tower-2026-08-29.json"


def dump(ch, base, track):
    a = getattr(ch, "a", None)
    if a is None:
        a = ch.m  # single-track Mult channel: coefficient is m
    word = getattr(ch, "word", None)
    if word is None:
        word = str(ch.d)  # Mult stores the avoided digit as d
    return {"a": int(a), "b": int(getattr(ch, "b", 0)),
            "word": str(word), "base": base, "track": track,
            "n_states": int(ch.n_states),
            "c_min": int(getattr(ch, "c_min", 0)),
            "nxt": ch.nxt.tolist()}


def main() -> None:
    claims = []

    # C1/C3: {1,2} and {1,5}, each digit
    for cid, ms in (("C1", (1, 2)), ("C3", (1, 5))):
        for d in range(3):
            chans = [Mult(m, d) for m in ms]
            ok = xzm(chans)
            assert ok, (cid, d)
            claims.append({"id": f"{cid}-digit{d}", "base": 3, "track": 1,
                           "verified": ok,
                           "channels": [dump(c, 3, 1) for c in chans]})

    # C2: product block {2,11}, all 9 assignments
    for d1 in range(3):
        for d2 in range(3):
            chans = [Mult(2, d1), Mult(11, d2)]
            ok = xzm(chans)
            assert ok, ("C2", d1, d2)
            claims.append({"id": f"C2-{d1}{d2}", "base": 3, "track": 1,
                           "verified": ok,
                           "channels": [dump(c, 3, 1) for c in chans]})

    # C4: base-3 four-channel
    c4 = [Channel3(0, 1, "0"), Channel3(0, 3, "2"),
          Channel3(3, 1, "0"), Channel3(1, 1, "2")]
    ok, live, per = exact_zero3(c4)
    assert ok
    claims.append({"id": "C4", "base": 3, "track": 2, "verified": ok,
                   "joint_live": live, "periods": per,
                   "channels": [dump(c, 3, 2) for c in c4]})

    # C5: escape from Cantor
    c5 = [Channel3(a, b, "1") for a, b in
          [(0, 1), (0, 2), (1, 4), (2, 0), (4, 0)]]
    ok, live, per = exact_zero3(c5)
    assert ok
    claims.append({"id": "C5", "base": 3, "track": 2, "verified": ok,
                   "joint_live": live, "periods": per,
                   "channels": [dump(c, 3, 2) for c in c5]})

    # C6: base-4 positioned-binary
    Ch4, bn4, _ = make_base(4)
    c6 = [Ch4(1, 0, 3), Ch4(1, 3, 1), Ch4(1, 4, 3),
          Ch4(2, -1, 2), Ch4(2, 0, 0), Ch4(2, 2, 0)]
    ok, live = xzg(bn4, c6)
    assert ok
    claims.append({"id": "C6", "base": 4, "track": 2, "verified": ok,
                   "joint_live": live,
                   "channels": [dump(c, 4, 2) for c in c6]})

    # C10: base-5 nine-channel family
    Ch5, bn5, _ = make_base(5)
    c10_spec = [(0, 1, 3), (0, 2, 4), (0, 3, 2), (0, 4, 0), (1, 1, 2),
                (1, 4, 3), (2, 2, 2), (3, 3, 2), (4, 4, 2)]
    c10 = [Ch5(a, b, d) for a, b, d in c10_spec]
    ok, live = xzg(bn5, c10)
    assert ok
    claims.append({"id": "C10", "base": 5, "track": 2, "verified": ok,
                   "joint_live": live,
                   "channels": [dump(c, 5, 2) for c in c10]})

    # C7: musical; C8: complemented flagship (base 2, two-track)
    for cid, fam in (
        ("C7", [(1, 0, "00"), (0, 1, "11"), (-1, 1, "100"),
                (2, -1, "11"), (-3, 2, "00"), (1, 1, "010")]),
        ("C8", [(1, 0, "11"), (0, 1, "110"), (1, 1, "00"),
                (1, 2, "110"), (2, 1, "101"), (1, 3, "111")]),
    ):
        chans = [GenChannel(*t) for t in fam]
        ok, live, per = xz2(chans)
        assert ok, cid
        claims.append({"id": cid, "base": 2, "track": 2, "verified": ok,
                       "joint_live": live, "periods": per,
                       "channels": [dump(c, 2, 2) for c in chans]})

    with open(OUT, "w") as f:
        json.dump({"emitted": "2026-08-29",
                   "note": "all claims re-verified at emission; see "
                           "EVIDENCE-2026-08-29-tower-formalization.md",
                   "claims": claims}, f, indent=1)
    n = sum(1 for c in claims)
    print(f"emitted {n} verified claim certificates -> {OUT}")


if __name__ == "__main__":
    sys.exit(main())
