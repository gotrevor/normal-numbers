#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: Product-Block hunt for F = {00, 11} (Babel story 1b).

Target (from docs/transversal-ceiling-2026-08-29.md): a channel set M such
that EVERY word assignment f in {00,11}^M collapses exactly (h = 0, integer
graph).  By the transversal characterization, such a product block yields the
universal theorem:

    for ANY reals X, Y not both rational, some channel a*X + b*Y with
    (a,b) in M contains BOTH 00 AND 11 infinitely often in binary -

the first rung of the graded joint-visit ladder (strictly above every
existing factory clause; not forbidden by any known blocking pair).

Blocking-pair pre-filter (proved in the ceiling doc, tested here): on the
independent-blocks sparse pair, channel (a,b) realizes exactly the factors of
0*bin(a)0* and 0*bin(b)0*.  Word 00 is always realized, so ONLY the all-11
assignment is exposed - and it provably cannot collapse when every
coefficient is Fibbinary (no 11 in any bin(a), bin(b)).  The engine must
agree (two instruments, independent origins); a channel set can only carry a
product block if some coefficient contains 11 in binary.

COMPLEMENT INVOLUTION (operator observation, 2026-08-29 dialogue: "-1
complements digits"): (x, y, c) -> (1-x, 1-y, a+b-1-c) is an exact involution
of each adder channel that complements the output digit: with v = ax+by+c,
one checks z-bar = 1-z and c-bar' = a+b-1-c'.  Hence tuple f collapses iff
the complemented tuple ~f collapses, mechanically - so 00 and 11 are exactly
symmetric in the machine, the greedy need only screen canonical
representatives (f <= ~f), and the complement of the FLAGSHIP family is
predicted to be a new exact collapse (tested below; a falsifiable
consequence of the involution).

Self-tests: base-family regression (exact h=0); COMPLEMENTED base family
exact h=0 (the involution's prediction); single avoid-00 channel
h = 1 + log2(phi); Fibbinary all-11 prediction (engine must report h > 0).
"""

import sys
import time
from itertools import product as iproduct
from math import log2
import numpy as np
from adder_collapse_hunt import build_nxts, joint_entropy
from adder_family_enum import GenChannel, exact_zero

F = ["00", "11"]
STATE_CAP = 8_000_000
SCREEN_ITERS = 40


def has11(n: int) -> bool:
    return "11" in format(n, "b")


def entropy_screen(channels, iters=SCREEN_ITERS) -> float:
    """Cheap power-iteration entropy for greedy screening only (final claims
    always go through joint_entropy + exact_zero)."""
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


def comp(f) -> tuple:
    return tuple("11" if w == "00" else "00" for w in f)


def block_profile(abset, screen=True, stop_above=None):
    """Max entropy over {00,11}-assignments of the channel set, screening only
    canonical representatives f <= ~f (the complement involution proves
    h(f) = h(~f) exactly), uniform assignment first.  Returns (max_h,
    worst_f, n_near_zero canonical).  stop_above: greedy early-exit."""
    k = len(abset)
    assigns = [tuple(["00"] * k)]
    assigns += [f for f in iproduct(F, repeat=k)
                if f <= comp(f) and f not in assigns]
    hmax, worst, near0 = float("-inf"), None, 0
    fn = entropy_screen if screen else joint_entropy
    for f in assigns:
        chans = [GenChannel(a, b, w) for (a, b), w in zip(abset, f)]
        h = fn(chans)
        if np.isnan(h):
            return float("nan"), f, near0
        if h <= 1e-3:
            near0 += 1
        if h > hmax:
            hmax, worst = h, f
        if stop_above is not None and hmax > stop_above:
            return hmax, worst, near0
    return hmax, worst, near0


def verify_block(abset) -> bool:
    """EXACT verification of a candidate product block: every assignment must
    pass the integer-graph zero-entropy check."""
    for f in iproduct(F, repeat=len(abset)):
        chans = [GenChannel(a, b, w) for (a, b), w in zip(abset, f)]
        ok, live, periods = exact_zero(chans)
        if not ok:
            print(f"    exact check FAILED on assignment {f}")
            return False
    return True


def main() -> None:
    # --- self-tests -------------------------------------------------------
    base = [(1, 0, "00"), (0, 1, "001"), (1, 1, "11"),
            (1, 2, "001"), (2, 1, "010"), (1, 3, "000")]
    ok, live, _ = exact_zero([GenChannel(*t) for t in base])
    assert ok, "regression: base family lost its exact collapse"
    # involution prediction: the COMPLEMENTED flagship must also collapse
    cbase = [(a, b, w.translate(str.maketrans("01", "10")))
             for a, b, w in base]
    okc, livec, periodsc = exact_zero([GenChannel(*t) for t in cbase])
    assert okc, "involution FALSIFIED: complemented base family not h=0"
    print(f"involution confirmed: complemented flagship exact-collapses "
          f"({livec} live states, periods {periodsc}) - a new distance-6 "
          f"theorem for free: at least one of 11 in ln2, 110 in ln3, 00 in "
          f"ln6, 110 in ln18, 101 in ln12, 111 in ln54")
    h = joint_entropy([GenChannel(1, 0, "00")])
    assert abs(h - (1 + log2((1 + 5 ** 0.5) / 2))) < 1e-3, h
    # blocking-pair cross-check: all-11 on an all-Fibbinary coefficient set
    # is PREDICTED non-collapsing (independent-blocks sparse pair survives).
    fib_set = [(1, 0), (0, 1), (1, 1), (2, 2), (1, 2), (2, 1)]
    assert all(not has11(a) and not has11(b) for a, b in fib_set)
    h11 = joint_entropy([GenChannel(a, b, "11") for a, b in fib_set])
    assert h11 > 1e-2, f"engine contradicts blocking pair: h={h11}"
    print(f"self-tests OK (regression, golden-mean, Fibbinary all-11 "
          f"h={h11:.4f} > 0 as the blocking pair demands)\n")

    # --- part 1: the base six-channel ab-set as a candidate block ---------
    base_ab = [(a, b) for a, b, _ in base]
    t0 = time.time()
    hmax, worst, near0 = block_profile(base_ab, screen=False)
    print(f"base ab-set {base_ab}:")
    print(f"  {near0}/32 canonical assignments near zero (x2 by involution); "
          f"max h = {hmax:.4f} at {worst}  [{time.time()-t0:.0f}s]\n")

    # --- part 2: greedy block growth --------------------------------------
    # pool: 0 <= a,b <= 3, (a,b) != (0,0); pre-filter demands SOME coefficient
    # with 11 in binary before a block is even possible.
    pool = [(a, b) for a in range(4) for b in range(4) if (a, b) != (0, 0)]
    print("greedy block growth (score = max h over ALL {00,11}-assignments):")
    chosen: list = []
    while True:
        best = None
        for cand in pool:
            if cand in chosen:
                continue
            trial = chosen + [cand]
            stop = best[0] if best else None
            hmax, worst, _ = block_profile(trial, screen=True, stop_above=stop)
            if np.isnan(hmax):
                continue
            if best is None or hmax < best[0]:
                best = (hmax, cand, worst)
        if best is None:
            print("  state cap exhausted; stopping")
            break
        hmax, cand, worst = best
        chosen.append(cand)
        print(f"  +{cand}: max-assignment h = {hmax:.4f}  (worst = "
              f"{''.join(w[0] for w in worst)} as 0=00/1=11)  "
              f"[k={len(chosen)}]")
        if hmax <= 1e-3:
            print("\n  float block reached - exact-verifying all "
                  f"{2 ** len(chosen)} assignments...")
            if verify_block(chosen):
                print(f"\n*** PRODUCT BLOCK FOUND: {chosen} ***")
                print("*** CANDIDATE THEOREM (pending independent reimpl + "
                      "novelty sweep): for any reals X, Y not both rational, "
                      "some channel a*X+b*Y on this set contains BOTH 00 AND "
                      "11 infinitely often in binary. ***")
            else:
                print("  float zero was numerical; not a block")
            break
        if len(chosen) >= 8:
            print(f"\n  no block through k=8; FLOOR = {hmax:.4f} - the "
                  "entropy budget of joint 00/11 pathology on this pool "
                  "(a finding in the W3 currency).")
            break
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
