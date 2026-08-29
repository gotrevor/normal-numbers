#!/usr/bin/env -S uv run --quiet python3
"""Probe: the e kick-barrier mechanism (tower rung T4, decisive uncertain case).

Tower story (2026-08-29 second-story session): e's factorial-threshold kicks
arrive at positions n_k ~ log2(k!), every ~log2 k bits.  A digit run RIDING the
sliver past a kick must survive a profile shift of size ~dist(frac(log2 k!), Z)
(the crossing term's fractional part - how close k! sits to a power of 2).  If
that bookkeeping is right:

    run length at n  <~  (gap to next kick) + survivable-kick chain,
    surviving kick k at remaining depth d requires
        dist(frac(log2 k!), Z) < ~2^-d.

The COUNTING side is classical: {log2 k!} is equidistributed mod 1 (van der
Corput, f(x) = x log2 x class), and #{k <= K : dist < eps} <= K*eps + K*D_K
with effective discrepancy — so a *provable* seed exists if the mechanism
holds.  This probe tests the mechanism against e's actual 200k binary digits:

  1. population stats of dist(frac(log2 k!), Z) — equidistribution sanity;
  2. for every super-threshold run (the sliver events), which kicks fall
     inside the run span, and how clingy those kicks are vs the population;
  3. distance from each long-run END to the next kick position (if kicks are
     barriers, run ends should cluster just before/at kick positions).

Refutation reading: if kicks crossed by long runs look like uniform draws
(no clinginess) AND run ends show no kick alignment, the barrier mechanism is
dead and rung T4 falls.
"""

import sys
from math import lgamma, log, log2

B = 200_064
LOG2E = 1.4426950408889634


def frac_log2_fact(k: int) -> float:
    return (lgamma(k + 1) * LOG2E) % 1.0


def dist_to_int(x: float) -> float:
    f = x % 1.0
    return min(f, 1.0 - f)


def main() -> None:
    # --- binary digits of e (same construction as e_binary_runs.py) ----------
    s, t, k = 0, 1 << B, 0
    while t:
        s += t
        k += 1
        t //= k
    K_MAX = k
    bits = bin(s - (2 << B))[2:].zfill(B)[: B - 64]
    n_bits = len(bits)

    # kick positions: n_k = ceil(log2 k!) for k up to K_MAX
    kick_pos = []  # (position, k)
    acc = 0.0
    for kk in range(2, K_MAX + 1):
        acc += log2(kk)
        p = int(acc) + 1
        if p > n_bits:
            break
        kick_pos.append((p, kk))

    # --- 1. population stats --------------------------------------------------
    dists = sorted((dist_to_int(frac_log2_fact(kk)), kk) for _, kk in kick_pos)
    K = len(dists)
    mean_d = sum(d for d, _ in dists) / K
    small = sum(1 for d, _ in dists if d < 0.01)
    print(f"population: {K} kicks in first {n_bits} bits")
    print(f"  mean dist(frac(log2 k!), Z) = {mean_d:.4f}  (uniform predicts 0.25)")
    print(f"  #dist < 0.01: {small}  (uniform predicts {K * 0.02:.1f})")
    print(f"  clingiest kicks: " +
          ", ".join(f"k={kk} (2^{log2(d):.1f})" for d, kk in dists[:5]))

    # --- 2. super-threshold runs vs the kicks they cross ----------------------
    # M(n) via walking the same cumulative log2 factorial
    def M_of(n: int) -> int:
        lo, acc2, m = 0.0, 0.0, 0
        while True:
            m += 1
            acc2 += log2(m + 1)
            if acc2 > n:
                return m

    # cheap monotone M: precompute thresholds
    thresholds = []  # log2((m+1)!) ascending
    acc2, m = 0.0, 0
    while acc2 <= n_bits:
        m += 1
        acc2 += log2(m + 1)
        thresholds.append(acc2)

    def M_fast(n: int) -> int:
        import bisect
        return bisect.bisect_right(thresholds, n) + 1

    import bisect
    kick_positions_only = [p for p, _ in kick_pos]

    print("\nsuper-threshold runs and the kicks inside their span:")
    print(f"{'pos':>8} {'len':>4} {'thr':>5}  kicks crossed (k, dist as 2^x)"
          f"      pop-median 2^-2")
    i = 0
    events = []
    while i < n_bits:
        c = bits[i]
        j = i
        while j < n_bits and bits[j] == c:
            j += 1
        run_len, pos = j - i, i + 1
        if pos > 4:
            thr = log2(M_fast(pos) + 1) + 1
            if run_len > thr:
                lo_idx = bisect.bisect_left(kick_positions_only, pos)
                hi_idx = bisect.bisect_right(kick_positions_only, pos + run_len - 1)
                crossed = kick_pos[lo_idx:hi_idx]
                desc = ", ".join(
                    f"(k={kk}, 2^{log2(max(dist_to_int(frac_log2_fact(kk)), 1e-300)):.1f})"
                    for _, kk in crossed) or "none"
                events.append((pos, run_len, thr, crossed))
                print(f"{pos:>8} {run_len:>4} {thr:>5.1f}  {desc}")
        i = j

    # --- 3. run ends vs next kick ---------------------------------------------
    print("\ndistance from each super-threshold run END to the NEXT kick:")
    gaps = []
    for pos, run_len, thr, crossed in events:
        end = pos + run_len - 1
        idx = bisect.bisect_right(kick_positions_only, end)
        if idx < len(kick_positions_only):
            nxt = kick_positions_only[idx]
            typical = log2(M_fast(end)) if end > 2 else 1.0
            gaps.append((nxt - end) / typical)
            print(f"  run@{pos:>7} ends {end:>7}: next kick at {nxt:>7} "
                  f"(gap {nxt - end}, typical spacing ~{typical:.0f})")
    if gaps:
        print(f"  normalized end-to-kick gap: mean {sum(gaps)/len(gaps):.2f} "
              f"(uniform-in-gap predicts ~0.5)")
    print("\nreading: barrier mechanism predicts crossed kicks clingier than")
    print("2^-2 median AND/OR run ends hugging kicks (normalized gap << 0.5).")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
