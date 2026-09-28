# HANDOFF c3-mrt 2026-09-25 lap71 — THE D=2 CRUX IS CLOSED

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (OUTRANKS this file).
Detail: `PENDING_WORK.md` → laps 61–71.  Branch `wip/c3-mrt`, HEAD `13a42d2`, tree clean.

## BUILD HYGIENE

    lake build                                  # 9257 jobs (root)
    lake build NormalNumbers.C3MrtMultChase     # the log layer, new anchor
    lake build NormalNumbers.C3MrtNoExc         # 8992 jobs — the new tip, SORRY-FREE

`C3MrtMultElliott → C3MrtMultRung → C3MrtMultChase → C3MrtTTThm31 → C3MrtExcScales →
C3MrtNoExc`.  None of these is in the `ProgChase` chain; build the tip explicitly.

## What this session did (laps 61–71)

**61.** `progression_log_rung_class_mult` — the merely-multiplicative anchor reaches lap 59's
conclusion, with no powerful-divisor bridge, no truncation, no `K^{K²}`.  The one "brick"
lap 60 named needed no new mathematics; old brick 4b was never an obligation.

**62.** `TwoPointNaturalCorrelation` — TT arXiv 2512.01739 Thm 3.1(ii) stated faithfully
(exceptional set as a real integral bound), plus `c3_two_point_natural_of_TT` wiring it to the
C3 summand.

**63–64.** The exceptional set is a genuine obstruction, machine-checked from both sides:
`exceptional_scales_not_tendsto` (a density-zero scale set with arbitrarily long runs carrying
a non-vanishing sequence) and `exceptional_set_can_pin_a_scale` (a singleton is a legal
exceptional set at every `X`).  The Fubini rescue is refuted in `PENDING_WORK.md`.

**65–70.** The assembly, with one design correction that mattered: the *bottom-up* dyadic stack
is wrong (TT bounds only FULL windows `(N,2N]`, so the top window would need a trivial `≍ Y`
bound).  The fix is the **top-down halving stack** `N_k = Y/2^k`, where each level is a full
window up to one point.  Proved along the way: `tendsto_geom_weighted_avg`,
`dyadic_sum_geometric`, `class_sum_split`, `sum_Ioc_halving_stack`, `norm_sum_level_le`,
`dyadic_window_bound_of_noExc`, `top_down_weighted_tendsto`, `class_sum_tendsto_of_noExc`.

**71.** **`logToNatural_two_of_noExc`** — `[propext, Classical.choice, Quot.sound]`.  The
`K = 2` natural-density transfer, from TT Thm 3.1(ii) with the exceptional set removed.

## The deliverable

The `D = 2` layer of the C3/MRT route is **equivalent to a named open problem** — removing the
exceptional set of scales from TT Theorem 3.1 — and both directions are machine-checked.  TT
state in print (`papers/…-quantitative-correlations.txt:2997`) that this is out of reach of
current technology.  Trigger **C3-T2 is satisfied**: the `D = 2` natural-density rung is a
theorem on the new anchor, within 6 laps of the escalation.

## NEXT — resume here

1. **`TTNonPretentious (zOmegaNat z) X L`** for `‖z‖ = 1`, `z ≠ 1`.  This is the last
   hypothesis of `logToNatural_two_of_noExc` not yet discharged from the repo's own inputs.
   Laps 18–21 built the archimedean certificate in `Erdos67b.pretentiousDistSqToTwist`;
   `pretentiousDistSqToTwist_zOmegaInt_eq` (lap 60) transfers it to `ζ^ω` for free.  The work
   is matching that metric to TT's `M(g; X², log^{1/125} X)` (`ttPretentiousSum`): both are
   sums over primes of `(1 − Re(g(p)·twist))/p`, so the bridge should be a change of
   normalisation plus the range `X → X²` — bounded work, not a new estimate.
2. `LogToNaturalCorrelationNZ 2` (the `z 0 ≠ 1` variant of `LogToNaturalCorrelation`) and the
   one-line rewiring of `depthAvg_tendsto_of_transfer` (which already has `hζ` in hand), so
   lap 71's theorem plugs into the existing chain instead of sitting beside it.
3. Only then: the generational `K ≥ 3` item.

## Still refuted — DO NOT RETRY

Everything in the `-session-wrap-*` files, plus: finding R3 (lap 60); deriving
`LogToNaturalCorrelation 2` from `TwoPointNaturalCorrelation` *with* its exceptional set (three
independent arguments, laps 62–64); the Fubini rescue (lap 63); the bottom-up dyadic stack
(lap 68).

## Confidence

* leaf TRUE ≈ 97 % (unchanged).
* leaf PROVABLE with known techniques ≈ 8 % (unchanged — the barrier is now *named*, not
  reduced).
* **ledger QUALITY** — the ratified deliverable — is at its high point: the `D = 2` layer is a
  machine-checked equivalence with a published open problem, and the remaining `K ≥ 3` item is
  quoted from the source.
