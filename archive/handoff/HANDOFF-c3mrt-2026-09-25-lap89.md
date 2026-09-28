# HANDOFF c3-mrt 2026-09-25 lap89 — the route boundary moves from θ<1/2 to θ<1

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (lap 87; still in force).  This lap executed
HANDOFF lap88 NEXT ① in full.  Branch `wip/c3-mrt`, tree clean.
Tip module `NormalNumbers.C3MrtSlowSched` (new; build explicitly — `NormalNumbers.lean` does not
import the `C3Mrt*` chain).

    lake build                              # 9257 jobs, green
    lake build NormalNumbers.C3MrtSlowSched # green

## One-line state

`ConjC3` is a **theorem** on a geometrically-degrading `K`-point input whose saving may decay as
fast as `c₀ b^{-θK}` for **any `θ < 1`** — twice the decay lap88 could tolerate:

    conjC3_of_geom_slow : (∀ b ≥ 3, ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K)
                          → (threshold data) → (0 < θ) → (θ < 1) → ConjC3

## What moved, and why it is the crux advance

The `θ < 1/2` of `weylLambertTwist_of_geom` was **never** a fact about the correlation input; it
was the price of the depth schedule.  `PairDecouple.depthLL` is built so `b^{D_N} > (u_N+1)²`
(`u_N = log₂log₂N`), i.e. TWO powers of `u_N`, but the only consumer of that size — the mean-phase
discard in `weylLambertTwist_of_schedule` — needs just `LLbound N / b^{D_N} → 0`, and
`LLbound N ≍ 15 u_N` is ONE power.  The second power was pure slack, and the geometric saving was
paying for it: `b^{-θD_N} ≍ u^{-2θ}` against boundary terms costing `u^{-1}`.

So the schedule was slowed to the minimum that still works:

    slowW b N  = log_b(u_N+1) + 2
    slowArg b N = (u_N+1) · slowW b N
    depthSlow b N = log_b(slowArg b N) + 1          ⇒  b^{D_N} ∈ ((u+1)W, b(u+1)W]

* discard: `LLbound/b^{D_N} ≤ 15/W → 0` (`tendsto_LLbound_div_pow_depthSlow`) — one power cancels,
  the surviving `W → ∞` does the work.
* saving: `b^{-θD_N}·log(2 log a_N) ≳ u^{1-θ}(log u)^{-θ}`, which still beats
  `log CstKdeg = (D_N+1)^m = O(log u)^m` for every `θ < 1`
  (`exponent_tendsto_atBot_of_geom_slow`).

**This is why it matters for the open input.**  TT Thm 3.3's `V^{-0.49J'}` is a *constant factor*
of saving lost per correlation point — i.e. exactly `cKgeom` shape, with `θ` set by the constant,
not by anything small.  `θ < 1/2` demanded the per-point loss beat `b^{-1/2}`; `θ < 1` only
demands it beat `b^{-1}`, which is one full base-digit of room.  The diagonal now rests on
strictly less (C3-T5 satisfied).

## New file `src/NormalNumbers/C3MrtSlowSched.lean` (pure addition, 19 declarations)

Schedule layer: `slowW`, `slowArg`, `depthSlow`, `pow_depthSlow_gt`, `pow_depthSlow_le`,
`depthSlow_le_depthLL` (eventually — so every `KN N ≤ depthLL b N` side condition in
`C3MrtUnifK` is inherited free), `eventually_depthSlow_add_le`, `tendsto_slowW`,
`tendsto_depthSlow`, `tendsto_LLbound_div_pow_depthSlow`, `slowW_le_log`, `pow_depthSlow_le_log`.

Analytic layer: `tendsto_polyPow_sub_expDiv` (`(2+3t)^p - c₁(e^{αt}-3)/(2+2t) → -∞`; the linear
divisor the log factor introduces is swallowed by halving the rate, since eventually
`e^{αt/2} ≥ 5+2t`), `exponent_tendsto_atBot_of_geom_slow`.

Assembly: `depthAvg_dvd_tendsto_of_primitive_sched` (schedule-generic form of
`C3MrtUnifK.depthAvg_dvd_tendsto_of_primitive` — its proof only ever used `Dsch → ∞`),
`depthAvg_gen_tendsto_of_geom_slow`, `DepthDiagonalSlow`,
`weylLambertTwist_of_depthDiagonalSlow`, `depthDiagonalSlow_of_geom`,
`weylLambertTwist_of_geom_slow`, `conjC3_of_geom_slow`.

Supporting `Nat.log` facts: `add_two_le_two_pow`, `natLog_add_two_le`, `natLog_mul_log_two_le`.

All 19 `[propext, Classical.choice, Quot.sound]`.  The `C3Mrt*` chain still has zero `axiom`s and
zero `sorry`s.  Nothing in `C3MrtUnifK` or earlier was weakened, renamed or deleted.

## Is θ<1 the new hard boundary?

Yes, for THIS route, and the reason is structural rather than slack: the discard needs
`b^{D_N} ≫ u_N` (strictly), the saving is `b^{-θD_N}·log log a_N ≍ b^{-θD_N} u_N`, so the product
is `≍ u_N^{1-θ}` up to logs.  At `θ = 1` the two cancel exactly and no choice of schedule
separates them.  **Widening past `θ = 1` therefore requires a different lever than the schedule** —
either a cheaper mean-phase discard (`LLbound` sublinear in `u_N`) or a saving that is not a pure
power of `b^{-D_N}`.  Record this as the route's real endpoint.

## NEXT (in order)

1. **`KPointThresholdOKWith` is the last assumed piece.**  Pin its `K`-growth: TT's threshold is
   `X ≥ X₀` with `X₀` absolute at two points, so the question is how `X₀(K)` grows under the
   `K`-fold decoupling.  With `cKgeom`, `hAthr` demands
   `(2 log Athr K)^{κc₀b^{-θK}} ≥ max(K+1, Q·primorial P)`, i.e.
   `log log Athr K ≳ b^{θK} log K` — a TOWER in `K`.  Check against `hAcut`
   (`Athr K ≤ N/2^{u_N}` for `K ≤ D_N ≍ log_b(u log u)`): `log log Athr(D_N) ≳ b^{θD_N} ≍ u^θ`,
   against `log log a_N ≍ log u`.  **This looks like it FAILS for θ>0**, which would mean the
   threshold, not the saving rate, is the binding constraint — verify or refute in Lean, it is
   cheap and route-decisive.  If it fails, the honest profile must have `cK K` decaying
   *sub*-geometrically (e.g. `cKdeg`, already handled by `weylLambertTwist_of_degrading`), and
   `weylLambertTwist_of_geom*` is decorative.  Do this FIRST.
2. Only if ① survives: narrow `KPointNoExcWith` itself via a `K`-fold Pilatte decoupling.

## Still refuted — DO NOT RETRY

Lap 80's list, plus: `exceptional_set_can_pin_a_scale`; bounded-ratio-density of good scales at the
`ConjC3` end (lap 87 F3); the whole `QuantDepthElliottGen` budget layer (lap 87 F1); fixed-`K`
`Tendsto` statements as a route to the diagonal (lap 87 F2); and now — widening `θ` past 1 by
choosing a different depth schedule (lap 89: the discard and the saving cancel exactly at θ=1).
