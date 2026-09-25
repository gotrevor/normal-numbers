# HANDOFF c3-mrt 2026-09-25 lap88 — the crux is a THEOREM on the K-point input

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (lap 87; still in force, and this lap executed
its NEXT ⑤ and then went past it).  Branch `wip/c3-mrt`, HEAD `3f89631`, tree clean.
Tip module `NormalNumbers.C3MrtUnifK` (build it explicitly — `NormalNumbers.lean` does not import
the `C3Mrt*` chain).

    lake build                            # 9257 jobs, green
    lake build NormalNumbers.C3MrtUnifK   # 9005 jobs, green

## One-line state

`WeylLambertTwist b` (hence `ConjC3`) is now a **theorem** on ONE named open input with EXPLICIT,
DEGRADING constants plus its own threshold data — no schedule hypothesis, no budget layer, and
with both degenerate twist levels (`hh = 0`, `b ∣ hh`) discharged in kernel.

    weylLambertTwist_of_degrading : KPointNoExcWith (cKdeg c₀ m) (CstKdeg m) → KPointThresholdOK
                                    → WeylLambertTwist b
    weylLambertTwist_of_geom      : KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) (θ < 1/2)
                                    + KPointThresholdOKWith → WeylLambertTwist b

`cKdeg c₀ m K = c₀/(K+1)^m`, `CstKdeg m K = exp((K+1)^m)`, `cKgeom c₀ θ b K = c₀ b^{-θK}`.
All new declarations `[propext, Classical.choice, Quot.sound]`; the `C3Mrt*` chain still has zero
`axiom`s and zero `sorry`s.

## Commits this lap

`68e8b38` degrading profile ⇒ diagonal; `e4518d4` the minorant diverges; `2574ac0` **hgrow is a
theorem** (no schedule hypothesis); `8e20a4a` `hh = 0`; `6b293e8` `b ∣ hh` reduced;
`77f1b9f` `exists_pow_mul_not_dvd` + the divisible diagonal; `136c81d` **`DepthDiagonal` from the
degrading input**; `3f89631` the geometric profile, `θ < 1/2`.

## The chain, end to end

    KPointNoExcWith cK CstK K            -- named open input, constants EXPLICIT in K
      + ttNonPretentious_zOmegaNat       -- archimedean, unconditional (lap 83)
      → dyadic_window_bound_with → windowPhi → depthAvg_le_with
      → depthAvg_gen_tendsto_of_unif     -- ANY positive level sequence KN
      → rate_tendsto_of_exponent         -- the hypothesis is ONE scalar limit
      → exponent_tendsto_atBot_of_degrading  /  _of_geom_le
      → hgrow_of_schedule_le             -- DISCHARGED: k₀ N = u_N = log₂log₂N
      → depthDiagonal_of_degrading / _of_geom   -- all hh: 0, b∣hh (level - v), primitive
      → weylLambertTwist_of_depthDiagonal → WeylLambertTwist b → ConjC3

Key schedule facts (all new, all proved): `depthLL_succ_le_log` (`D_N+1 ≤ 2+3log(u_N+1)`),
`le_sq_cut` (`a_N = N/2^{u_N} ≥ √N`, via `(log₂N)³ ≤ 2^{log₂N} ≤ N`), `log_two_log_cut_ge`
(`log(2 log a_N) ≥ (u_N-2)log2`), `tendsto_cut_atTop`, `tendsto_depthLL`.

## Source reading (this lap)

`papers/tao-teravainen-2025-quantitative-correlations.txt:1569` — TT Thm 3.1 is a **two-point**
statement with a single absolute `c > 0`, an exceptional set `E ⊂ [√X, X]` of log density `≪ L^{-c}`,
and `W, b, h₁, h₂ = O(L^c)`.  There is no `K` in it: every `K`-dependence in `KPointNoExcWith` is
OUR generalisation's, which is why the honest profiles are the degrading ones.

## NEXT (in order)

1. **Slow the schedule to widen `θ`.**  `θ < 1/2` is an artefact of `b^{depthLL b N} ≍ (u_N+1)²`,
   and the mean-phase discard only needs `b^{D_N} ≫ LLbound N ≍ u_N` — ONE power, not two.  With
   `b^{D_N} ≍ u log u` (e.g. `depthSlow b N := log_b(u+1) + log_b(log_b(u+1)+2) + 2`) the saving
   is `u^{1-θ}(log u)^{-θ}`, so **`θ < 1` becomes admissible**.  Needs: `pow_depthSlow_gt/le`,
   `tendsto_LLbound_div_pow_depthSlow`, then re-run `exponent_tendsto_atBot_of_geom_le` against the
   new schedule (`log_two_log_cut_ge` and the cut lemmas are schedule-independent).
2. Narrow `KPointNoExcWith` itself: what does a `K`-fold Pilatte decoupling give?  `V^{-0.49J'}`
   in TT Thm 3.3 suggests the saving per point is a constant factor, i.e. exactly `cKgeom`.
3. `KPointThresholdOKWith` is currently assumed; TT's threshold is `X ≥ X₀` with `X₀` absolute at
   two points, so the `K`-point threshold's growth in `K` is the thing to pin down.

## Still refuted — DO NOT RETRY

Lap 80's list, plus: `exceptional_set_can_pin_a_scale`; bounded-ratio-density of good scales at the
`ConjC3` end (lap 87 F3); the whole `QuantDepthElliottGen` budget layer (lap 87 F1); fixed-`K`
`Tendsto` statements as a route to the diagonal (lap 87 F2).
