# HANDOFF: π² BBP node fully proved (Formula 29), axiom-clean 🎯

Branch `wip/pisq-bbp-decomp`, tree clean, full build green (8833 jobs).
Overnight sorry-discharge run (operator-authorized 2026-08-30).

## Result

**`NormalNumbers.piSqBBP_proved : PiSqBBP` is FULLY PROVED and
axiom-clean.**  `PiSqBBP = HasSum piSqTerm (Real.pi^2)` — Bailey's
Compendium **Formula 29** (the π² base-16 BBP series, probe-verified to
88 digits).  `#print axioms piSqBBP_proved = [propext, Classical.choice,
Quot.sound]` — NO `sorryAx`.  This was the frozen lane-2 node named in
the operator brief; it is discharged.

All in `src/NormalNumbers/PiSqBBPProof.lean` (self-contained; header
docstring has the full map).

## How (mathlib has NO dilogarithm — built from scratch)

Degree-2 roots-of-unity filter (the `PiBBPProof.lean` trick, one level
up): `w2 n = (−16·xⁿ + 16·z₁ⁿ − 16·(−x)ⁿ + 16·z̄₁ⁿ)/n²`, the SAME four
points as `PiBBP` (the Formula-29 coefficient DFT is supported on
frequencies {0,1,4,7} with real integer weights; `experiments/pi_sq_bbp.py`).

The full dilogarithm theory, all kernel-checked:
- `Li2 z := ∑' zⁿ/n²`, `dilogSummable` (geometric domination).
- `hasDerivAt_Li2` (term-wise derivative via
  `hasDerivAt_tsum_of_isPreconnected` on a sub-ball) → `hasDerivAt_Li2'`
  (`Li₂' w = −log(1−w)/w`, closed form via `hasSum_taylorSeries_neg_log`).
- `dilog_add_neg` (`Li₂ z + Li₂(−z) = ½Li₂(z²)`) — even/odd series split.
- `dilog_reflection` (`Li₂ z + Li₂(1−z) = π²/6 − log z·log(1−z)`):
  `hasDerivAt_dilogRefl` (F′≡0) + `dilogF_const` (constancy on the lens
  `lensL = ball 0 1 ∩ ball 1 1`, which is convex and ⊆ slitPlane), with
  the constant pinned by `dilogF_value` (the `t→0⁺` boundary limit:
  `tendsto_Li2_zero`, `tendsto_Li2_one` via **Abel**
  `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` + `hasSum_zeta_two`,
  `tendsto_logprod` via `negMulLog` + `d/dt log(1−t)`).
- `dilog_special_values` (`−8·Li₂(½)+16·(Li₂ z₁+Li₂ z̄₁)=π²`) from
  reflection at `½` and `z₁`.
- `hasSum_w2` (analytic convergence) + `hasSum_fiber2` (fiber algebra,
  `linear_combination` over I²=−1, x²=½) → `piSqBBP_proved` via
  `Nat.divModEquiv 8` + `HasSum.prod_fiberwise` + `Complex.hasSum_ofReal`.

## Downstream now unconditional

`PiSqBBP.lean`'s headlines `piSq_boundary_of_zeroRun` /
`piSq_boundary_of_maxRun` were stated conditional on the frozen node
`PiSqBBP`; that hypothesis is now a proved theorem (`piSqBBP_proved`), so
they can be instantiated unconditionally.  (Not yet wired — optional
follow-up.)

## Next (per DIRECTION.md standing mandate / prior handoff)

The PiSqBBP objective is done.  Remaining open threads from
`HANDOFF-2026-08-30-tower-and-ledger-done.md`: ledger deepening (Philipp
1967 ψ-mixing, B–M strong hot spot — statement-only counts), and the
conjecture-graph frontier in `DIRECTION.md`.  The two `CFScheduleA.lean`
sorries and the two `Comparator/Challenge.lean` holes remain OFF-LIMITS
per the operator brief.

## Reusable artifact

The from-scratch dilogarithm (`Li2`, its derivative, duplication,
reflection, `Li₂(½)`/`Li₂((1+i)/2)` special values) is general and could
seed a mathlib contribution or be reused for other BBP-type constants
(e.g. any polylog-order-2 base-b formula).
