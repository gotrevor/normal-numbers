# Operator brief v2: lane-2 grind, second batch (Fable-low laps) 🏃

**Written 2026-08-29 by Ren at Trevor's direction ("Keep going! Pick some new goals to
formalize - same successful pattern").  Same authorization, rules, and ops mechanics as
`HANDOFF-2026-08-29-lane2-treadmill-brief.md`** (lane-2 clause fired; ADDITIVE ONLY;
evidence tiers; commit green via git-safe; no outward actions; phase-1 tolerances;
`decide +kernel` over `native_decide`; never touch `CFScheduleA.lean:4400`/`:5774`).
Batch 1 (`## RESULT` in that file) landed all 5 targets; this batch continues.
Already landed host-side before this brief: `lnTwoRun_le_unconditional`
(`LnTwoExpSepProof.lean`) — the hypothesis-free 26n run cap.

## RESULT (2026-08-29, batch complete — all 3 targets landed) ✅

All three targets discharged in ~40 min of Fable/low laps (one scoped run each), every
headline re-verified HOST-side by `#print axioms` — trust triple, 2026-08-29.
(1) **`LogTwoSqSeries` discharged**: `logTwoSqSeries_proved` (`LogTwoSqSeriesProof.lean`)
via the real log series at 1/2 + summable-norm Cauchy square + partial fractions; both
log²2 sliver headlines unconditional at call sites.  (2) **Signed-kick machine + π²**
(`PiSqBBP.lean`): frozen CITED node `PiSqBBP` (compendium Formula 29, probe green to 88
digits, `experiments/pi_sq_bbp.py`), two-sided tail cap `kicked_tail_abs_le`, boundary
cores, and both headlines `piSq_boundary_of_zeroRun`/`_maxRun` — a long hex run of π²
pins the surrogate within `16⁻ᵏ + 52/(8n+1)²` of the wrap point (the lap correctly
caught that the draft surrogate missed the `j = 0` block and restated via the shifted
kick).  (3) **Tier-1 sharpened to β = 9**: `lnTwoExpSep_sharp` (`LnTwoExpSepSharp.lean`)
via `Σ|c_k| ≤ 6^ℓ`, kernel-max remainder cap `429/2500`, exact-root interval lower bound
`(1/50)(6/35)^ℓ`, ratio `ℓ/n = 15/8`; docstring records why β = 8 is unreachable by this
method (Chebyshev `4^ℓ` lcm; PNT-strength would give ≈ 5).  Host-side wiring landed both
unconditional run caps: `lnTwoRun_le_unconditional` (26n, pre-batch) and
`lnTwoRun_le_unconditional_sharp` (9n).  Lane-2 discharge still owed: `PiSqBBP` (→ batch 3).

## Progress

- **Target 1 DONE** (cb3a0d2, 2026-08-29): `logTwoSqSeries_proved` lands in
  `LogTwoSqSeriesProof.lean`; frozen node `LogTwoSqSeries` discharged. Route as briefed
  (real log series at 1/2 + `hasSum_sum_range_mul_of_summable_norm` Cauchy square;
  partial fractions + `sum_range_reflect` for the coefficient identity). Sorry-free,
  `#print axioms` = trust triple. Next: target 2 (π² signed-kick probe first).
- **Target 2 DONE** (2026-08-29): `PiSqBBP.lean` complete, sorry-free. Signed
  abstract layer (`kicked_tail_abs_le` two-sided cap → `|bⁿ(x−sₙ)| ≤ A/(b−1)`;
  boundary cores `boundary_of_fract_lt/_ge`; packaged
  `boundary_of_zeroRun_kickedAbs` / `boundary_of_maxRun_kickedAbs`). π²
  instance via SHIFTED kick `piSqShiftKick m = 16·piSqKick (m−1)` (folds the
  j=0 block in, so the kicked series is exactly π²; the draft's
  `kickedPartial 16 piSqKick` surrogate missed the j=0 term and was restated).
  `|piSqKick j| ≤ 48/(8j+1)²` for j ≥ 1. Headlines
  `piSq_boundary_of_zeroRun` + `_maxRun` twin: window `16⁻ᵏ + 52/(8n+1)²`
  (machine: A = 768/(8n+1)², sliver A/15), conditional on frozen `PiSqBBP`.
  `#print axioms` both = trust triple. Node discharge stays lane-2 owed.
  Gotcha: linarith does NOT relate `16/X` and `48/X` as multiples of one atom —
  state comparisons as `c·(1/X)` first. Next: target 3 (β = 26 sharpening).
- **Target 3 DONE** (2026-08-29): `lnTwoExpSep_sharp : ∃ N₀, LnTwoExpSep 9 N₀`
  proved sorry-free in `LnTwoExpSepSharp.lean`, `#print axioms` = trust triple.
  β = 26 → **9** (single digit; the draft's β = 8 is provably out of reach
  while lcm ≤ 4^ℓ — full accounting in the module docstring). Three
  sharpenings: height `Σ|c_k| ≤ 6^ℓ` (binomial, no `(ℓ+1)` factor), kernel
  cap `429/2500` (disc −959 < 0, ~0.2% off the true max `3−2√2` — THE
  unlock: ratio constraint drops from `c > 3.11` to `c > 1.842`), lower
  bound `(1/50)(6/35)^ℓ` on `[2/5, 3/7]` (quadratic roots exactly at the
  endpoints; the `6^ℓ` height CANCELS against `(6/35)^ℓ`, zero-case base
  exactly 35). Index `ℓ = 15n/8 + 1`; eventual inequalities via 8th powers
  + master `r^n·e^{16√(2n)log(2n)} → 0`; certificates `2⁸·429¹⁵ < 625¹⁵`,
  `24¹⁵ < 2⁷²`, `35¹⁵ < 2⁸⁰`. PNT-strength lcm would give β ≈ 5 (future).
  Landed `lnTwoExpSep_holds` untouched.

## Targets, ranked (work top-down; each is self-contained)

1. **Discharge `LogTwoSqSeries`** (`LogTwoSqKicked.lean:59`, the frozen CITED node) —
   prove `logTwoSqSeries_proved : LogTwoSqSeries` in a new `LogTwoSqSeriesProof.lean`,
   mirroring the PiBBP discharge.  Route: `log²2 = (Σ_{k≥1} xᵏ/k)²` at `x = 1/2`; the
   Cauchy product of the log series with itself has coefficient
   `Σ_{i+j=m, i,j≥1} 1/(i·j) = 2·H_{m−1}/m` — mathlib's `Complex.hasSum_taylorSeries_neg_log`
   (real version or `hasSum_ofReal`) + `HasSum.mul` / summable-norm Cauchy-product API.
   Payoff: both log²2 sliver headlines become unconditional at call sites.
2. **Signed-kick machine + π² instance** — the compendium (Bailey, *A Compendium of
   BBP-Type Formulas*, 2023-04-08, Formula 29) gives
   `π² = Σ_k 16⁻ᵏ (16/(8k+1)² − 16/(8k+2)² − 8/(8k+3)² − 16/(8k+4)² − 4/(8k+5)²
   − 4/(8k+6)² + 2/(8k+7)²)`.  ⚠️ The per-digit block sum is asymptotically
   `−30/(64k²) < 0` (coefficient sum −30), so the nonneg-kick machine does NOT apply:
   the honest move is a SIGNED variant in `KickedOrbit.lean`-style (new module,
   `|r m| ≤ A` two-sided tail bracket `|bⁿ(x − sₙ)| ≤ A/(b−1)`), whose run theorem is
   mismatch/boundary-shaped (a long run pins the surrogate near the wrap point from
   either side), NOT top-sliver-shaped.  PROBE FIRST (`experiments/pi_sq_bbp.py`):
   verify Formula 29 numerically to high precision AND the block-sign claim; freeze the
   node `PiSqBBP` only after the probe passes.  All statements DRAFT-restatable.
3. **Sharpen Tier-1: β = 26 → single digits** (`LnTwoExpSepProof.lean`) — new theorem
   (e.g. `lnTwoExpSep_sharp`), do NOT weaken/edit `lnTwoExpSep_holds` or its corollary.
   The two lossy spots recorded in that file's docstring: coefficient height (crude
   `8^ℓ` per coeff → sharp `Σ|c_k| = P_ℓ(3) ~ (3+2√2)^ℓ ≈ 5.83^ℓ`, Legendre value at 3)
   and the zero-case remainder lower bound (crude `(1/6)(1/12)^ℓ` on `[1/4,1/2]` →
   sharper interval/kernel estimates).  Rebalance `ℓ = c·n` optimally.  Any explicit
   `β < 26` is progress; record the honest accounting.  Multi-lap; a per-lap
   decomposition into named height/remainder lemmas is expected.

## Stop condition

Targets exhausted or operator returns → final commit, `## RESULT` paragraph at the top
of THIS file, self-stop.  Blocked → `knowledge/outbox/`, move to next target.
