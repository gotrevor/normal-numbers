# Operator brief v2: lane-2 grind, second batch (Fable-low laps) 🏃

**Written 2026-08-29 by Ren at Trevor's direction ("Keep going! Pick some new goals to
formalize - same successful pattern").  Same authorization, rules, and ops mechanics as
`HANDOFF-2026-08-29-lane2-treadmill-brief.md`** (lane-2 clause fired; ADDITIVE ONLY;
evidence tiers; commit green via git-safe; no outward actions; phase-1 tolerances;
`decide +kernel` over `native_decide`; never touch `CFScheduleA.lean:4400`/`:5774`).
Batch 1 (`## RESULT` in that file) landed all 5 targets; this batch continues.
Already landed host-side before this brief: `lnTwoRun_le_unconditional`
(`LnTwoExpSepProof.lean`) — the hypothesis-free 26n run cap.

## Progress

- **Target 1 DONE** (cb3a0d2, 2026-08-29): `logTwoSqSeries_proved` lands in
  `LogTwoSqSeriesProof.lean`; frozen node `LogTwoSqSeries` discharged. Route as briefed
  (real log series at 1/2 + `hasSum_sum_range_mul_of_summable_norm` Cauchy square;
  partial fractions + `sum_range_reflect` for the coefficient identity). Sorry-free,
  `#print axioms` = trust triple. Next: target 2 (π² signed-kick probe first).

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
