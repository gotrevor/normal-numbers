# HANDOFF c3-mrt 2026-09-25 lap80 — the crux is a formalization, not an axiom

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (OUTRANKS this file).
Detail: `PENDING_WORK.md` → laps 72–80.  Branch `wip/c3-mrt`, HEAD `85ba856`, tree clean.

## BUILD HYGIENE

    lake build                                   # 9257 jobs (root)
    lake build NormalNumbers.C3MrtNoExc          # lap-71 tip
    lake build NormalNumbers.C3MrtTTPretentious  # the certificate
    lake build NormalNumbers.C3MrtWindowMass     # THE NEW TIP — the crux's leaves

Chain: `… → C3MrtNoExc → C3MrtTTPretentious → C3MrtWindowMass`.  Build the tip explicitly.
`C3MrtWindowMass` imports `PrimeNumberTheoremAnd.BrunTitchmarsh` — a transitive package
already in `.lake/packages`, sorry-free, axiom-clean.  This is legal from a `C3Mrt*` file
(none of them is in the `NormalNumbers` root).

## What this session did (laps 72–80)

**72.** The lap-71 NEXT item (1) as stated is **FALSE**: `exp(ttPretentiousSum (z^ω) X 0)
≍ (log X)^{1−cos(arg z)}`, so TT's (3.3) cannot hold for `L` up to `log X` when `arg z` is
small.  Correct range: `L ≤ (log X)^{κ(z)}`.  Built `C3MrtTTPretentious.lean`
(`ttPretentiousSum_eq_primes`, `ttPretentiousSum_ge`, `ttNonPretentious_of_uniformResonantMass`)
and rewired `C3MrtNoExc`'s three assembly theorems to `0 < κ ≤ 1`, `L ≤ (log X)^κ`.

**72b.** `LogToNaturalCorrelationNZ` (the `z 0 ≠ 1` variant — the unrestricted form is false),
`depthAvg_tendsto_of_classSums`, `depthAvg_tendsto_of_transfer_nz`.
`depthAvg_tendsto_of_transfer` keeps its exact statement and is now a corollary.
**`depthAvg_two_tendsto_of_named`**: the `D = 2` natural-density depth rung from exactly
`TwoPointNaturalCorrelationNoExc` + `UniformResonantMass` + `ProgressionLogRung 2`.

**73, 75.** Two constant corrections found by pushing the arithmetic, not by taste: the
covering loses a factor 2 (fatal at `z = −1`), and Brun–Titchmarsh loses ~10 more.  The window
half-width is now a free parameter and `UniformResonantMass` carries `100·δ`, with
`ttEps z := min (resEps z) (1/256)` keeping `κ = ttExponent z ≥ 0.6(1 − cos δ) > 0`.

**74.** **The unlock.**  `PrimeNumberTheoremAnd.BrunTitchmarsh.primesBetween_le` is present and
axiom-clean.  It is the one shape the dependency's Mertens cannot give — error proportional to
the window WIDTH, not a flat additive constant.  `UniformResonantMass` became a formalization
target.  `short_interval_mass_le` landed.

**75–80.  Every leaf of `UniformResonantMass` is now proved and axiom-clean:**
`short_interval_mass_le`, `interval_mass_le` (the block brick), `window_err_le`,
`exp_sub_one_le_two_mul`, `sum_inv_gap_le`, `sum_exp_neg_le`, `sum_Icc_symm_le`,
`small_prime_mass_le`, `log_le_mul_sub`/`log_log_le_mul_log`, plus the `δ`-covering
(`exists_window_of_resonant_width`, `windowIndexW`, `windowIndexW_spec`, `abs_windowIndexW_le`).

**80.  Architecture change (supersedes the lap-74 plan).**  Cut every resonance window into
UNIT pieces in `log p`.  Per-window is wrong in both directions: wide windows (`|t| < 2δ`) make
BT exponentially lossy while Mertens' flat per-window error costs `O(δ log Y)`; narrow windows
at large `|t|` make the BT error cost `O(|t|)`.  Unit pieces are always narrow, and their BT
errors sit `≥ 1` apart in height, so they sum geometrically with no `|t|`.

## NEXT — resume here

**The assembly of `UniformResonantMass`**, the only thing between the repo and an
unconditional `TTNonPretentious` for `z^ω`.  All leaves exist; this is bookkeeping, ~300 lines:

1. Fibre the resonant primes with `log p ≥ A₁` by (window index `m`, block index `k = ⌊log p⌋`)
   — `Finset.sum_fiberwise_of_maps_to` twice, `abs_windowIndexW_le` for the `m`-range.
   Each fibre sits in `log p ∈ (max(a_m, k), … + min(1, 2δ/|t|))`: apply `interval_mass_le`.
2. Main terms `∑ 8·len/k`: a Riemann sum for the log-log measure of the resonant set.  Group
   the blocks of one window, compare `1/k ≤ 2/a` (valid for `a ≥ 2`), then `sum_inv_gap_le`
   + `sum_Icc_symm_le`.
3. Errors `∑_k n_k·10⁵e^{−k/8}`, `n_k ≤ 1 + |t|/(2π)` sub-intervals per block: `sum_exp_neg_le`
   at `c = 1/8`; the `(1 + |t|/2π)` factor is killed by `A₁ := 8 log(C(1+|t|))`.
4. `log p < A₁`: `small_prime_mass_le` at `B = exp A₁`, cost `log A₁ + O(1) ≈ log log|t|`,
   absorbed by `log_log_le_mul_log`.

Then `uniformResonantMass_holds` discharges the hypothesis of
`ttNonPretentious_of_uniformResonantMass`, `logToNaturalCorrelationNZ_two_of_noExc` and
`depthAvg_two_tendsto_of_named`, leaving the `D = 2` layer resting on
`TwoPointNaturalCorrelationNoExc` (the published open problem) and `ProgressionLogRung 2` ALONE.

After that: the generational `K ≥ 3` item.

## Still refuted — DO NOT RETRY

Everything in the `-session-wrap-*` files and the lap-71 list, plus:
* `TTNonPretentious … X L` for `L` up to `log X` (lap 72 — false, not merely open).
* Per-window summation of `reciprocalPrimeInterval_le_log_ratio`: the dependency's Mertens
  error is a flat constant, so `K` windows cost `K·const` (lap 74).
* Dyadic grouping in the window index `m`: gives `(log 4 + 2·mertensBound)·log K`, which
  exceeds the total mass `log log Y` (lap 74).
* `TwistedPrimeSumSaving` / Vinogradov–Korobov as the missing input: it gives a constant
  saving where `L → ∞` needs one growing like `κ log log X` (lap 72).
* The small-prime cutoff at `p ≥ 7` (lap 78) and the per-window architecture (lap 80).

## Confidence

* leaf TRUE ≈ 97 % (unchanged).
* leaf PROVABLE with known techniques ≈ 8 % (unchanged — the `K ≥ 3` wall is untouched).
* **`UniformResonantMass` provable this campaign ≈ 85 %** (new): every ingredient is proved and
  in-kernel; what remains is finite bookkeeping with no missing mathematics.
