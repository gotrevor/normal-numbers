# HANDOFF elliott 2026-09-25 laps 95–102 — (c′) cut into bands; both soft inputs reduced to `ζ'/ζ`

Branch `wip/elliott-port`, HEAD `c9d4883`, working tree **clean**.
**Green means BOTH targets**: `lake build` → 9257 jobs · `lake build NormalNumbers.ElliottAxiomAudit`
→ 9680 jobs.  Never `lake exe cache get`.  Never edit `.lake/packages/`.
`DIRECTION.md` CURRENT DIRECTIVE governs — read it first, do **not** edit it (altitude laps own it).

## Where the campaign stands

The headline (`ElliottGeneral.nonasymptoticLogElliott`, `…Mult`) has been proved and axiom-clean
since lap 83/84 — **verified again this session**, trust triple, no `sorryAx`.  The operator's
kickoff objective (the two `ElliottLeafTwo` sorries) was therefore already met before lap 95; these
laps worked DIRECTION's live objective instead: making `TwoPointElliottLog` rest on TRUE classical
inputs.  `src/` Elliott scope still has **zero `sorry`**: every open obligation is a named `Prop`.

## The input list, before and after

| lap 94 | now (lap 102) |
|---|---|
| `PrimeDensityAP` | `PrimeDensityAP` (unchanged) |
| **(c′)** one Archimedean bound over the whole range `T X < \|v\| ≤ A²X` | `SliceBoundSmall` (pole-local `ζ'/ζ`; needs only `ζ(1+it) ≠ 0`, **already in mathlib**, + compactness) |
| | `SliceBoundModerate` (de la Vallée Poussin `\|ζ'/ζ(σ+iv)\| ≪ log\|v\|`) |
| | `ArchCorrNearMaxHeight` (**Vinogradov–Korobov**, only `\|v\| > exp((log X)^{1-ν})`) |

Consumer chain, all proved: `twoPointElliottLog_of_three_bands` ← `twoPointElliottLog_of_bands` ←
`archimedeanCorrelationBoundAbove_of_bands` ← `archCorrLargeShift_of_moderate_and_nearMax`;
and `shiftedMertensSmall_of_dampedSeriesBound` ∘ `dampedSeriesBoundSmall_of_sliceBound`
(resp. `archCorrModerate_…`) connect the soft inputs to the slice statements.

## What landed, lap by lap (all sorry-free, all trust triple, all in the audit surface)

* **95** `ElliottArchBands.lean` — (c′) cut at `|v| = 1`; `ShiftedMertensSmall` + `ArchCorrLargeShift`
  ⟹ (c′) with `η = min ρ η₁/4`.  `ElliottSmallShift`'s `harch` hypotheses restricted to `0 < r < 1`
  (for `r ≥ 2` the threshold degenerates to `0` and the statement is FALSE).
* **96** Fidelity correction + `heightCut`; `ArchCorrModerate` + `ArchCorrNearMaxHeight` ⟹
  `ArchCorrLargeShift`.  The Vinogradov site is only near-maximal height.
* **97** `ElliottDamped.lean` — Mertens I in the campaign's index set; `norm_archCorr_sub_dampedArchCorr_le`.
* **98** `dampedTail_le` (block iteration over `(X^{2^k}, X^{2^{k+1}}]`); `norm_archCorr_sub_dampedPrefix_le`.
* **99** `ElliottLogIntegral.lean` — `integral_le_one_add_log`; `DampedSeriesBound*` + reductions.
* **100** `integral_rpow_neg_Ioi`; **`dampedPrefix_eq_integral`** (the interchange).
* **101** `norm_logWeightedSlice_le_decay` (`≤ 4·∑n^{-3/2}·2^{-w}` for `w ≥ 1`).
* **102** integrability/continuity of the slice, `integral_norm_slice_Ioi_le`,
  `integral_le_one_add_log_add_const`, **`norm_dampedPrefix_le_of_slice_le'`**, `SliceBound*` and
  their two reductions.

## Refutations and corrections recorded (do not retry)

* ⛔ **(c′-vdC) is refuted as recorded.**  Van der Corput's `k`-th derivative test only replaces the
  trivial `log t` in `|ζ(1+it)|` by `(1/k)log t` — an *additive* `O(1)` saving on `archCorr`, while
  the consumer needs a *proportional* one.  A power saving needs `k ≍ (log t)^η` uniformly, i.e.
  Vinogradov.  The Halász half is independently vacuous: `∑_{n≤X} n^{-iv} = X^{1-iv}/(1-iv)+O(1+|v|)`
  exactly, of size `≍ X/|v|`, so it reproves only what the trivial bound gives.
* ⚠ Lap 95's "(c′-I) is free of a zero-free region" was **wrong** and is corrected in the module
  docstring: Abel summation against Mertens with an absolute-constant error costs `|v|·∫|E|`,
  `O(1)` only for `E = O(1/log²u)`.  The ζ-analytic route (lap 97+) is what works instead.
* The multiplicative `K·T⁻¹` slice shape is **wrong** for this consumer (it multiplies the log);
  the additive `1/|s−1| + C` shape is both true and what the calculus lemma needs.

## Traps recorded these laps

* `import PrimeNumberTheoremAnd.IEANTN.Mertens` FAILS — `lean-proofs-latest` shadows that module
  root.  The importable path is **`ErdosProblems.Erdos49.PNT.IEANTN.Mertens`** (sorry-free,
  `Mertens.sum_log_prime_div_eq_log`, constant `log 4 + 4`).
* `open Finset` makes bare `Ioi` a `Finset.Ioi`; write `Set.Ioi` in measure-theory code.
* `MeasureTheory.setIntegral_union` (Bochner/Set.lean) is the union splitter; `integral_union`
  does not exist.  `MeasureTheory.integral_finsetSum` (not `integral_finset_sum`, deprecated).
* `Integrable.of_integral_ne_zero` gives integrability free once the integral's value is computed.
* `Real.rpow_le_rpow_of_nonpos (0<x) (x≤y) (z≤0) : y^z ≤ x^z`; `Summable.sum_le_tsum` (not
  `Finset.sum_le_tsum`); `le_or_gt` (not `le_or_lt`).
* `δ = 1/log X ≤ 1` FAILS at `X = 2`; the damped-series Props carry `X₀ = 3`.

## What the next lap does

Attack `SliceBoundSmall` (input 2) — the softest of the three ζ-side inputs, and the only one whose
key ingredient (`ζ(1+it) ≠ 0`) is already in mathlib.  **Before writing Lean, settle the shape**:
the slice is the *truncated* prime series, and the truncation `∑_{p>Y}` is NOT `O(1)` slice-wise —
only after the `w`-integration (lap 98's `dampedTail_le`).  So either
(a) restate `SliceBound*` for the FULL prime series and re-route the truncation through
`dampedTail_le` at the integrated level, or (b) keep the truncated slice and carry a `w`-dependent
error.  (a) looks right.  The other elementary piece is the prime-power correction
`∑_{p,k≥2} log p · p^{-kσ} ≤ 2∑_p log p · p^{-2σ}`, same `p`-series technique as lap 101.

`ArchCorrNearMaxHeight` remains the one deep wall; the recorded probe is whether the classical
zero-free region's *shape* `σ > 1 − c/log|t|` already yields a power saving in `log X` when
`log|t| ≫ (log X)^{1-ν}`.

## Doc map

`DIRECTION.md` CURRENT DIRECTIVE (lap 92, binding) · `PENDING_WORK.md` top section (live attack
paths, laps 95–102) · `ROUTE-ESCALATION-2026-09-25-archimedean.md` (the lap-92 refutation+repair) ·
`HANDOFF-elliott-2026-09-25-lap94.md` (previous) · audit surface
`src/NormalNumbers/ElliottAxiomAudit.lean`.
