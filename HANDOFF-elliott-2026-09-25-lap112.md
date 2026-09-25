# HANDOFF elliott 2026-09-25 lap 112 (DEEP REFLECTION) — (c′-I) PROVED, and three "cited" inputs turn out to be in-repo

Branch `wip/elliott-port`, HEAD `100e906`, working tree **clean**.
**Green means BOTH targets**: `lake build` → 9257 jobs · `lake build NormalNumbers.ElliottAxiomAudit`
→ 9684 jobs.  Never `lake exe cache get`.  Never edit `.lake/packages/`.
`DIRECTION.md` CURRENT DIRECTIVE governs — read it first (it was rewritten this lap).
`src/` Elliott scope has **zero `sorry`**; every open obligation is a named `Prop`.

## What this lap did

**1. The reflection (committed as `77cbb82`).**  Route verdict **CONTINUE**; no registered trigger
fired.  Full synthesis in `PENDING_WORK.md` → "🧘 Reflection — 2026-09-25 (DEEP REFLECTION lap 112)"
and in the rewritten `DIRECTION.md` CURRENT DIRECTIVE.  Three findings:

* 🔑 **`src/PNTPort/ZetaBounds.lean` is in this repo, 3142 lines, ZERO `sorry`, 3597 jobs**, and
  proves `ZetaZeroFree9`, `LogDerivZetaBnd`, **`LogDerivZetaBndUnif99`** (`‖ζ'/ζ(σ+it)‖ ≤
  C(log|t|)⁹` for all `σ ≥ 1−A/(log|t|)⁹`, `|t|>3`), `ZetaUpperBnd`, `ZetaInvBnd`,
  `triv_bound_zeta` — verified `[propext, Classical.choice, Quot.sound]` this lap.  That is a de la
  Vallée Poussin-strength input the campaign has been *citing* since lap 95.
  ⛔ `import PrimeNumberTheoremAnd.ZetaBounds` **FAILS** (a partial `lean_lib` of that name in
  `lean-proofs-latest` shadows the real package).  **Import `PNTPort.ZetaBounds`.**
* 🔑 `src/NormalNumbers/G4MertensAP.lean` proves `mertensRate_residueClass`, which is the whole
  content of the open `Prop` `ElliottCharRigidity.PrimeDensityAP`.
* ⚠ **Correction to lap 92's directive**: `PrimeDensityAP` is NOT proved (bare `def … : Prop`) and
  is NOT off the critical path — every live consumer takes it as a hypothesis.

**2. (c′-I) PROVED (committed as `100e906`).**  New `src/NormalNumbers/ElliottSliceCap.lean`,
sorry-free, all seven theorems trust-triple, all in the audit surface.

| theorem | content |
|---|---|
| `exists_far_band_bound_le`, `exists_band_logDeriv_bound` | `ElliottZetaPole`'s sub-unit bound with the right edge `Re s ≤ 2` widened to an arbitrary `B`.  **Why it was needed**: inside the cap band `Re s = 1+δ+w` and `w ≤ max(|v|,δ) ≤ 1`, so `Re s` can exceed `2` by `δ`; `B = 3` is what the band actually requires. |
| `norm_term_vonMangoldt` | `‖LSeries.term ↗Λ s n‖ = Λ n · n^{-Re s}` (`LSeries.norm_term_eq`, `Λ ≥ 0`). |
| **`norm_slice_add_logDeriv_le`** | **THE BRIDGE**: `‖logWeightedSlice v X Y w + ζ'/ζ(sliceAbscissa X w v)‖ ≤ 1 + ppCost` for `X ≥ 2²⁰`, `Y ≥ sliceCut X`, `w ≥ 0`. |
| **`exists_sliceCapSmall`** | `∃ K ≥ 0, SliceCapSmall K` — **(c′-I)**. |
| **`exists_shiftedMertensSmall`** | `∃ K, ShiftedMertensSmall K`, end to end. |
| `twoPointElliottLog_of_two_bands` | the consumer on the **three** remaining inputs. |

## Facts worth not re-deriving

* **The bridge recipe that worked.**  `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
  (needs `1 < Re s`) + `logDeriv_apply`; `LSeriesSummable_vonMangoldt`; `summable_norm_iff` both
  ways; split `term = (if n ∈ S then term else 0) + tailFun` and use **`Summable.tsum_add`** then
  **`tsum_eq_sum`** for the finite part; bound `‖∑' tailFun‖` by `norm_tsum_le_tsum_norm` then
  **`Summable.tsum_le_of_sum_le`** (these are *methods*, not root-level `tsum_add` /
  `tsum_le_of_sum_le`, which do **not** exist).
* `Complex.abs_re_le_norm` / `Complex.abs_im_le_norm` give `‖s−1‖ ≥ max(δ+w, |v|) ≥ T` in one line.
* `set s := … with hs` does **not** fold `s` into hypotheses created *afterwards*; use
  `rw [← hs] at h`.
* `inv_anti₀` (not `inv_le_inv_of_le`); `summable_of_ne_finset_zero` (not
  `summable_of_finite_support`).

## NEXT LAP — T2, `ArchCorrModerate`, from `PNTPort.ZetaBounds`

The directive's mandated move.  Shape of the work:

1. `import PNTPort.ZetaBounds` in a new `ElliottSliceCapModerate.lean`.
2. State an exponent-9 moderate cap: `SliceCapModerate9 K` = the `SliceCapModerate` clause with
   `T` replaced by `max ((Real.log (|v|+16))^(-9 : ℝ)) (Real.log X)⁻¹`, and the matching
   `SliceBoundModerate9`, `DampedSeriesBoundModerate9` (copy laps 102/106's two proofs verbatim;
   only the definition of `T` changes, and both proofs only use `δ ≤ T ≤ 1`).
3. Prove `SliceCapModerate9` from **`norm_slice_add_logDeriv_le`** (already proved, it is uniform
   in `v`) plus `LogDerivZetaBndUnif99` for `|v| > 3`, and `exists_band_logDeriv_bound` extended to
   `1 ≤ |Im s| ≤ 3` by the same compactness argument for `1 < |v| ≤ 3`.
4. `ArchCorrModerate` then holds with the constant `9` in front of `log log(|v|+16)`; generalise
   `ElliottArchBands.ArchCorrModerate` to `C·log log(|v|+16) + K` and fix
   `archCorrLargeShift_of_moderate_and_nearMax` by moving the height cut from `exp((log X)^{1−ν})`
   to `exp((log X)^{(1−ν)/C})` (only `logLog_heightCut` and the `hstep` calc change).

Then **T3** `PrimeDensityAP` from `G4MertensAP.mertensRate_residueClass` +
`Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le`.  After T2 and T3 the ledger reads:
**one cited 🟠 axiom (`ArchCorrNearMaxHeight` = Vinogradov) and a fully built remainder.**

## Doc map

`DIRECTION.md` CURRENT DIRECTIVE (lap 112, binding) · `STATUS.md` (refreshed lap 112, axiom ledger) ·
`PENDING_WORK.md` top section (the reflection, then laps 95–111 attack paths) ·
`ON-LINE-REQUEST.md` (Tao 2016 arXiv:1509.05422 — would settle whether the `|t| ≤ A·x` range, and
hence the Vinogradov wall, is real) · `HANDOFF-elliott-2026-09-25-lap111.md` (previous) ·
audit surface `src/NormalNumbers/ElliottAxiomAudit.lean`.
