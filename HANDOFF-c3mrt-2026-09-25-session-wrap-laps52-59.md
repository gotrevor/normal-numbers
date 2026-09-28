# HANDOFF c3-mrt 2026-09-25 — SESSION WRAP (laps 52–59)

**Branch** `wip/c3-mrt` · **HEAD** `263dcd5` · working tree **clean** · `lake build` (9257 jobs) and
the chain tip green at every commit.  Read `DIRECTION.md` → CURRENT DIRECTIVE first (it OUTRANKS
this file; its item 4 authorises exactly this work).  Per-lap detail:
`HANDOFF-c3mrt-2026-09-25-lap52.md` … `-lap59.md`.  Earlier: `-session-wrap-laps43-51.md`.

## BUILD HYGIENE

    lake build                              # 9257 jobs
    lake build NormalNumbers.C3MrtProgChase # 8990 jobs — THE CHAIN TIP

New chain (all this session): `… → C3MrtMultiRung → C3MrtBudget → C3MrtTwist →
C3MrtSmallPrimes → C3MrtNatural → C3MrtProgForms → C3MrtProgTrunc → C3MrtProgInner →
C3MrtProgChase`.

## The crux is untouched; this session is pure addition

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged — still the only campaign `sorry` in
`src/`.  `QuantDepthElliott` not edited.  **7 new files, 33 new declarations, every one
`[propext, Classical.choice, Quot.sound]`, zero sorries.**

## Session result — the `D ≥ 2` route is reduced to ONE named open problem

| lap | file | headline declaration |
|---|---|---|
| 52 | `C3MrtMultiRung` | `rung_multi_uniform`, **`rung_multi_correlation`** — the `K`-fold assembly closes |
| 53 | `C3MrtTwist` | **`norm_depthAvg_le_progressions`** — the additive twist costs only `Q` |
| 54 | `C3MrtSmallPrimes` | **`norm_depthAvg_le_omega_progressions`** — the small primes cost only a period |
| 55 | `C3MrtNatural` | `ProgressionLogRung`, `LogToNaturalCorrelation`, **`depthAvg_tendsto_of_transfer`** |
| 56 | `C3MrtProgForms` | `joint_class_prog`, `nondegenerateForms_prog`, `inner_sum_prog_forms` |
| 57 | `C3MrtProgTrunc` | `multi_truncation_bound_set`, `multi_truncation_bound_prog` |
| 58 | `C3MrtProgInner` | `inner_multi_bound_prog`, `multi_bound_of_rung_prog` |
| 59 | `C3MrtProgChase` | **`progression_log_rung_class`** — obligation A, class-indexed form |

### The four real insights of the session

1. **The additive twist is not an obstruction, and this is now proved** (lap 53).  `e(jn/Q)` is
   `Q`-periodic and `Q` is quantified before `N`, so a residue-class decomposition strips it at the
   cost of a FIXED factor `Q`, leaving untwisted correlations along `Q·X + (r+i+1)` — forms with
   pairwise determinant `Q(i'−i) ≠ 0`, exactly `KPointLogElliott`'s domain.  `C3MrtShape`'s
   docstring had argued this heuristically since the start of the campaign.
2. **The small primes are the SAME obstruction as the twist** (lap 54).
   `ζ^{ω_{>P}} = ζ^{ω}·conj(ζ)^{ω_{≤P}}` and `ω_{≤P}` is `primorial P`-periodic, so the
   discrepancy is a unimodular periodic weight.  One decomposition mod `M = Q·primorial P` strips
   BOTH (`norm_sum_periodic_le` subsumes lap 53's `norm_sum_twist_le`), leaving full-`ω`
   correlations.
3. **Nothing in the `K`-fold chain needs the LEAST common multiple** (lap 56).  This is what made
   obligation A cheap instead of a five-file transcription: `multi_forms_det` only asks `d_i ∣ L'`,
   every mass estimate *improves* as the modulus grows, and `∏ d_i ≤ K^{K²}·lcm d ≤ K^{K²}·L'`
   survives verbatim.  Consequences: `multi_truncation_telescope` and `joint_multi_harmonic_mass`
   were already stated for an arbitrary `S` (lap 57 only had to lift `multi_truncation_bound`'s own
   statement), and `multi_full_sum_bound` is used UNCHANGED in lap 58 because `1 + R/progLcm` is
   *stronger* than the `1 + R/lcm` it asks for.
4. **The barrier is exactly log-Chowla ⇏ Chowla, and I checked it rather than assuming** (lap 55).
   Log control gives `S(N) = o(log N)`; the natural window mean over `(X, AX]` needs
   `S(AX) − S(X) = o(1)`.  Partial summation converts window-uniform log bounds of size `δ` into
   natural bounds `O(δ)` — but here `δ ≍ ε log X`, not `o(1)`.  So it is not bookkeeping.

### Where the ledger stands

`ConjC3`'s `D ≥ 2` route rests on, and only on:

1. `KPointLogElliott K` = Tao–Teräväinen's product log-Elliott (**published**);
2. `TwistedPrimeSumSavingAllLevels` (the Vinogradov–Korobov-type input);
3. `ProgressionLogRung K` — **proved in class-indexed form** (`progression_log_rung_class`, lap 59);
   only the weight bridge (brick 4b, below) remains to match the stated `Prop`;
4. **`LogToNaturalCorrelation K` — the log-Chowla ⇏ Chowla barrier (a named open problem)**;
5. uniformity in `D` along `D = D_N ≍ log log log N`, quantified by `QuantDepthElliottGen` /
   `budget_absorb`, needing `η N ≤ exp(−C(log log log N)⁴)` (lap 40).

`depthAvg_tendsto_of_transfer` (lap 55) proves the natural-density `D`-point rung at every FIXED
`D` from items 3+4 — the campaign's first natural-density multi-point statement, generalising
`depthAvg_one_tendsto` (Selberg–Delange, `D = 1`).

## NEXT — resume here

1. **Brick 4b, the weight bridge** (small, fully specified in `-lap59.md`).  `ProgressionLogRung`
   uses the progression-variable weight `(m+1)⁻¹`; lap 59 delivers the class weight `(n+1)⁻¹`.
   `(m+1)⁻¹ − Mo·(Mo·m+r+1)⁻¹ = (r+1−Mo)/((m+1)(Mo·m+r+1))`, absolutely `≤ Mo/(m+1)²`, and
   `sum_inv_sq_le` (`C3MrtRungTwo:372`) is already in the repo.  `ε ↦ ε/Mo` absorbs the factor.
   `class_sum_reindex` (lap 53) does the index bookkeeping.  Then obligation A is a theorem and
   item 3 leaves the ledger.
2. **Then the `D`-uniform / quantitative statement.**  `weylLambertTwist_of_kfold_bound` wants an
   explicit `η N`; `progression_log_rung_class` is ε-for-every-ε.  So restate obligations as
   `η`-shaped (quantitative `KPointLogElliott`), with lap 40's `η N ≤ exp(−C(log log log N)⁴)` as
   the target class.  This is the last bookkeeping item; after it the ledger is
   `ConjC3 ⟸ (Tao–Teräväinen, quantitative) + (VK) + (log→natural)`.

## Still refuted — DO NOT RETRY

Everything in `-session-wrap-laps40-42.md` and `-laps43-51.md`.  Added this session:
* Fourier-expanding the periodic weight to avoid progressions — it just reproduces additive
  twists, which is where we started (lap 58 thinking).
* Getting natural density from the log-averaged bound by partial summation over dyadic windows —
  computed and refuted in lap 55 (the window difference is `o(log N)`, not `o(1)`).

## Confidence

* obligation A fully discharged: **≈97%** (only the weight bridge remains, fully specified).
* leaf TRUE ≈ 97%.
* leaf PROVABLE with known techniques ≈ 20% — *down* slightly and deliberately: this session
  removed every gap EXCEPT the log→natural barrier, which sharpens the honest estimate to "the
  route is complete modulo one named open problem plus a decay class", rather than moving it.
