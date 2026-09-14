# HANDOFF 2026-09-14 — G4 disjunctivity, lap 8 (`PropJackson` discharged)

Branch `wip/g4-disjunctivity`, HEAD `96155de` (+ this handoff commit).  Not pushed.  Build:
pre-commit `lake build` (8888 jobs) green; `lake build NormalNumbers.G4Jackson` green;
`#print axioms NormalNumbers.G4.Frame.propJackson` = `[propext, Classical.choice, Quot.sound]`.

## Proved this lap (`src/NormalNumbers/G4Jackson.lean`)

**`Frame.propJackson : fr.PropJackson (1/(fr.res · √(fr.D+1))) ((2·fr.D+1)^fr.r)`** for
*every* frame — the §4E smoothing input is no longer a hypothesis.

Route: product Fejér kernel `P(w) = ∏_ν F_D(w_ν)`, `F_D(t) = ‖∑_{k≤D} e(kt)‖²/(D+1)`.
* `norm_mul_norm_dirSum_le`: `‖t‖·‖∑_{k≤D}e(kt)‖ ≤ 1/2` (geometric sum, `‖e(x)−1‖ ≥ 4 dist(x,ℤ)`).
* `norm_mul_fejer_le`: `‖t‖F_D(t) ≤ aF_D(t) + 1/(4(D+1)a)` pointwise — the whole first-moment
  estimate, no interval integral.
* `fejer_expand` (fibre-counted coefficients, `sum_fiberwise_of_maps_to`), `integral_fejer = 1`,
  `fejerCoeff_neg`, `jackKer_expand` over `fourierBox`, `integral_jackKer = 1`,
  `integral_norm_mul_jackKer_le : ∫ ‖w_ν‖P ≤ 1/√(D+1)`.
* `abs_clipTest_sub_le` (`1/ρ`-Lipschitz in `dAv`), `dAv_add_left`, `torusChar_sub`,
  `sum_jackC_eq` (Haar translation invariance on `Torus r`), `norm_sum_jackC_sub_le`,
  `norm_jackC_le_one`, `card_fourierBox`.

Deviation from the draft, recorded: rate `1/√D` not `1/D`.  Harmless for §5 (`D` polynomial in
`1/(εη)`, `Λ = exp(O(rK))` unchanged, C4 still absorbs it).

## Dependency map

`PropA` ✅ · `PropC` ✅ · `PropD` ✅ (modulo two §5 inequalities, `gridFrame_propD_of_bounds`) ·
`PropJackson` ✅ (unconditional, every frame) · **`PropB` open** (all inputs proved; assembly
steps and the paper exponent check are in `PENDING_WORK.md`, lap 8) · §5 schedule open.
Nothing refuted.  `isDisjunctive_four_of_frames` remains CONDITIONAL on `SeparatingFrameExists`.

## Resume here

1. **B assembly** (`gridFrame_propB`), steps (i)–(iv) in `PENDING_WORK.md` lap 8.  The
   route-decisive piece is (iii), Markov in the average metric — it is where the brief's
   "average coordinate torus distance, not the product sup metric" constraint bites, and where
   the `2^r` union over good coordinate sets `G` enters.
2. **§5 schedule module** closing `δ₁ + δ₂ + 2κ + Λδ₃ < 1` in one limit.
