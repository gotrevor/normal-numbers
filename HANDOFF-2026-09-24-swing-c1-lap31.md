# Handoff — swing at C1, laps 27–31: Elliott → Delange + one decorrelation

**Branch** `wip/swing-c1` · **HEAD** `998749b` · tree clean, NOT pushed
**Build**: full `lake build` green, **9182 jobs**.
**Objective**: `KICKOFF-2026-09-24-swing-c1.md` (supersedes `DIRECTION.md` and older handoffs).

## New files this session (all additive; `SwingC1.lean` untouched)

| file | status |
|---|---|
| `SwingC1Model.lean` | **sorry-free** (leaf (M) complete) |
| `SwingC1Depth.lean` | **sorry-free** (finite-depth reduction, leaf (B)) |
| `SwingC1Delange.lean` | **sorry-free** (Elliott → Delange + `ShiftIndep`) |
| `SwingC1Pair.lean` | 1 named leaf: `norm_pairLocalFactor_le` |

`SwingC1.lean` still has exactly its two ratified `sorry`s (`hDepthAll` l. 920, `conjC1` l. 2201),
per the kickoff addendum.  Nothing was deleted, renamed or weakened.

## What landed

### lap 27 — leaf (M) DONE (unconditional randomness)
`periodMean_tendsto_zero`: `‖periodMean (e(h·θ^{(P)})) (primorialLe P)‖ → 0` for all `b ≥ 2`,
`h ≠ 0`.  Chain: `periodMean_phase_truncTail` (CRT) + `norm_localFactor_le` + Mertens.
`norm_localFactor_le` key step: the EXACT identity `h·b^{p−1−i}/(b^p−1) − t = t/(b^p−1)` with
`t = h/b^{1+i}`, `b^{1+i} > 2|h|`, plus `b^p − 1 ≥ p`; two unit vectors `δ/2` apart give
`‖z+w‖ ≤ 2 − δ²/16` (parallelogram).  Reusable helpers: `norm_add_le_of_norm_sub_ge`,
`norm_phase_sub_phase`, `norm_phase_sub_one_le`, `phase_ne_one`.

### lap 28 — the finite-depth reduction; two-block truncation REFUTED
Refutation: `sum_primePeriodicTerm_period` ⇒ no truncation of the PRIME expansion is uniformly
small below cut `2M`, and at that cut the period `≈ e^{2M}` exceeds `M`.  Truncate in `k` instead:
`norm_phase_omegaTail_sub_head`, `norm_fullMean_phase_sub_head`,
`depthBound_tendsto_zero_of_pow_div_atTop` — the Weyl mean equals the depth-`L` mean up to
`4π|h|(log₂(M+L)+1)/b^L`, so depth `L(M) ≍ 2 log_b log₂ M` suffices and BOUNDED depth is refuted.

### lap 29 — leaf (B), and its correction
`windowVal_eq_trunc_of_tail_le` + `fract_omegaTail_pos` (from the repo's
`G4.irrational_primeLambertAtBase`, via the new bridge `primeLambert_mul_pow`) +
`exists_good_depth` give `goodDepth` with an EMPTY bad set.  ⚠️ **Correction, same lap**: since
`goodDepth n ≥ n`, that only proves `hDepth_iff_hWindowChar : HDepth b L ↔ HWindowChar b L` — the
carry is not where any difficulty lives, and "choose the depth profile cleverly" is refuted, but
the crux is not weakened.  Leaf (B)'s honest content at a SLOW profile is stated and reduced:
`OrbitNonConc b L κ → HCarryOverflowAt b L κ` (`hCarryOverflowAt_of_orbitNonConc`).

### lap 30 — **Elliott → Delange + one decorrelation** (the session's main result)
`phase_omegaTail_factor` (from `omegaTail_rec`): `e(hθ_n) = e((h/b)ω(n+1))·e((h/b)θ_{n+1})`.  Hence
```
weylMean_tendsto_zero_of : 2 ≤ b → DelangeMean (h/b) → ShiftIndep b (h/b) → weylMean b h → 0
```
`DelangeMean` is Delange (1969), a KNOWN theorem (Selberg–Delange), not in mathlib.  `ShiftIndep`
is one decorrelation.  Strictly and substantially weaker than Elliott.

### lap 31 — the Daboussi–Kátai pair factors
`ShiftIndep` is exactly the multiplicative-BSZ (Daboussi–Kátai) hypothesis, whose input is
`mean_n e(t(θ_{pn} − θ_{qn})) → 0`, `p ≠ q` prime.  Proved: `pairLocalFactor`,
`norm_pairLocalFactor_le_one`, `primePeriodicTerm_mul_mod`, `periodMean_phase_truncPairTail` (CRT),
`prod_pairLocalFactor_tendsto_zero`, `periodMean_pair_tendsto_zero`.  Refactor: the Mertens engine
is now the shared `prod_tendsto_zero_of_norm_le` in `SwingC1Model.lean`.

## THE next move (start here)

**Prove `norm_pairLocalFactor_le`** (`SwingC1Pair.lean`, the only new open leaf).  Its docstring
has the complete mechanism; it is `norm_localFactor_le` (proved) plus ONE pigeonhole:
* `s_j := p⁻¹(r−1−j) mod r` ⇒ first exponent `r−1−j`, term → `t·b^{−1−j}`;
* `c_j := qp⁻¹(r−1−j) mod r` runs over an AP of nonzero step, so the `c_j`, `j ∈ [i, 2i+2]`, are
  distinct and at most `i+1` can exceed `r−2−i`; pick a `j` that does not.  Then the second term
  is `≤ b^{−1}` times the first, so the `s=0` vector `1` and the `s_j` vector are a fixed `δ` apart.
* `c_j = r−1−j` is impossible (it forces `r ∣ q−p`), so exclude `r ≤ p*q + |p−q|`.
* Finish with `norm_add_le_of_norm_sub_ge` exactly as in `norm_localFactor_le`.
Ingredients: `(p : ZMod r)⁻¹`, injectivity of `x ↦ qp⁻¹x` on `ZMod r`, one `Finset.card` pigeonhole.

Then, in order:
1. Assemble Daboussi–Kátai: state the criterion as a named Prop and derive `ShiftIndep` from
   `mean_n e(t(θ_{pn} − θ_{qn})) → 0`.
2. The remaining honest gap on BOTH pair and single factors is the same one:
   **natural density vs. one full period** (leaf (D)).  For the DIFFERENCE there is extra room —
   no `r`-independent drift — which is the reason to push the pair side first.
3. `DelangeMean` is a known theorem; formalizing Selberg–Delange is a separate mathlib-scale
   project.  Do NOT attack it inside this swing; keep it a named hypothesis.

## Standing constraints (unchanged)

* Do not edit `CastingOut.lean`, `CastingOutCount.lean`, `CastingOutLambert.lean`, `Maze.lean`,
  `papers/`, `agent-mail/`, other KICKOFFs.  Work in `src/NormalNumbers/SwingC1*.lean`.
* `conjC1`, `hDepthAll` stay as `sorry`s in `SwingC1.lean` until proved — deleting or restating
  them is a failure, not completion.
* Never use `axiom`; named hypotheses (`DelangeMean`, `ShiftIndep`, `OrbitNonConc`) are the
  sanctioned device.
* `PENDING_WORK.md` carries the per-lap record including the two refutations and the lap-29
  self-correction; read its last five sections before planning.
