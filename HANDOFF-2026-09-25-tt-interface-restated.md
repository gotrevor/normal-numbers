# HANDOFF 2026-09-25 — the TT interface: defects machine-checked, statements repaired, SURVIVORS table

Lap type: **restatement run** (operator-scoped).  No crux advance, by instruction.
All of (a)-(c) done; `lake build` green (9439 jobs), all new results
`[propext, Classical.choice, Quot.sound]`.

New module: `src/NormalNumbers/C3MrtTTDefect.lean`.  Three `Maze.lean` kernel rows + four
aliases.

## (a) The defects, as theorems

| theorem | content |
|---|---|
| `ttPretentiousSum_nonneg` | every summand of TT's sum is `≥ 0` for 1-bounded `g` |
| `ttNonPretentious_trivial` | `TTNonPretentious g X L` for **every** 1-bounded `g`, `0 < L`; witness `A = 1/L` |
| `ttNonPretentious_one` | …in particular for `g = 1` |
| `not_kPointNoExcWith_const_one` | `¬ KPointNoExcWith cK CstK 2` whenever `0 < cK 2` |
| `not_kPointNaturalCorrelationNoExc` | `¬ KPointNaturalCorrelationNoExc 2` |
| `kPointNoExcWith_of_twoPointNoExc` | the missing converse of `twoPointNoExc_of_kPointNoExc`, available exactly because the hypothesis is free |
| `not_twoPointNaturalCorrelationNoExc` | **the "named open problem" is FALSE**, not open |
| `twoPointNaturalCorrelation_trivially_true` | `TwoPointNaturalCorrelation` is TRUE via `E = ℕ ∩ [√X, X]` |

The `not_kPointNoExcWith_const_one` witness: `K = 2`, `g 0 = g 1 = 1`, `W = 1`, `b = 0`,
`hsh = ![1,2]`, `X = exp L`, `N = ⌈√X⌉`, `L` chosen with `L^{cK 2} ≥ max 2 (CstK 2 + 2)`
(`exists_rpow_ge`).  LHS `= (1/N)·N = 1`; RHS `= CstK 2/L^{cK 2} < 1`.

## (b) The faithful restatements

* `ttPretentiousSumChar g X χ t` — TT's `M(g; X², Q)` summand **with Dirichlet characters**;
  `ttPretentiousSumChar_one` identifies the `q = 1` case with the old `ttPretentiousSum`.
* `TTNonPretentiousAt A g X L` — the implied constant `A` is a **parameter** (outside `X, L`);
  characters of modulus `q ≤ (log X)^{1/125}`; twists `|t| ≤ X²` (TT's range, not `Q`).
* `TTNonPretentiousUnif g := ∃ A > 0, ∀ X L …` — the `≫`-faithful form.
* `ttNonPretentious_of_At` — faithful ⇒ old, so the swap weakens **no** consumer.
* `dyadicScales X : Finset ℕ` and `TwoPointDyadicCorrelation A` — the exceptional set is a
  `Finset` of dyadic scales whose cost is a *fraction* `≤ Cst·L^{-c}` of `#(dyadicScales X)`:
  a counting/log-density cost.
* `KPointNoExcAtWith A cK CstK K` — the `K`-point input on the faithful hypothesis;
  `kPointNoExcAtWith_of_with` (old ⇒ faithful).

### Non-vacuity guards

| guard | says |
|---|---|
| `not_ttNonPretentiousUnif_one` | `TTNonPretentiousUnif` is **false for `g = 1`** — not trivially true (contrast §1) |
| `not_ttNonPretentiousAt_one` | `¬ TTNonPretentiousAt A 1 X L` once `1 < A·L` |
| `const_one_not_faithful` | hence the §2 refutation of the `K`-point input is **blocked** at the faithful hypothesis: it needs large `L`, and there the hypothesis fails |
| `full_exceptional_set_not_admissible` + `exists_L_cost_lt_one` | the §3 free-exceptional-set trick is **forbidden**: the all-scales set breaks the counting cost at any `L` with `Cst L^{-c} < 1`, and such `L` exist |

## (c) SURVIVORS table

Rule used: a theorem whose hypothesis list contains a **refuted** `Prop`
(`KPointNoExcWith`/`Roots`/`Depth`/`At`/`AllWith`, `KPointNaturalCorrelationNoExc`,
`TwoPointNaturalCorrelationNoExc`) is **VACUOUS** — true, but with an unsatisfiable antecedent.
A theorem whose hypothesis is `TTNonPretentious` alone is **FREE-HYP**: correct, but the
hypothesis adds nothing (it is provable outright), so it carries no arithmetic content.
A theorem over `TwoPointNaturalCorrelation` is **EMPTY**: its antecedent is provable (§3) and
therefore its conclusion is unconditional *and* content-free, because the conclusion is only
ever asked off an exceptional set that may be all integer scales.

| module | declarations | verdict |
|---|---|---|
| `C3MrtUnifK` | `dyadic_window_bound_with`, `windowPhi_hwin`, `depthAvg_le_with`, `depthAvg_diag_tendsto_of_unif`, `depthAvg_gen_tendsto_of_unif`, `depthAvg_diag_tendsto_of_uniform`, `depthAvg_diag_tendsto_of_degrading`, `depthAvg_gen_tendsto_of_degrading`, `depthAvg_diag_tendsto_of_degrading_sched`, `depthAvg_gen_tendsto_of_degrading_sched`, `depthDiagonal_of_degrading`, `weylLambertTwist_of_degrading`, `depthAvg_gen_tendsto_of_geom`, `depthDiagonal_of_geom`, `weylLambertTwist_of_geom` | VACUOUS |
| `C3MrtSlowSched` | `depthAvg_gen_tendsto_of_geom_slow`, `depthDiagonalSlow_of_geom`, `weylLambertTwist_of_geom_slow`, `weylLambertTwist_of_geom_slow_of_with`, `conjC3_of_geom_slow`, `weylLambertTwist_of_geom_input`, **`conjC3_of_geom_input`** | VACUOUS — the lap-90 headline included |
| `C3MrtRootsInput` | `dyadic_window_bound_roots`, `windowPhi_hwin_roots`, `depthAvg_le_roots`, `depthAvg_gen_tendsto_of_unif_roots`, `depthAvg_gen_tendsto_of_geom_slow_roots`, `depthDiagonalSlow_of_geom_roots`, `weylLambertTwist_of_geom_slow_roots`, `weylLambertTwist_of_geom_input_roots`, `conjC3_of_geom_input_roots` | VACUOUS |
| `C3MrtDepthInput` | `dyadic_window_bound_at`, `windowPhi_hwin_at`, `depthAvg_le_depth`, `depthAvg_gen_tendsto_of_unif_depth`, `depthAvg_gen_tendsto_of_geom_slow_depth`, `depthDiagonalSlow_of_geom_depth`, `weylLambertTwist_of_geom_input_depth`, `conjC3_of_geom_input_depth`, `conjC3_of_geom_input_roots'` | VACUOUS |
| `C3MrtEvtInput` | `depthAvg_gen_tendsto_of_unif_evt`, `depthAvg_gen_tendsto_of_geom_slow_evt`, `depthDiagonalSlow_of_geom_evt`, `weylLambertTwist_of_geom_input_evt`, `conjC3_of_geom_input_evt`, `conjC3_of_geom_input_depth'` | VACUOUS |
| `C3MrtDyadicInput` | `depthDyadicBound_of_depth`, `conjC3_of_geom_input_evt'` | VACUOUS |
| `C3MrtKPointNoExc` | `dyadic_window_bound_K`, `logToNatural_K_of_noExc`, `logToNaturalCorrelationNZ_of_kPointNoExc`, `depthAvg_K_tendsto_of_noExc`, `twoPointNoExc_of_kPointNoExc` | VACUOUS |
| `C3MrtNoExc` | `dyadic_window_bound_of_noExc`, `class_sum_tendsto_of_noExc`, `logToNatural_two_of_noExc`, `twoPointNatural_of_noExc` | VACUOUS |
| `C3MrtTTPretentious` | `logToNatural_two_of_noExc_of_ne_one`, `logToNaturalCorrelationNZ_two_of_noExc`, `depthAvg_two_tendsto_of_named` | VACUOUS |
| `C3MrtUniformMass` | `logToNaturalCorrelationNZ_two_of_noExc'`, `depthAvg_two_tendsto_of_noExc` | VACUOUS |
| `C3MrtNoExcAll` | `kPointNoExcWith_mono`, `kPointNoExcAllWith_of_with` | STRUCTURAL — true and content-free (monotonicity / implication between two false `Prop`s); reusable once rethreaded |
| `C3MrtUnifK` | `kPointNoExc_of_with`, `exists_with_of_kPointNoExc` | STRUCTURAL, and `exists_with_of_kPointNoExc` is **load-bearing in the refutation** |
| `C3MrtTTThm31` | `c3_two_point_natural_of_TT` | EMPTY (antecedent provable, conclusion content-free) |
| `C3MrtTTPretentious` | `ttNonPretentious_of_uniformResonantMass` | FREE-HYP — **but the one genuine survivor**: its proof produces `A = exp(−C₁)` with `C₁ = C₁(z)` only, i.e. it already gives the *uniform* constant `TTNonPretentiousAt` needs.  What it does **not** give is characters `q > 1` or twists up to `X²`. |
| `C3MrtUniformMass` | `ttNonPretentious_zOmegaNat` | FREE-HYP, same remark |
| everything not in this table | `kPointThresholdSlow_of_geom`, `depthDiagonal_of_quantDepthElliottGen`, `weylLambertTwist_of_depthDiagonal`, `weylLambertTwist_of_depthElliottLL`, the schedule/threshold/window algebra, `depthRoot` theory, `CastingOut` proper | SURVIVE with content — none of it mentions a refuted `Prop` |

**Net reading.** Nothing arithmetic was lost: the vacuous rows are all *plumbing* (window
algebra, dyadic bookkeeping, schedule composition) whose proofs go through verbatim once the
hypothesis is `KPointNoExcAtWith A`.  What was lost is the **claim** that the headline rested
on one honest published input: the input as stated was false, and the `D = 2` "named open
problem" was false too.

## Next attack (for the lap after this one)

1. **Rethread** the chain from `KPointNoExcWith` onto `KPointNoExcAtWith A`, bottom-up:
   `dyadic_window_bound_with` → … → `conjC3_of_geom_input`.  The consumer side must now
   *supply* `TTNonPretentiousAt A (zOmegaNat (depthRoot b h' 0)) X L`, and the `A` must be
   uniform in `b, h', X, L` — that is the real new obligation, and it is where
   `ttNonPretentious_of_uniformResonantMass` has to be upgraded (characters, twists ≤ X²).
   Do **not** rethread onto `TTNonPretentious`; it is free.
2. **Restate the correlation input** as `TwoPointDyadicCorrelation`-shaped at general `K`
   (dyadic-scale exceptional set with a counting cost), and check TT 3.1(ii)'s actual
   conclusion shape against `papers/tao-teravainen-2025-quantitative-correlations.txt:1566`
   once more — in particular whether the dyadic-window conclusion is for all `N ∈ [√X, X]∖E`
   with `E` a real-scale set of log-measure, in which case the honest formal cost is
   `∫_E dt/t` **plus** a statement that the integer scales in a dyadic block inherit it.
3. The crux is unchanged in substance (one Weyl sum, lap 100-101) but its *interface* is now
   `KPointNoExcAtWith`.

---

## Lap 103 addendum — the headline is repaired (same session, after the restatement)

`C3MrtUnifK.KPointNoExcFor Pnp` + `C3MrtSlowSched.ArchSupply Pnp` make the whole
window/schedule/threshold chain parametric in the archimedean hypothesis, *in place* (old names
kept as wrappers, no duplication).  Hence

    C3MrtFaithfulInput.conjC3_of_geom_input_at :
      (∀ b ≥ 3, ∀ K, KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K) →
      (∀ b ≥ 3, ArchSupply (TTNonPretentiousAt A) b) → ConjC3      (0 < θ < 1)

axiom-clean.  Every row of the SURVIVORS table marked VACUOUS is therefore *recoverable* by the
same substitution — the plumbing was never the problem.  The ledger now honestly shows TWO open
inputs (correlation + archimedean supply); the archimedean one used to be hidden inside the
vacuous `archSupply_tt`.

## Lap 104 addendum — the new crux, decomposed

`C3MrtArchFaithful.lean`: the faithful archimedean supply is *exactly* one bound on
`Re(z · ∑_{p≤X²} conj(χ(p))p^{-it}/p)` (`ttPretentiousSumChar_eq`, `ttPretentiousSumChar_ge`),
split into `NarrowTwistSmall` (resonance range, essentially available) and `WideTwistSmall`
(new debt: needs cancellation in the twisted prime sum, i.e. a zero-free region for `L(s,χ)`).
Two sub-routes refuted in passing: the `‖T‖`-only form of the narrow bound is false (t = 0,
χ = 1), and the existing resonance certificate cannot reach `|t| ≤ X²` because of its
`log(2+|t|)` loss.  Chain: `faithfulArchLower_of_twist_small` → `FaithfulArchLower` →
`archSupply_of_faithfulArchLower` → `conjC3_of_geom_input_lower`.

## Lap 105 addendum — narrow range discharged at q = 1

`ttPretentiousSum_lower_of_uniformResonantMass` (extracted from the old vacuous corollary) gives
`ttExponent z · log log X − C₁ ≤ ttPretentiousSum`, and
`narrowTwistSmallTriv_of_uniformResonantMass` converts it into `NarrowTwistSmallTriv z
(ttExponent z) C`.  The narrow range therefore costs no new analysis; the two live debts are the
characters `q > 1` in the narrow range and `WideTwistSmall` in the wide one.

## Lap 106 addendum — principal characters reduced; a uniformity obligation surfaced

Narrow range status: `q = 1` proved (lap 105), principal `q > 1` proved
(`narrowTwist_principal_of_triv`, cost `log log q ≤ log log log X`, absorbed by halving κ),
non-principal `q > 1` named (`NonPrincipalTwistSmall`) and expected easier.  New obligation made
visible by the repair: `ArchSupply (TTNonPretentiousAt A) b` fixes ONE constant across all
primitive twists `h'`, so `FaithfulArchLower b C` needs `C` and `κ` uniform in `h'`.  Route:
`|arg (depthRoot b h' 0)| ≥ 2π/b` for `b ∤ h'`, so both depend on `b` alone.

## Lap 107 addendum — uniformity in `h'`, exponent side proved

`resEps_depthRoot_ge`: `|arg(depthRoot b h' 0)| ≥ 2π/b` for every `b ∤ h'`; hence
`ttExponent_depthRoot_ge : kappaDepth b ≤ ttExponent (depthRoot b h' 0)` with
`kappaDepth b = (1/10)·min(π/b,1/256)² > 0`.  Remaining: the constant side, a finite max over
the `b − 1` values of `h' mod b`.

## Re-verification at HEAD (2026-09-25, restatement-run re-audit)

The operator's restatement objective (a)-(c) was re-audited at `871797b` (i.e. after laps
103-117 rethreaded and then partly refuted the block route).  Result: **still intact and still
axiom-clean.**  `lake build` green (9443 jobs).  `#print axioms` gives exactly
`[propext, Classical.choice, Quot.sound]` for every item of the surface:

* (a) defects — `ttNonPretentious_trivial`, `ttNonPretentious_one`,
  `not_kPointNoExcWith_const_one`, `twoPointNaturalCorrelation_trivially_true`;
  `Maze.lean` aliases `hall_tt_nonpretentious_vacuous`, `hall_kpoint_noexc_false` (also clean).
* (b) restatements — `TTNonPretentiousAt` / `TTNonPretentiousUnif` (Dirichlet characters of
  conductor `≤ Q`, `|t| ≤ X`, constant `A` outside `X` and `L`), `TwoPointDyadicCorrelation`
  (exceptional set a `Finset` of dyadic scales with a *counting* cost), `KPointNoExcAtWith`.
  Non-vacuity guards, all kernel-checked: `not_ttNonPretentiousAt_one`,
  `not_ttNonPretentiousUnif_one`, `const_one_not_faithful`,
  `full_exceptional_set_not_admissible` + `exists_L_cost_lt_one`; bridge
  `ttNonPretentious_of_At`, `kPointNoExcAtWith_of_with`.
* (c) SURVIVORS table above — consumer verdicts unchanged; the two FREE-HYP rows
  (`ttNonPretentious_of_uniformResonantMass`, `ttNonPretentious_zOmegaNat`) remain the only
  genuine survivors on the supply side, and the archimedean gap they leave (characters `q > 1`,
  twists to `X²`) is exactly what DIRECTION.md's mandated next move attacks.

No restatement drift was introduced by laps 103-117: the later defect round (lap 115) hit the
*block* layer (`WideBlockSaving`/`WideBlockPartial`/`BlockPhasePairing`), not the TT interface.

### Scope note for the host / next lap

This run was launched with a **bounded** objective (the restatement items (a)-(c), explicitly
"do not advance the crux"), not repo-wide sorry-freeness.  That objective is met and re-audited
(`2fc0435`).  The repo-wide self-stop gate therefore correctly declines the stop: 15 open sorries
remain, all of them on the *crux* side this run was told not to touch.  A bounded run like this
should be launched with `--done-when 'sorry-free:<target>'`.

**Next lap should resume DIRECTION.md's mandated program**, not the restatement work: item ②.1
`blockBandCost_holds` for a parametric `J` (top blocks: primes `p > (⌈X²⌉₊+1)/2`, total mass
`≤ 2`; bottom blocks: `small_prime_mass_le` giving `log(J X · log 2) + mertensBound`), then ②.2
the kernel pin of the bottom threshold, then `CharPrimeSumLogQ D` at `t = 0`.
