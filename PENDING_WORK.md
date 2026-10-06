## Schmidt-games lane E1 (2026-10-04) — DONE
* `SchmidtGames.lean` sorry-free.  `potentialWinning_E`, `dimH_E₂_le`, `codim_E_asymp`:
  `#print axioms` = propext, Classical.choice, Quot.sound (wiring conditional only via the cited
  `Literature.BFS*` Props as hypotheses).
* Headline 1 via a stateless strategy `charge` (levels `ρ_k ≤ b^{-n} ≤ (1/β+1/ρ)ρ_k`, centres
  within 2), budget `tsum_charge_le`.  Headline 2 via `runFree` words, `card_runFree_le`
  (`≤ 2·(2−2^{1−m})^N`), `floor_mem_runFree`, `dimH_E₂_Ico_le`.
* Refereed 2026-10-04 (`docs/SCHMIDT-GAMES-REFEREE-2026-10-04.md`): `BFSPotentialDim` now takes
  `ρ ≤ 1`; the unrestricted form is refuted (`not_BFSPotentialDimUnrestricted`).
* Open: stretch `exists_computable_cantorPoint_mem_U_inter_Bad` (crux in `BarrierAudit.lean`).

## Barrier siblings lane (2026-10-04) — DONE
* `Barriers/Siblings.lean` sorry-free; (a)–(d) promoted to `.proved`.  `#print axioms` on each =
  propext, Classical.choice, Quot.sound.  See `HANDOFF-2026-10-04-barriers-siblings.md`.
* By-product: `Barriers.Siblings.LogNormalWitness.exists_isNormal` — a normal number in every base
  `b ≥ 2` (Borel via DEL, Lebesgue measure).  Candidate to move to a shared module if other lanes
  need base-`b` normal numbers for `3 ∣ b`.

## Bugeaud 10.36 lane (2026-10-04) — DONE
* `UniformBad.lean` sorry-free: `bugeaud_10_36` (uniform `‖bⁿξ‖ > b^{−24}`, all `b ≥ 2`, `n ≥ 0`),
  `#print axioms` = propext, Classical.choice, Quot.sound.  Leaves closed: `potential_step`
  (indicator tsums, `card_children_le`), `encard_stage_meet_le` (actually ≤ 6), `newPotential_le`
  (fiberwise by base + `tsum_base_weight_le` via `hasSum_zeta_two`, sum ≈ 0.023 < 1/40).
* Open: the true threshold for `c` lies in `[log₂ 3, 24]`.

## LevinSparse lane (2026-10-03) — headline + computable DONE
* `exists_levinRate_oddNormal` and `exists_computable_bld_odd_add`: `#print axioms` = propext,
  Classical.choice, Quot.sound (conditional only via hypotheses Levin1999, BLDLemma5).
* Only remaining sorry in LevinSparse.lean: `exists_absNormal_base2_fast` — a frozen OPEN PROBLEM
  (absolutely normal with base-2 discrepancy o(N^{-1/2}); ABSS 1707.02628 "barrier"; best known
  O(log^3 N / N^{1/2})).  Operator decision needed: convert to a `def … : Prop` conjecture node
  (LEAN-NEW-MATH table) or keep as open target.  Not attackable this run.

## BAD-normal (A) and reciprocal (B) lanes (2026-10-03) — DONE
* `ReciprocalNormal.lean` sorry-free.  `exists_computable_absNormal_recip_not_normal` (on
  `BakerBanajiQuarterCantor`) and `exists_computable_absNormal_recip_not_simplyNormal` (on
  `Literature.BakerBanajiSparse`, every `b ≥ 2`): `#print axioms` = propext, Classical.choice, Quot.sound.
  Sparse engine: `sdL`/`sYp` (prefix reader, `sYp_pre` via `floor_realOfDigits_mul_pow`), `Asp`/`PsiSp`;
  `y ≥ 1/2` read off the `k = 0` term of the floor sum.
* `BadNormal.lean` sorry-free.  `exists_computable_absNormal_bad` (on `SahlstenStevensBernoulli12`) and
  `cfCoin_const_false`: trust base only.  Mechanism: Möbius tail form `gcf` (`cfVal_append_real`,
  `gcf_mem_uIcc`), widths `≤ 2^{-D}` via `fib_mul_ge` (`F_{n+1}F_{n+2} ≥ 2^n`), Cauchy limit
  (`conv_tendsto`); digits via the shift identity `cfCoin_shift` and `1/3 ≤ cfCoin < 1` (no
  irrationality/cylinder argument needed).  `primrec_cfK` via a pair `foldr` (`cfK'`).
  CFCylinder: `bumpLast_*`, `cfK_bumpLast`, `cfVal_mem_Icc`, `add_cfVal`, `abs_cfVal_sub_bumpLast` made public.
* Open: only the cited Props (referee: `BakerBanajiSparse`, `SahlstenStevensBernoulli12`).

## Manai P/Q lane (2026-10-03) — DONE
* `ExplicitPQ.exists_computable_PQ` PROVED (from `BakerBanajiUniformQuarterCantor` only); `#print axioms`
  = propext, Classical.choice, Quot.sound.  `exists_PQ_of_analytic` likewise.  ExplicitPQ.lean has no sorry.
* The frozen leaf `approx_GPfam` was FALSE (`not_approxGPfamClaim`, kept with `ApproxGPfamClaim`); the
  theorem was deleted and the derandomization rerouted through the re-normalised family `GPfam2`
  (normaliser `M = (Σ|l_j|(u+2)^{|l|}+1)(|c|+1)(|l|+1)`, slope ≤ 1/2): `approx2_core`/`approx_GPfam2`,
  `decay_GPfam2`, `measurable_GPfam2`.  Supporting: `grid_bracket` (primrec monotone grid inverse of Q),
  `affFail_iff` (primrec test for P ∈ span(1,Q)), `exists_lst_eq`/`not_affineIn_lst`.
* `exists_computable_approx_xPQ` from the grid (`approx_xPQ_aux`, `computable_pre`).
* `GPfam`, `decay_GPfam`, `measurable_GPfam` remain proved but are now off the headline path.

## Bergelson-Downarowicz questions 2 and 4 (2026-10-03) — DONE
* `DeterministicBD.lean` sorry-free.  Item 4 (`not_productQuestion`, `not_ratioQuestion`,
  `not_recipProductQuestion`, `dimH_det*`, `volume_det*`) is UNCONDITIONAL, every base `b ≥ 2`:
  `#print axioms` = propext, Classical.choice, Quot.sound.
* Leaf (a) `deterministic_subexp_cover`: prefix count via `candSuffix` (F-block at good positions,
  digit elsewhere; `card_candSuffix_le`), bad-set count `card_smallSubsets_le`
  (`≤ (1+r)^N / r^k`, replaces the entropy/phase argument), `floor_eq_digVal`, `subexp_asymp`.
* Leaf (b) `dimH_prod_le_of_subexp`: `hausdorffMeasure_le_liminf_sum` with `b^{2εN}` squares.
* `isDeterministic_ratCast` (orbit takes ≤ den values, `S = ∅`), `isDeterministic_of_oneFreqZero`.
* Item 2 remains conditional on the cited `DetSub 2`, `DetSqNotDet` (by design).

## Manai Ω_k dimension lane (2026-10-03) — DONE
* PROVED `ExplicitOmegaK.dimH_Omega_eq_one` from `BakerBanajiAnalytic` alone; `#print axioms` =
  propext, Classical.choice, Quot.sound.
* New module `DigitCantor.lean`: `nu m` = law of `1/2 + z/2`, `z` base `m+2` with i.i.d. uniform
  digits in `{0..m}`; `nu_eq_sum_map` (self-similarity), `not_isNormal_yReal`, `sep_of_ne`
  (digit separation), `nu_le_of_ediam_lt` / `nu_le_mul_ediam_rpow` (Frostman, `C = 2b²`, any
  `d ≤ 1` with `b^d ≤ m+1`), `le_dimH_of_one_le_nu` (mass distribution via `le_hausdorffMeasure`).
* Wiring in ExplicitOmegaK: `isSelfSimilarOnWindow_nu`, `ae_digit_mem_Omega`, `lipschitzOnWith_pow`,
  `le_dimH_Omega`, `rpow_le_of_two_pow` (b = 2^L, d = (L−1)/L).
* Also PROVED: `bakerBanajiAnalyticQuarterCantor_of_general` (law of cantorReal is self-similar on the window).

## Manai Ω_k lane (2026-10-03) — Phase 1 + Phase 2 DONE
* `ExplicitOmegaK.Omega_nonempty` (needs only `BakerBanajiAnalyticQuarterCantor`) and
  `exists_computable_mem_Omega_two` (needs only `BakerBanajiQuarterCantor`): `#print axioms` =
  propext, Classical.choice, Quot.sound.
* Proved: `analyticOnNhd_Gk`, `exists_deriv2_Gk_ne_zero`, `deriv2_Gk_three_eq_zero` (inflection
  obstruction for k = 3), `bakerBanajiQuarterCantor_of_uniform` (helpers `OmegaKCalculus.lean`);
  `exists_computable_isAbsNormal_sqrt_of_polyDecay` via the new generic all-bases derandomization
  `ComputableNormalB.exists_computable_absNormal` (tests on a computable lower approximation +
  top-cell test; base-uniform decay constant from `VisitDeviationB`) instantiated in
  `SqrtCantorAbs.lean`.
* Phase 3 plan (explicit, so constants are computable from p):
  1. [DONE] `CantorSelfSimilar.pushFourier_self_similar` (one-step μ = ½ψ₁μ + ½ψ₀μ).
  2. [DONE] `CantorCylinders.pushFourier_cylinders` (depth m, φ_w t = offs w + t/4^m), `offs_sep`, `card_near_le` (≤ 4R·4^m+2 words with offset within R of z) — also covers step 4 counting.
  3. |Q(s)| ≥ |lead Q|·dist_ℂ(s, roots)^deg (complex roots; no root location needed);
     t²G_p'' = Q(t^{1/k}).
  4. bad words (cylinder within r of a root's real part): count ≤ deg·(24 r 4^m + 2).
  5. good words: BakerBanajiUniform on F∘ψ_w with explicit A₁,a₁,A₂,a₂ in (H(p), 4^{-m}, r).
  6. choose m, r as powers of |ξ| ⇒ ‖pF G_p ξ‖ ≤ K₀ (1+H)^e |ξ|^{-δ}, δ = δ(η,κ,k).
  7. family version of ComputableNormalB (admit p_i at level n when its computable bound ≤ n,
     N = n^20), dyadic lower approximation of G_p(y) (Nat k-th root via counting sum,
     interval evaluation of p), shift by an integer to make it ≥ 0.
* Open in the file: Phase 3 stretch `polyDecay_Gk`, `exists_computable_isAbsNormal_Gk` (next attack:
  extend `exists_computable_absNormal` to a countable family `G_i` with per-i constants `C_i`
  admitted at levels `n ≥ n(i)`; the hard part is computable constants for `polyDecay_Gk`), and the
  out-of-scope `dimH_Omega_eq_one`, `bakerBanajiAnalyticQuarterCantor_of_general`.

## TT dyadic bridge (2026-10-02) — DONE
* PROVED `CastingOut.ttEquidistributedDyadic_of_real : TTEquidistributedReal → TTEquidistributedDyadic`
  (axioms: propext, Classical.choice, Quot.sound).  Helpers in `TTDyadicBridge.lean`:
  `perturb_bound` (δ transfer via (3.1) at q=1 + boundary terms), `card_mul_le_integral` (parity-
  disjoint windows), `log_le_card_dyadicScales`, `dyadic_of_real_core` (c' = min c 1/4, η = L^{-2c'}).
* So `TTEquidistributedDyadic` is now a theorem from TT 3.1(i) verbatim.  Next (another lane's call):
  re-freeze the Erdős #257 headline on `TTEquidistributedReal`, as the referee recommended.

## Erdős #257 base 2 — lap 4 (2026-10-02)
* N7 PROVED: `SchedB.exists_scheduleWitnessSC_two_of_supplyEff` (G4Base2Sched.lean) — b=3 parameter
  layer + base-2 hM/hB/hbig/hfar/hbudget (`scheduleWitnessSC2`), (k₄,e) chosen under the moment cap.
* Finding: the ineffective supply (`∃ e₀`) cannot feed N7 — `HypE` caps e ≤ 2^{8K²}/(10⁵T).  Old
  sorry'd `exists_scheduleWitnessSC_two_of_supply` removed (unprovable shape); replaced by
  `SchedB.VeryLargeCovSupplyEff` (threshold A·(P₀(c₀+1)2^t)^A ≤ 2^e).
* PROVED: `binPair_cov_eff` (G4Base2GoodL.lean, explicit good-L threshold), and
  `veryLargeCovSupplyEff_of_TT` (Erdos257Base2.lean).  Erdos257Base2.lean has NO local sorry.
* Headline axioms still show sorryAx via the leaves: N5 `binInd_ap_mean` (G4Base2TTHyp),
  `exists_bins`, `abs_one_sub_binDelta_le`, `sum_inv_vlPrimes_le`, `avg_binErr_le` (G4Base2Supply).
  Next: these five, easiest first (exists_bins greedy, abs_one_sub_binDelta_le).

## Erdős #257 base 2 — lap 3 (2026-10-02, re-frozen on TTEquidistributedDyadic)

Headline + corollaries PROVED from: N7 `exists_scheduleWitnessSC_two_of_supply` (sorry) and the
N3–N6 supply `veryLargeCovSupply_of_TT` (PROVED from leaves).  `binPair_cov` (the TT step) PROVED.
**Open leaves (all on path):**
* N5 `binInd_ap_mean` (G4Base2TTHyp) — rough-number count; δ truncated to ∏T ≤ 2N.
* `exists_bins` (greedy), `abs_one_sub_binDelta_le`, `sum_inv_vlPrimes_le` (Mertens upper,
  mass of primes in (Y, Y^102] ≤ 5), `avg_binErr_le` (semiprime count) — G4Base2Supply.
* N7 base-2 schedule (Erdos257Base2.lean) — needs X = 2^x variable, V = 20000, κ ≤ 2^{-K/2}/(256K²);
  b≥3-only spots: gridB_bound, hN (clog), hfar, freqSeed.
Files: G4SubsetWitnessCov, G4Base2Cov, G4Base2Bins, G4Base2TTHyp, G4Base2Supply, G4Base2Blocks,
G4Base2Pair, G4Base2PairCov.

## Erdős #257 base 2 on prime subsets (launched 2026-10-02) — STOPPED lap 1: cited input vacuous

**Interface done:** `G4VeryLargeCov.lean` — `VeryLargeCov`, N1 `sum_sq_le_of_cov` /
`blockSum_sq_le_of_cov`, `bigAvgS_le_of_cov`, N2 `gridFrameW_subset_propD_of_cov` (PropD at any
`bb ≥ 2` from a covariance bound; axiom-clean).
**Route blocker (kernel):** `CastingOut.ttEquidistributedCorrelation_trivially_true`
(`LiteratureTTEquidistributedDefect.lean`; Maze row "TT 3.1(i) with a Lebesgue-measured
exceptional set", alias `hall_tt_equidistributed_vacuous`).  The frozen TT 3.1(i) Prop charges
`E ⊆ ℝ` by `∫_E t⁻¹` but asks the conclusion only at natural `N`, so `E = ℕ ∩ [√X,X]` is free —
the same defect as the 2026-09-25 case-(ii) row.  So N6 cannot be derived and the frozen headline
is, in effect, UNCONDITIONAL base-2 disjunctivity.  Per operator instruction, stopped.
**To resume (needs a human decision, frozen file):** re-freeze the headline on the repair
`CastingOut.TTEquidistributedDyadic` (counted dyadic scales), then N3–N6 as in the audit §4.
N7 notes from this lap: the b≥3 schedule (`G4SchedB*`, `Hyp.hb : 3 ≤ b`) needs a b=2 copy;
shifts/P₀ ≤ exp(logP₀Nat K) depend on K only, so `(log X)^c` beats them by taking the cutoff
exponent `e ≥ logP₀Nat K / c` (room under the cap 2^{8K²}); `hfar` at b=2 needs
`2^N ≥ K·2^{k₄}·A` (N = 100K², fine); `freqSeed 2 K` vs `freqSeed_le_quarter_pow` (3 ≤ b) is
unchecked.  With counted dyadic scales, the sample `[0,X)` still needs its dyadic block
endpoints `X/2^{j+1}` to be good scales: choose among the j's (fraction of bad scales small,
bad blocks bounded pointwise by A²) — that averaging is the N6 content.

## DONE (2026-09-29) — joint Lambert quantitative count

**Both ratified headlines are proved, with their full dependency chains, and are
`#print axioms`-clean** (`propext, Classical.choice, Quot.sound` only):

* `jointWords_quantitative` — for every finite `S` of bases `≥ 2` and fixed valid words,
  `A(N) ≥ N exp(-C (log log N)² log log log N)` for every `N ≥ N0`;
* `jointWords_power_count` — for every fixed `ε > 0`, eventually `A(N) ≥ N^(1-ε)`.

Permanent audit: `scripts/check-joint-lambert-count.sh` (frozen-source diff against
`e2828b32`, full build, exact ratified types, the `{2,4}` specialization, the boundary
controls, and transitive axiom verification of both headlines).

Four mathematical findings, recorded at the head of
`docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`: the far range needs no `τ(n) ≤ 2√n`; the split
point `J` is better chosen adaptively than as `⌊(log₂X)²⌋`; feasibility and rate need
*different* bounds on `log B`; and `B³ ≤ X` is exactly a factor two short of the window
comparison `H = o(M)`, repaired for free by running the schedule at pool exponent `4c+4`.

---

# PENDING WORK — the queue

## Current Lambert status, 29 September 2026

The bounded qualitative Lambert objective is complete: `f6fbf87` proves the original
common-position theorem unconditionally.  [Completed proof](docs/JOINT-LAMBERT-RESCALED-PROOF.md).
The [next quantitative target](docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md) has a paper derivation
of `N exp(-C (log log N)^2 log log log N)` occurrences for every sufficiently large N.
No new treadmill is launched by this documentation update.  The older AGP-only status
below is historical; proving AGP is not the next Lambert obligation.  Vandehey work is
separate, in the main checkout.


Concrete next moves, cheapest and most clear-cut first.  Front context is in `STATUS.md`.  The
lap-by-lap log from before the 2026-09-27 merge is `archive/PENDING_WORK-to-2026-09-27.md`.
Treadmill laps append dated notes **below the queue**, and a review lap folds them back into it.
## Erdős #257 for A = k·S (launched 2026-10-02) — CLOSED lap 1

All five frozen statements in `Erdos257.lean` PROVED; `#print axioms` = [propext,
Classical.choice, Quot.sound] for each.  New: `subsetLambert_two_pow_eq` (the Lambert identity
`c_S(2ᵏ) = Σ_{n∈k·S} 1/(2ⁿ−1)`, via `subsetLambert_eq_tsum_inv` + injective reindex `p ↦ kp`),
`isNormal_two_of_four` (base change 4 → 2 through Wall: odd orbit points are the doubling map of
the base-4 orbit, `visitCount_two_even`, then an even/odd squeeze).  Open debt is upstream only
(C′ hypotheses `SqrtFreshMassZero`, `DivergentRecip` are arguments).
## Master conjectures campaign (2026-10-02)

**Phase 1 DONE** (`MasterConjectures.lean`, axioms = trust base): `hypA_lnTwo`, `hypA_pi_base16`,
`borel_sqrt_two`.  Key new lemma: `not_irrational_of_hasFiniteAttractor_base` (B–C Thm 2.10 for
`x ↦ bx mod 1`, any `b ≥ 2`), plus `hasFiniteAttractor_perturb`; BBP surrogate `piP/piQ`
(eq. (3) numerator scaled by 16 so the orbit is exactly `piSurrogate`).
**Phases 2–3 DONE** (MasterConsequences / MasterKicked / MasterPiSq / MasterLnTwoBase3 / MasterMaze).
Open follow-ups (not campaign-blocking): `Irrational (π²)` in-repo (mathlib's Cartwright lemmas are
private; would make `hypA_piSq_base2` hypothesis-free); `catalan`/`ζ(3)`-type BBP formulas as more
machine instances; convert remaining legacy Maze rows in `mazeTestImplied` to links once their
obstructions are stated.

## ζ_Y campaign (launched 2026-10-02) — CLOSED lap 2

**Lap 2: `zetaY_isNormal` PROVED**, conditional only on the hypothesis argument
`VandeheyThm51`; `#print axioms` = [propext, Classical.choice, Quot.sound] for both headlines.
New: `weyl_scale`, `weyl_Rs` (`GrowingLocalizedLogScale.lean`, N9 complete);
`ePhase_orbit`, `orbit_sum_close`, `isNormal_xS` (`GrowingLocalizedLogNormal.lean`, N10).
The frozen statement is unchanged; only an import line and the proof body changed.
Remaining open debt for this route: discharging `VandeheyThm51` itself (side quest).

### lap 1 record

**Advance on crux N8:** Vandehey's Lemma 6.3 (the `Ĩ_k` table, constant `c`) is replaced by a
proved, constant-free window: `GrowingLocalizedLogExponent.lean`.  The invariant
`F_k = (ν_k − γ_k)(2^{k+1} − 1)` satisfies `F_{k+1} = F_k(1 − α_k) + 1` (`F_succ`), with
`k − 1 + (k+2)/2^k ≤ F_k ≤ k + 1` (`F_bounds`).  `exists_window`: every `y ≥ 1/4` has `k ≤ y + 2`
with `|F_k − y| ≤ 3/4`.  `exponents_le`: then both exponents are `≤ 1 − 2^{−k−4}`.
`vandehey_window_bound` (axiom-clean modulo the hypothesis `VandeheyThm51`): for `2 ≤ L`,
`log L ≤ 4 log m`, some `k ≤ log m/log L + 2` gives
`‖Σ_{n≤L} e(a bⁿ/m)‖ ≤ (A_k + B_k) L^{1−2^{−k−4}} (1 + log m)^{2^{−k}}`.
The saving `2^{−k−4}` (vs Vandehey's `2^{−k−3}`) costs a factor 2 in the saving, irrelevant.

**Lap 1b (cost side, done):** `GrowingLocalizedLogCost.lean` — `constPair_sum_le`:
`A_k + B_k ≤ 9·2^{3s+2}·Q·M·2^{(k+5)s}` for any prime set (crude Lemma 5.4; `cP_le`
`C_{P,x} ≤ (3/x)^s`).  N7 done: `bigM_two_le` (`GrowingLocalizedLogM.lean`, LTE), `M ≤ ∏_p 2^p·2Q`.  Remaining for N8: the assembly into
`korobov_uniform_saving`.

**Lap 1c:** `exists_unbounded_zetaY` PROVED (`GrowingLocalizedLogWitness.lean`).
N3–N5 PROVED generically (`GrowingLocalizedLogArith.lean`): for any index set `S` at a clean time
`n` (`CleanAt`: support `≤ Z`, `m < 2^{n−m}`), `Rs S n = Tnum/oddD` (`Rs_eq`), `3 ∤ Tnum`
(`three_not_dvd_Tnum`), and `den_bounds`: `den(aR_n) ∣ oddD` (odd, primes `≤ Z`, `≤ n^{π Z}`
by `oddD_le`), `3^{⌊log₃ n⌋} ≤ den(aR_n)·|a|`.

**Plan for the rest (`zetaY_isNormal`)** — fixed-length blocks, not runs:
* generic `S` (3-smooth ⊆ S, support ≤ Z monotone, π(Z n) ≤ (1−ε)log₂log n); instantiate Retained Y.
* DONE (Tail.lean): `two_pow_mul_xS_sub`, `Rs_shift`.  DONE (Count.lean): `card_smooth_le` (N1), `le_of_primeCounting` (Z ≤ 17(π Z+1)²).
* blocks of length `H ≈ N exp(−(log log N)^3)`; a block starting at `n₀ ≥ √N` is clean if no S in
  `[n₀ − B, n₀ + H)`, `B = log₂ N + 1`; unclean blocks ≤ 2·Ψ(N) + 1, Ψ ≤ (1+log₂N)^{π(Z N)}.
* DONE (Block.lean) `block_bound`. clean block sum = Vandehey sum with `m = den(hR_{n₀})`, `a = num`; `vandehey_window_bound` +
  `constPair_sum_le` + `bigM_two_le`; need `Y ≲ poly(π(Y))` via `Chebyshev.psi_ge`.

**(superseded) Next attack (rest of N8):** the cost side, Lemma 5.4 in closed form:
`log(A_k + B_k) ≤ s(k+1) log 2 + 2 log M + (3/2) log Q + log C_{P,1/2} + …` for `k ≤ s + O(1)`,
plus N7 `log M ≤ (log 2) Σ_{p≤Y}(p−1) + π(Y) log Y` (LTE).  Note the slack: with
`π(Y) ≤ (1−ε) log₂ log N`, any `k ≤ y + 2 ≤ s(1+o(1)) + 3` and any cost `exp(O(Y²))` suffices,
so a crude induction `A_k + B_k ≤ (2^{s+3} Q M C)^{?}` is enough; `C_{P,α_k}` needs
`∏ p^α/(p^α − 1) ≤ ∏ (1 + 1/(α log p))` (Lemma 4.2/5.3), the delicate factor.

## Vandehey §7 Problem 1 — CLOSED 2026-09-29 (laps 27–91) 🏁

Not solved.  The map of closed routes, with a kernel witness for each, is
**`docs/VANDEHEY-S7-FALSE-STARTS.md`**; every verdict is aliased in `src/NormalNumbers/Maze.lean`,
and `DIRECTION.md`'s "Completed runs" carries the three findings a future lap must not re-derive
(the crux is the headline plus locality; the scalar debts were artefacts of the one-digit-per-read
throttle; the wall is joint equidistribution of `(state, input point)`).  The lap-by-lap §7 record
is in the handoffs `HANDOFF-2026-09-29-lap*.md` and in `archive/PENDING_WORK-to-2026-09-27.md`.

(Historical §7 *lap notes* from laps 13–26 remain further down this file under "Lap notes"; the
lap-27-to-90 planning sections moved to `archive/PENDING_WORK-vandehey-s7-laps27-90.md`.)

**Do not re-open §7 without reading that doc.**  If a new idea survives it, the live formulations
to attack are `BlockForgetAll` (S7-AW, the whole architecture rests on it alone) and the
no-concentration statement of S7-GS.


## Joint Lambert update, 29 September 2026

The synchronized-word theorem is unconditional at proof commit `f6fbf87` on
`proof/joint-lambert-unconditional`, in the sibling checkout `normal-numbers-lambert`.
There are no remaining prime-distribution hypotheses on that theorem.
The old AGP target below is a separate analytic question, not a prerequisite.
The next Lambert target is an all-N occurrence count; its proposed stronger paper bound is
`N exp(-C (log log N)^2 log log log N)`, documented on that branch in
`docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`.  It is not yet formalized.


## ✅ LAP 7 (2026-09-28, bounded joint-Lambert objective): `PrimeIntervalSupply` IS A THEOREM

Scoped operator objective `DIRECTION.md` 2026-09-28 (c), ≤ 2 laps, **not** Vandehey assembly.
Vandehey's queue below is untouched and remains the main line.

`3ddc0b6` **`src/NormalNumbers/JointLambertPrimeInputs.lean`** — the joint Erdős–Borwein headline
now rests on `AGP` **alone**:

* `primeIntervalSupply_holds : PrimeIntervalSupply`, from **ordinary PNT** via the installed
  `Erdos446.eventually_dyadicPrimes_card_bounds` (itself from
  `BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent`).  Two bookkeeping steps:
  `dyadicPrimes_eq_filter_Ioo` (for `2 ≤ L` the endpoint `2L` is even and `> 2`, hence composite,
  so half-open `(L,2L]` = open `(L,2L)` as FINSETS) and the free `1/2 → 1/3` constant.
* `jointLambertDisjunctivity_of_agp`, `jointWords_two_four_of_agp`.

All three at the exact frozen types (compiler-pinned by the file's `Audit` section), axiom-clean,
every pre-existing `JointLambert*.lean` byte-identical to `7b17c44`.  Reproducible check:
`scripts/check-joint-lambert-inputs.sh`.

**`docs/JOINT-LAMBERT-AGP-GAP.md`** — the AGP gap map against the *installed* pins.  Findings:

1. Interval supply was never PNT-in-AP strength; the old `STATUS.md` row saying so is corrected.
2. Bombieri–Vinogradov is **only a `def`** in the installed `BoundedGaps`
   (`BombieriVinogradov/Statement.lean:66,76`; the sibling `Challenge.lean` has 3 `sorry`s).
3. `Erdos4.FGKMT.exists_exponential_prime_distribution` is genuinely stronger than BV in the error
   factor *and* has the AGP exceptional-set shape (one excised conductor, chosen before the
   modulus) — but it is an **absolute** error bound, `≤ C x e^{−c√log x}`, and AGP wants a
   **relative** lower bound whose main term `x/(φ(B) log x)` shrinks with `B`.  So it yields AGP
   only for `φ(B) ≲ e^{c√log x}`, not `B ≤ x^{1/4}`.  **Structural, not a constant loss**:
   improving the error factor to `x/(log x)^A` makes the admissible range *worse*.
4. The `D > log X` clause is a second, smaller gap: the `Erdos4` excision chain drops the Page
   witness, whose conductor bound `log Q < c·2^22·√m·(log m)^4`
   (`Erdos48.PageExceptionalWitness.log_scale_lt_quadraticGapDenom`) gives `m ≫ (log Q)^{2−ε}`.
   Re-threading it is adapter work.
5. `ElliottPrimeDensityAP.exists_primeDensityAP` is a theorem of the **wrong shape** (fixed finite
   modulus, reciprocal-prime mass) — not a lead.  No AGP-shaped declaration exists anywhere in
   `~/src/lean-proofs` or `~/src/FormalPantheon`, so there is no copy to mistake for progress.

**→ NEXT on this front (one target, fully quantified in §6 of the gap doc): `AGPExpRange`** —
`AGP` verbatim with the modulus range `X^{1/4}` cut to `exp(c√log X)` and `D0 = 1`.  Route: (★)
at a single modulus via `Finset.single_le_sum` off `exists_exponential_prime_distribution`,
`eventually_primeCounting_tenth_bounds` for the main term, and the Page-witness re-thread for
`log X < D`.  Proving it discharges the whole exceptional-set/choice-order architecture of `AGP`
against real analytic input and reduces the remaining gap to the single named implication
`AGPExpRange + (log-free zero-density: range extension) ⟹ AGP`.  That density estimate is the
substantial missing theorem and a multi-lap analytic campaign, deliberately out of scope here.

**Opened, same lap: `src/NormalNumbers/JointLambertAGPRange.lean`** — the named next target, now
decomposed in `src/` rather than only described in prose.  Proved and axiom-clean there:

* `AGPExpRange` (the def), faithful to `AGP` in every respect but the modulus range;
* `agpCount_eq_primeCountUpTo` — `AGP`'s prime count and `BoundedGaps.Maynard.primeCountUpTo`
  are literally the same filter, so the two libraries' encodings need no reconciliation;
* `mod_mem_coprimeResidues`, `progressionDiscrepancy_le_max`, `maxDisc_le_excisedPrimeSum`;
* **`exists_pointwise_exponential_distribution`** — the (★) of the gap doc: the installed
  `Erdos4.FGKMT.exists_exponential_prime_distribution` read at a SINGLE modulus, giving, for one
  excised conductor `B` and every `q ≤ x^{1/3}` coprime to it and every reduced `u`,
  `|π(x;q,u) − π(x)/φ(q)| ≤ C x e^{−(a/2)√log x}`.  This is the analytic content `AGPExpRange`
  needs, and it also confirms §2b of the gap doc in-kernel.

Two disclosed `sorry`s remain in that file, both named and both documented:

1. **`exceptionalModulus_gt_log`** — `AGP`'s `D > log X` clause.  **Route correction, same lap:**
   my first diagnosis (the `Erdos4` chain projects away `Erdos48`'s Page witness, so re-threading
   it is adapter work) was WRONG, and the real obstruction is worse.  Tracing the chain to its
   root, `Erdos4/FGKMTPrimeExcision.lean:8` excises `B := (χ.modulus).minFac` — the *smallest
   prime factor* of the exceptional conductor — with the exclusion stated as coprimality.  No
   lower bound on `B` is possible even in principle: `m` can be huge with `minFac m = 2`, giving
   `B = 2 ≤ log X` always.  A Landau–Siegel bound on `m` does not help because `m` is not what is
   excised.
   **The repair is proved sound in-kernel this lap:** `exists_modulus_excision_of_unique` and
   `exists_uniform_modulus_excision` excise `m` itself with `AGP`'s own **divisibility** exclusion
   `¬ D ∣ d`, which is also the mathematically correct one — a character mod `d` is induced by a
   primitive character of conductor dividing `d`, so an exceptional conductor `m` pollutes only
   *multiples* of `m`.  Coprimality-to-`minFac` is strictly cruder than needed.
   Cost, stated plainly: `¬ m ∣ d` does not imply `d.Coprime (minFac m)`, so the new excision
   cannot feed the existing chain.  Using it means re-deriving `exists_uniform_twisted_sum` …
   `exists_exponential_prime_distribution` with divisibility excision — five upstream theorems in
   a dependency this campaign does not modify.  **That is the honest size of this item**, and it
   is no longer describable as adapter work.
2. `agpExpRange_holds` — the quantitative assembly, blocked on (1) and on that re-derivation.  The
   arithmetic is written out in its docstring: (★) +
   `Erdos446.eventually_primeCounting_tenth_bounds` + `φ(q) ≤ q ≤ exp((a/4)√log x)` reduces it to
   `(5/2) C log x ≤ exp((a/4)√log x)`.

**Box gotcha (new).** The wide cold builds of `Util.Linnik.Theorem` / the `Erdos4`–`Erdos48`
analytic trees hit `EMFILE` ("too many open files", errno 24) persistently, and **`taskset -c 0-2`
did NOT fix it** here — contrary to the reference corpus's `taskset` remedy.  The failure also
surfaced inside **`lake` itself** reading `.trace` files, not only in `lean` workers.  Our own
`src/` build is unaffected (the pre-commit full `lake build` is green, 10352 jobs); only the
unimported analytic dependency trees are hard to bring up.  This is why §2b–§2d of the gap doc are
marked *stated-and-sourced* rather than in-kernel axiom-audited; `probes/AgpAudit.lean` is the
prepared audit, to be run once that tree converges.

---

## ✅ LAP 6 (2026-09-28): `hjs` IS CLOSED, and `hlen` is a corollary

`54610ea` **`VandeheyTransport.lean`** — the parity machinery of lap 5 transported back to the
genuine Raney transducer.  The bridge is `runState_lrDelta_eq`
(`runState lrDelta M.toRState w = ι^{|w|} (runState rplusDelta M w).toRState`), and the
determinant PINS the phase (`runState_lrDelta_eq_iff`), so
`jointSet lrDelta s₀ t q x n = jointSet (prodStep rplusDelta) (s₀,0) (tPlus t, tPhase t) q x n`
as FINSETS — an ext, not an estimate.  Hence `jointStateFreq_lrDelta` (= `hjs`) and
`subWindow_rhoLR` (= `hρ`), both `#print axioms`-clean.

**`VandeheyOutLen.lean`** — `hlen` reduced to `hjs`, as the lap-4 finding predicted and with no
cone perturbation: `outLen δ out s₀ x n = Σ_t wCount δ s₀ t (blockLen out t) 1 x n`
(`outLen_eq_sum_wCount`), so the length-1 engine `tendsto_wCount_div` gives
`tendsto_outLen_div` with limit `c = Σ_t wLimit ρ t (blockLen out t) 1`, needing only a uniform
block-length bound `hB`.

**ARCHITECTURAL FINDING (lap 6).**  The concrete `out` of `VandeheyLRTrigger` is `lrOutN`, which
emits `L/R` LETTERS.  Its `outLen` is therefore the LETTER count, and that diverges per input
digit (infinite Gauss digit mean — `VandeheyRunCount`'s own finding).  So `hB`/`hlen` can NEVER
hold for `lrOutN`, and the capstone must be driven by the RUN clock.
`VandeheyRunBirkhoff.lean` (lap 6) supplies that clock:

* augment the state with the last emitted letter, `lrB (M,b) j = (lrDelta M j, last (lrOut M j))`;
* `altOut (M,b) j = numAlt (b :: lrOut M j) ≤ 2D + 1` (Lemma 2.2, `altOut_le`);
* `numAlt_lrWord_eq_sum` : `numAlt (b₀ :: lrWord hD s₀ x n) = Σ_{i<n} altOut (stateAt lrB … i) (cfDigit x i)`.

That is exactly the `wCount` shape, with a BOUNDED weight.  So the run count has an
`x`-independent Cesàro limit as soon as `JointStateFreq` holds for `lrB`, and positivity comes
from `outLenLimit_pos`'s argument.

**LAP 6 CLOSED THAT TOO.**  `VandeheyTransportB.lean`: the involution acts on the augmented
state by `ι'(M,b) = (ι M, !b)` (`lrOut_swapState` + `getLast?_map_not`), so the whole phase
argument is verbatim; `rplusB_common_reach` is the length-3 reach (2 digits to `diag(1,D)`, one
more digit whose block `lrOut ⟨diag(1,D)⟩ j = Lᴰʲ` is nonempty, which overwrites the remembered
letter).  Hence `jointStateFreq_lrB`, `subWindow_rhoLRB`, and

> `tendsto_numAlt_lrWord_div` — **Vandehey's Lemma 6.1 for the TRUE clock**: the emitted RUN
> count has an `x`-independent Cesàro limit along every CF-normal orbit.

**POSITIVITY (`hc`) IS ALSO CLOSED (lap 6, `VandeheyFirstLetter.lean`).**  The probe found two
exceptionless structural facts, and both are now theorems:
`Mat2.det_pos_iff_branch` (for a balanced matrix `0 < det` iff the branch is `c < a ∧ b < d`)
and `head_lrOut_eq_true_iff` (**the first letter of a nonempty block is `L` iff `det M > 0`**).
Since `det` flips at every digit, consecutive nonempty blocks start with OPPOSITE letters, so
`one_le_altOut_add` : `altOut i + altOut (i+1) ≥ 1` — internally if the first block alternates,
at the SEAM otherwise (a constant block ends where it starts).  Blocks are nonempty for digits
`≥ D` (`lrOut_ne_nil_of_le`), so every position with 2-digit window `[D,D]` is charged, each
step at most twice: `winCard [D,D] x n ≤ 2 · numAlt(… (n+1))` (`winCard_le_two_mul_numAlt`),
hence `γ(I_[D,D]) ≤ 2c` and `zero_lt_runRate : 0 < c`.

**NEXT: the ASSEMBLY.**  Everything the capstone asks for now exists for the run clock except
the final wiring, and the wiring is where the remaining design question is:
`mobiusUniformFreq_of_transducer` is stated for a transducer whose `outLen` is `|outWord|`, i.e.
the LETTER count.  The run clock is not of that form — `out` would have to emit one ℕ per
COMPLETED run, and the value of a run is not a function of a finite state (the partial run
length is unbounded).  So the capstone needs a variant whose rescaling clock is supplied
SEPARATELY from the output word:
* keep `out := lrOutN` (letters) for `hkK`/`hK`/`hgen`/`htail`/`hout` — all already proved or
  near-free there, and the occurrence counting goes through `VandeheyLRPattern`'s
  `card_cf_eq_card_patWord` (CF occurrences ↔ `patWord` occurrences in the letter stream);
* replace `hlen` by the RUN clock `tendsto_numAlt_lrWord_div` + `zero_lt_runRate`, and feed
  `Rescale.tendsto_div_of_tendsto_comp_of_monotone` with the run count as `ℓ`.
That restatement of the capstone is the next lap's work; nothing analytic is left.

**What is left of the capstone**What is left of the capstone**What is left of the capstone**What is left of the capstone's hypothesis list** (`mobiusUniformFreq_of_transducer`):
1. `hc : 0 < c` — the ONE piece `tendsto_outLen_div` does not give.  `c ≥ 0` is
   `outLenLimit_nonneg`; strict positivity is combinatorial (some state/digit pair of positive
   Gauss mass emits a nonempty block).  Route: pick one genuine one-letter window `w` and a
   state `t` with `ρ [w] t > 0` and `out t w ≠ []`, and bound `wLimit` below by that single
   term (`le_csSup` with `Q = {[w]}`) — the `wLimit` sSup is over finite subfamilies, so a
   one-element `Q` suffices.
2. `hB` for the `L/R` machine (uniform block length) — expected from the same alternation count
   that gives `K = 2D + 2 + |v|` in `VandeheyLRTrigger`.
3. `hgen` (near-free, `patWord_alternation`), `htail` (a cylinder estimate), `hcof`.

## ⚠ THE LAP-5 ROUTE FINDING (2026-09-28) — the crux is an ALTERNATING PIN

Lap 5 first de-factorized the output side (commit `39b452f`: `JointStateFreq δ s₀ ρ`,
`SubWindow ρ`, `tailMass` without `ν`), which F2 below forced.  Then
`probes/raney_parity_split.py` (3.5M CF digits, `D = 3`) settled the shape of what is left, and
it is NOT what the lap-4 handoff predicted.

**Three numeric facts, one table.**
1. The **signed density is ZERO**: `(1/n) Σ_{i<n} (−1)^i 1[w_i = q] 1[P⁺_i = t] ≤ 0.003` for
   every state and every short `q` (vs. a signal size of `0.25`).  So `lrDelta`'s joint law is
   exactly **half** the phase-corrected one, `ρ(q,t) = ½ ρ⁺(q, ι^p t)`, `p` the phase of `t`.
2. The **phase-corrected law itself does NOT factorize**: the two states `(1,2,0,3)` and
   `(2,1,1,2)` (at `D = 3`) split a joint mass of exactly `¼·γ(I_q)` between them in a
   `q`-DEPENDENT way (`0.158/0.092` at `q=[1]` vs `0.138/0.112` at `q=[4]`).  So F2 is real, but
   it is **not a parity artifact** — it is non-factorization of `rplusDelta` itself.
3. That is **consistent with the kernel**: `VandeheyCocycle.ClassEquidistribution δ t q` binds its
   reference constant `L` **inside** the per-`q` statement, so `classEquidistribution_rplusDelta`
   never claimed a `q`-independent `ν`.  De-factorizing was exactly the right repair, and the
   kernel already supplies the de-factorized `ρ⁺(q,t) = L(q,t)·γ(I_q)`.

**So the remaining content of `hjs` is the PARITY SPLIT, and it is irreducible.**  Since
`stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)` and `det` pins the phase,
`1[stateAt lrDelta = t]` lives on ONE parity of `i`; the joint count is therefore the joint count
of the **product automaton** `δ* := rplusDelta × (ε ↦ ε+1)` on `RPlus D × ZMod 2` at the state
`(ι^p t, p)`.  Two dead ends, both checked this lap:
* the plain pin fails for `δ*` (its `n`-step kernel is `1[η+n=p]·(c + O(θⁿ))γ`, which oscillates),
  so `classEquidistribution_of_pin` does not apply — the period-2 wall reappears at the product;
* summing the signed identity over states gives `(1 − Σ_t c_t)·signedWin = o(n)`, i.e. `0 = o(n)`.
  The window-only parity balance `Σ_{i<n}(−1)^i 1[w_i=q] = o(n)` (the CF analogue of "normal to
  base `b` ⇒ normal to base `b²`") cannot be bootstrapped from the state statistics.

**THE ROUTE (identified lap 5, all inputs already in the kernel).**  Do not generalize the pin;
work with the product automaton's `devFun` written in the ORIGINAL automaton's events:

> `jointEvent δ* (d,η) (t,p) q k = if η + k = p then jointEvent δ d t q k else ∅`,
> hence `devFun δ* … k y = 1[η+k=p]·1[J_k] − L·1[W_k]`.

Write `σ_k := (−1)^{k+η−p} = ±1`, so `1[η+k=p] = (1+σ_k)/2`, and take the reference constant
`L := c/2` where `c` is the `rplusDelta` pin's constant.  Expanding
`∫ devFun*_k · devFun*_{k'}` against the FOUR existing estimates inside
`abs_integral_devFun_mul_le` (`hT1`–`hT4`: `|T1 − cγPJ| ≤ CθⁿγPJ`, `|T2 − γPJ| ≤ .79ⁿγPJ`,
`|T3 − cγPW| ≤ CθⁿγPW`, `|T4 − γPW| ≤ .79ⁿγPW`) the constant parts cancel EXACTLY at `L = c/2`
and what survives is

>  `mean part = (σ_{k'}/4)·( c·γ_q·PJ(k)·(1 + σ_k) − c²·γ_q·PW(k) ) =: σ_{k'}·R(k)`,  `|R| ≤ ½`.

`R` depends on `k` only.  So in the variance double sum
`∫ devAvg*² = K⁻² Σ_k Σ_{k'} ∫ devFun*_k devFun*_{k'}` the mean part contributes
`Σ_k R(k)·Σ_{k'∈[k+ℓ,K)} σ_{k'} = Σ_k R(k)·O(1) = O(K)` — **the alternating factor cancels over
the inner range**, which is exactly the cancellation the plain pin performed for free.  The rest
is the existing `Mρ^{gapExp}` majorant, also `O(K)`.  Hence `∫ devAvg*² = O(1/K)`, and from there
`classEquidistribution_of_pin`'s downstream half (`sum_gaussMeasure_windowBound_le`, the orbit
split, `tendsto_weighted_window_freq`) is **unchanged** and gives
`ClassEquidistribution δ* (ι^p t, p) q`, hence `hjs` for `lrDelta`.

**Work items, in order.**
1. Extract `hT1`–`hT4` out of `abs_integral_devFun_mul_le` as four named lemmas in
   `VandeheyTwoPoint.lean` (pure refactor; the existing proof then cites them).
2. `VandeheyParity.lean`: the product automaton (`prodStep`, `runState`/`stateAt` lemmas,
   `jointEvent_prod_eq`), the `devFun*` product identity, the two-point bound with the
   `σ_{k'}·R(k)` residue, and the alternating variance bound `∫ devAvg*² ≤ B/K`.
3. `classEquidistribution_prod` (re-run the `classEquidistribution_of_pin` endgame against the
   new variance bound), then `jointStateFreq_lrDelta`.
4. Only then `hlen` (corollary of `hjs`), `hgen`, `htail`.

## ⚠ TWO ROUTE-DECISIVE FINDINGS (2026-09-28 lap 4) — read before touching the supply side

### F1. The Raney automaton is PERIODIC: no uniform-length common reach, ever

`det (M · B j) = − det M`, so the determinant's sign is a **deterministic period-2 phase** on
`RState D`.  States of opposite phase are never simultaneously occupied, so no single target `z`
is reachable from EVERY state by words of one fixed length — and
`VandeheyTwo.classEquidistribution_of_common_reach` (whose hypothesis is exactly that) can never
be applied to `lrDelta`.  Equivalently `stateHorizonIntegral_pin_of_reach` is FALSE for a periodic
chain: the `n`-step kernel oscillates instead of converging.  Numeric: `probes/raney_reach.py`
(common targets exist for `D = 2,3,5,7,11,13`; no uniform length does).

**Repair, in the kernel as of lap 4** (`VandeheyRaneyReach.lean`, sorry-free):
* `Mat2.balanced_decomp_unique` — the Raney (L/R word, balanced matrix) factorization is UNIQUE.
  This pins the `Classical.choose`-defined `lrDelta`/`lrOut` for the first time
  (`VandeheyLR.lrStep_pin`), which is what makes any concrete computation with them possible.
* `Mat2.swapRows` (`ι M = J·M`) is an involution of the state set with `det (ι M) = −det M`,
  `lrDelta (ι M) j = ι (lrDelta M j)` (`lrDelta_swapState`) and
  `lrOut (ι M) j = (lrOut M j).map not` (`lrOut_swapState`) — an automaton isomorphism swapping
  the two phases, so the **phase-corrected** automaton `rplusDelta P a := ι (lrDelta P a)` on
  `RPlus D = {det = +D}` is a genuine finite automaton with `stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)`.
* The arithmetic core: `lrDelta M j = [[0,D],[1,0]] ↔ D ∣ a + b·j ∧ D ∣ c + d·j`
  (`lrDelta_eq_zMinus` / `dvd_of_lrDelta_eq_zMinus`), solvable over `ZMod D` for prime `D`
  because `D ∣ det M` makes the two congruences equivalent (`exists_digit_zMinus`); the one
  exceptional state is `diag(1,D)` (`eq_zPlus_of_dvd`), and it steps to `diag(D,1)` whatever the
  digit (`lrDelta_zPlus`), which then returns on the digit `D` (`lrDelta_zDiag`).
* **✅ LANDED (lap 4).**  `RPlus D` (a `Fintype`), `rplusDelta`, and `rplus_common_reach` —
  every `P ∈ RPlus D` reaches `diag(1,D)` in EXACTLY 2 genuine digits (one step off the
  exceptional state, one step home).  Hence **`classEquidistribution_rplusDelta`**: the crux
  input of Theorem 1.1, `VandeheyCocycle.ClassEquidistribution (rplusDelta hD) t q`, is PROVED
  for every prime `D` and every genuine window `q`, and `tendsto_jointCount_rplusDelta` turns it
  into the `x`-independent joint frequency.  All axiom-clean (trust triple).

### F2. `JointStateFreq`'s PRODUCT form is FALSE for the concrete machine

`VandeheyOut.mobiusUniformFreq_of_transducer` assumes
`jointCount(t,q,x,n)/n → ν t · γ(I_q)` with a **single** `ν` independent of `q`.  That shape was
adopted on lap 1 because it makes countable additivity of the output limit free.  It is not
available: `probes/raney_joint_product.py` measures `ρ(q,t)/γ(I_q)` over 2.1M Gauss-distributed CF
digits and finds, for `D = 3`, four states whose ratio moves by up to **20 %** across
`q ∈ {[1],[2],[3],[4],[1,1],[1,2],[2,1]}` — a ~15σ effect (the other ten states are flat to 0.3 %).
For `D = 2` it DOES factorize, and the reason is visible: there the stationary law is uniform
(`1/6` on each reachable state) and a uniform law is invariant under every individual digit's
action, so the state decouples from the adjacent window.  The Raney digit steps are **not**
injective, the `D = 3` stationary law is `(0.125 ×6, 0.073 ×2, 0.052 ×2)`, and the state at `i` is
genuinely correlated with the digits just before `i` — which abut the window at `i`.

**Consequence.**  The capstone must be restated with a general
`ρ : List ℕ → S → ℝ`, i.e. Vandehey's own un-factorized `ρ ≪≫ μ̃`.  **The factorization is not
needed:** the reason it was adopted — controlling the escape mass of the countably infinite
alphabet — is recovered for free from the pointwise bound

> `ρ(w,t) ≤ γ(I_w)`  (because `jointCount ≤ winCard` at every `n`),

so `Σ_{w ∉ F} ρ(w,t) ≤ 1 − Σ_{w ∈ F} γ(I_w)`, and `exists_boundedWords_sum_gt` (already proved)
supplies an `F` with `Σ_F γ(I_w) > 1 − ε`.  Every `ν t * γ(I_w)` in `VandeheyOutputFreq.lean`
becomes `ρ w t`, and `wLimit` becomes a sup over finite subfamilies of `Σ_{w∈F} a w * ρ w t`.

**Next, in order.**
(i) ~~Finish `rplus_common_reach`~~ — DONE (lap 4).
(ii) Generalize `JointStateFreq` → `JointStateFreq'` with `ρ`, and port `VandeheyOutputFreq.lean`
     (~1100 lines, mechanical: the only real change is the escape bound above).
(iii) Restate `mobiusUniformFreq_of_transducer` against `ρ`.
(iv) Then `hjs` is `ClassEquidistribution (rplusDelta hD) t q` for each `q` — which
     `classEquidistribution_of_common_reach` delivers from (i) — plus the **parity split**:
     `jointCount lrDelta` is supported on one parity of `i`, so it is
     `½(jointCount rplusDelta ± Σ_i (−1)^i …)`, and the signed half is FREE from the existing
     two-point machinery (`abs_integral_devFun_mul_le` bounds an ABSOLUTE value, so inserting
     `(−1)^k` changes nothing in `integral_devAvg_sq_le`).
(v) `hlen` is then a COROLLARY, not an analytic leaf: Vandehey's own §6 proof writes `ℓ(n)` as a
    Birkhoff sum of a BOUNDED window/state function (augment the state with the last emitted
    letter, so the seam term is local), which the `wCount`/`wLimit` machinery evaluates.

## 0′. `hK`/`hkK` — **CLOSED** for the `L/R` transducer (2026-09-28 lap 3)

`lr_trigger_bounds` (`VandeheyLRTrigger.lean`) supplies both trigger hypotheses of
`mobiusUniformFreq_of_transducer` for the concrete machine, with `K = 2D + 2 + |v|`, for every
target word `v` that ALTERNATES somewhere (`v[i₀]? ≠ v[i₀+1]?`).  The chain, all axiom-clean:

1. `VandeheyRunBound.numAlt_lrOut_le_two_mul` — Vandehey Lemma 2.2 in run form: one ingested
   digit emits at most `2D` alternations, with NO dependence on the digit.  Proof: the `j`-free
   column identity `(M.b, M.d) = lrProd w ·ᵛ (M'.a, M'.c)` plus the observation that each letter
   ADDS one coordinate to the other, so the coordinate sum bounds the alternation count; a
   vanishing coordinate persists under only one letter, i.e. the rest of `w` is a single run.
   **No case split on vanishing denominators** — Vandehey's Cases 1–3 disappear.
2. `VandeheyAltCount.occIn_le_numAlt_add` — abstract: occurrences of an alternating `v` starting
   in the first emitted block are `≤ numAlt (block) + 2 + |v|`, with no reference to block LENGTH.
3. `VandeheyAltCount.trigger_bounds_of_occIn_le` — `hK` and `hkK` ARE one statement (`kOut` is an
   increment of `occIn`; the `hK` sum telescopes along CF prefixes).

**The translation is CLOSED (lap 3, later).**  `VandeheyLRPattern.lean`:
`map_range'_eq_patWord` (CF digits match ⇒ the stream reads the forced pattern),
`cfDigit_of_map_range'_eq_patBody` (converse), and `card_cf_eq_card_patWord` (a BIJECTION
`n ↦ lrPos w n - 1` between CF occurrences in `[1,N)` of parity `b` and pattern occurrences).
The dictionary itself is `VandeheyLRRuns.lean`: `lrTail_lrPos` (after `n` runs the point is `Tⁿw`
or `(Tⁿw)⁻¹`), `lrExpand_eq_runIdx_parity`, `lrExpand_ne_succ_iff`.

**⚠ STRUCTURAL FINDING (lap 3) — rescale by RUNS, never by LETTERS.**  The Gauss measure has
infinite digit mean, so `lrPos w n / n → ∞` a.e.: the *letter* count per input digit DIVERGES and
the density of run boundaries in the L/R word is `0`.  Any plan that rescales the L/R-letter index
against the input index by a positive constant is WRONG.  What is linear is the RUN count, which
is why Lemma 6.1 is about emitted CF digits.  The bijection above is the right interface precisely
because it lands on CF INDICES, not letter positions.  Upper half now proved:
`VandeheyRunCount.numAlt_lrWord_le` — at most `(2D+1)·n` alternations after `n` input digits
(Lemma 2.2 summed over blocks, one alternation per seam).

**Next, in order.**
(a′) **`hlen`, the remaining analytic leaf**: the run count grows at least LINEARLY,
    `runs(lrWord n)/n → c > 0`.  Route: `lrRun_eq` says `M₀·B_{a₁}⋯B_{aₙ} = lrProd w · M_n` with
    `M_n` in a FINITE set, and the input product's own Stern–Brocot word has exactly `n` runs
    (one per input digit); right-multiplying by a bounded matrix perturbs the path's cone by a
    bounded amount, so the two run counts differ by a bounded FACTOR.  Making "perturbs the cone
    boundedly" precise is the work.  A cheaper sufficient form may be available: the frequency
    argument only needs `liminf runs/n > 0`.
(b′) Then factor the assembly (see (b) below) and assemble.

(a) The run↔CF-digit translation (HANDOFF NEXT 2), superseded above.  An occurrence of a CF word `v` in the image's
    expansion is an occurrence of the single `L/R` word `w_v = X · R^{v₁}L^{v₂}⋯ · Y` with the two
    boundary letters FORCED by alternation (maximal runs at both ends = a one-letter look-around).
    `w_v` alternates, so (a) is exactly what supplies the `i₀` that `lr_trigger_bounds` needs.
(b) Because the assembly's `hout` demands `out` emit the image's CF digits and the `L/R` machine
    emits letters, `mobiusUniformFreq_of_transducer` must be FACTORED: an `OutputWordFreq`
    conclusion (every output word has an `x`-independent Cesàro frequency, `K` allowed to depend
    on `v`) plus a separate CF-digit bridge through (a) and a second `VandeheyRescale` at the
    density of run boundaries.  Note `hK`/`hkK` are FALSE at the `L/R` level for constant `v`
    (`v = LL` occurs ~`j` times in a block), which is precisely why the bridge, not a direct
    instantiation, is the right architecture.

## Queue

New math comes first.  Trusted literature inputs (`AGP`, `CharPrimeSumLogQ`,
`ZetaLogDerivExponent`) stay as hypotheses and are not queue items until a new result
needs one discharged (DIRECTION standing rule 3).

*(Both former queue items were cleared on 2026-09-29, lap 1 of the §7 objective.)*

1. ✅ **SwingC2 triage — done.**  `tauMomentPrimesShiftStruct_of_primeDensity`,
   `survivorLeaf_of_struct` and `TauMomentPrimesShiftStruct` are **deleted** (no consumer
   anywhere in the repo).  `PrimeDensityAP` survives as a record of the intended AP input, with
   the 2026-09-25 review's vacuity defect **repaired** by the extra clause `M ≤ Y`; the repair is
   load-bearing and proved so in the kernel by `SwingC2.primeDensityAP_pos` (the repaired
   statement forces a prime to exist in the stated range; the old one did not).  The live open
   obligation on the headline path is unchanged: `shiftedDivisorIncidence_holds`.

2. ✅ **OVERVIEW refresh — done.**  `OVERVIEW.md` + the pandoc-built `OVERVIEW.html` (hand-patched;
   it carries custom CSS, so do NOT regenerate it wholesale from the Markdown).  Vandehey Thm 1.1
   now stated as PROVED, with the §3-free route described and §7 Problem 1 named as the live
   target; joint Lambert corrected to one remaining input (`AGP`).

3. 💤 **Parked, not for the current objective: normality's "master conjectures"** (Borel's conjecture and the general Bailey–Crandall Hypothesis A as hypothesis Props with their consequences, plus a Maze test of which rows they reopen).  Trevor, 2026-09-29.  Pick it up when §7 settles or a lap needs a new objective → `docs/proposal-normality-master-conjectures-2026-09-29.md`.

## Lap notes

### 2026-09-29 lap 26 — the emitted digit is a function of the STATE alone (`VandeheyS7Emit.lean`)

    cfDigit_mob_eq_emitDigit :  0 < s.b → CanEmit s → y ∈ [0,1] → cfDigit (s.mob y) 0 = emitDigit s

**That is the whole point of the lap.**  The emitted digit does not depend on the unread future
of the input.  Since the state after reading a window is `s₀ · wordState w` (`runWord_eq_comp`)
and merging makes `s₀` invisible (`spread_runWord_le`), the digit is a function of the WINDOW —
which is exactly what `cfCount_tendsto_of_decomposition` (lap 22) takes as its hypothesis.

Supporting, all axiom-clean:

* `mob_mem_uIcc` : a state maps `[0,1]` — the range of every possible continuation — into the
  interval between `s.mob 0` and `s.mob 1`.  The sign of `det` decides the orientation and
  `uIcc` absorbs it, so NO hypothesis on `det` is needed.  (The two exact identities
  `mob y − mob 0 = y·D/(d(cy+d))` and `mob 1 − mob y = (1−y)·D/((c+d)(cy+d))` carry it.)
* `cfDigit_zero_antitone` / `cfDigit_zero_eq_of_between` : `⌊1/·⌋` is antitone, so a digit that
  agrees at the endpoints is constant across the interval.
* `CanEmit s := cfDigit (s.mob 0) 0 = cfDigit (s.mob 1) 0`, with `emitDigit` the common value.

`0 < s.b` is load-bearing and not cosmetic: `phiState` has `b = 0`, where `mob 0 = 0` and the
digit is the junk value.  It is the same side condition the repo's `emit` already carries.

Degenerate case `not_canEmit_of_ne`: when the endpoints disagree, no digit is determined and the
machine must read more input — which is precisely the `boundaryBad` situation of
`VandeheyS7Boundary`.  **That is why that set had to be measured**, and the two modules now meet.

**Next attack (lap 27): the window function `F` itself.**  Define `F w := emitDigit (wordState w)`
(or `emitDigit (s₀.comp (wordState w))` and then quotient out `s₀` by merging).  The statement to
prove: for a.e. input and all large windows, the image digit at the corresponding position equals
`F` of the window.  The `CanEmit` hypothesis is discharged off `boundaryBad` by
`cfDigit_agree_depth`; the `s₀`-independence is `spread_runWord_le`.  Both are in hand, so this
is a matter of lining up the indices — the clock `ℓ` is what relates input position to image
position, and it is `VandeheyS7Clock`'s FIRST named hypothesis, believed fine and measured.

### 2026-09-29 lap 25 — the window lemma is UNCONDITIONAL along the run

**A route correction first, recorded so it is not retried.**  Lap 24's stated next step — get the
general `TriggerGap` by composing with the initial state on the LEFT — is WRONG.  `s₀(cylFar w)`
need not lie between near and far, so left-composition does not preserve the trigger.  The
correct general statement is the operational one.

* `abs_sub_beta_mem` : distance to `β` is monotone across the cylinder.  `conv_far_eq` gives
  `far − β = k(near − β)` with `1 ≤ k ≤ 2`, so the two have the SAME sign — `β` lies outside
  `[near, far]` (it is the parent cylinder's other endpoint, with `near` the separating mediant)
  and `near` is the closer.  Hence every `x` between them has `|near−β| ≤ |x−β| ≤ |far−β|`.
* `triggerGap_of_mem_cyl` : both image endpoints in `w`'s cylinder — exactly when the machine
  emits `w` — gives `TriggerGap`.  This is the general case, not the extremal one.
* `windowBound_runWord` : **post-burst distortion ≤ 4 along the machine's run, from ANY initial
  state, with no trigger hypothesis and no distortion hypothesis.**  Reading gives
  `distortion ≤ 2` for free (`distortion_runWord_le_two`) and emission gives the trigger.  Only
  the nondegeneracy side conditions (`hQ`, `hden0`, `hden1`) remain, and those are
  non-vanishing-denominator conditions, not estimates.

All axiom-clean.  The window lemma was "done as mathematics" per the 2026-09-29 handoff; it is
now done as a theorem about the machine.

**Next attack (lap 26): obligation 1 of lap 22 — define `F`.**  Nothing structural is in the way
any more.  The pieces: `runWord_eq_comp` (state = initial · word), `windowBound_runWord` (bounded
distortion along the run), `cfDigit_agree_depth` + `budget_le` (a window of input determines a
proportional number of image digits).  What to build: a definition of the emitted-digit function
`F : List ℕ → ℕ` from the machine's state, and the statement that the image digit at position `j`
equals `F` of the input window.  Start by writing down the machine as an explicit corecursion
(state + emission) rather than leaving it implicit in `runWord`/`emit`; the emission side
condition of `emit` (`e·a ≤ c`, `e·b ≤ d`) is what picks `e`, so `F` should be defined as the
largest such `e`, and then `mob_emit` says it does the right thing.

### 2026-09-29 lap 24 — `TriggerGap` is achieved, unconditionally, on the word matrix

`triggerGap_wordState : TriggerGap (wordState w) w` for any nonempty word with genuine digits —
no side conditions at all.  Axiom-clean.  This removes `windowBound`'s trigger hypothesis in the
extremal case, via two endpoint identities that `wordState_eq_conv` (lap 23) makes immediate:

    (wordState w).mob 0 = b/d       = p/q         = cylFar w
    (wordState w).mob 1 = (a+b)/(c+d) = (p+p')/(q+q') = cylNear w

**They come out SWAPPED** relative to `triggerGap_endpoints`' phrasing: the word matrix reads `0`
to the FAR endpoint and `1` to the near one.  Hence `triggerGap_endpoints_swap`.  `TriggerGap` is
symmetric in what it demands (both images between near and far), so the same argument serves —
but the swap is worth recording, since assuming the original orientation would silently produce a
false endpoint identity.

Scope, stated honestly: this is the EXTREMAL case, `s = wordState w`, not the general machine
state.  The machine's accumulated state is `s₀ · wordState w` (lap 13's `runWord_eq_comp`), and
what this pins is the endpoint of the range the general statement must cover.

**Next attack (lap 25): `TriggerGap` for `s₀ · wordState w`.**  The general statement is that
composing with the initial state on the LEFT keeps both images between near and far.  That should
follow from monotonicity of `s₀.mob` on `(0,∞)` — the same fact that gave `mob_ratio_le` /
`mob_ratio_ge` in lap 12 — since `s₀` maps the interval `[cylFar, cylNear]` into an interval with
the same ordering.  If it goes through, `windowBound` becomes unconditional along the whole run,
and obligation 1 of lap 22 (defining `F`) is unblocked.

### 2026-09-29 lap 23 — the word matrix IS the continuant matrix (transposed)

The handoff's queued bookkeeping is done, and it landed on lap 13's `wordState`:

    wordState_eq_conv :  wordState w  =  (p', p ; q', q)   for  Conv.of w = ⟨p', q', p, q⟩

(all digits `≥ 1`), axiom-clean.  Supporting: `idState_comp`, `wordState_append` (appending a
digit multiplies on the right).

**The transpose is the content, not a convention slip.**  The word matrix is built by PREPENDING
branches — which is what the machine does as it reads input — while `Conv` is built by APPENDING
digits, which is what the continuant recursion does.  Those two are transpose-conjugate.  Both
recursions were checked against each other: appending sends `(a,b;c,d) ↦ (b, a+e·b ; d, c+e·d)`
on the word matrix and `(p',q',p,q) ↦ (p, q, p'+e·p, q'+e·q)` on `Conv`, which agree under the
transpose, and the base cases agree (`idState = (1,0;0,1)`, `Conv.of [] = ⟨1,0,0,1⟩`).

**Consequence worth recording:** lap 13's Fibonacci growth of the word matrix's ROWS is literally
the classical growth of the convergent denominators `q_n`.  Two separately-derived facts are now
known to be one fact, and `windowBound`'s `Conv`-language hypotheses (`(of w).p'`, `(of w).q'`)
can be discharged from `wordState` facts and vice versa.

**Next attack (lap 24): `TriggerGap` from the machine.**  `windowBound` takes `TriggerGap s w` as
a hypothesis and `triggerGap_endpoints` proves it when `s.mob 0 = cylNear w` and
`s.mob 1 = cylFar w`.  With `wordState_eq_conv` in hand those two endpoint identities are now
statements about `wordState`, so prove them there.  That turns `windowBound` from conditional
into unconditional along the machine's run, which is the last structural gap before `F` can be
defined (obligation 1 of lap 22).

### 2026-09-29 lap 22 — the Cesàro engine, and the remaining obligation isolated to ONE hypothesis

`VandeheyS7Assemble.lean`, both theorems axiom-clean.

* `cfFreq_finset_sum` : a FINITE family of input words has a joint occurrence frequency, namely
  `∑ γ(I_u)`.  Finite additivity on top of CF-normality — the engine that turns "the image digit
  is a window function of the input" into an image frequency.
* `cfCount_tendsto_of_decomposition` : if the image's count of `v` agrees with the total count of
  a finite family `S` of input words **up to a bounded error**, then
  `cfCount v z p / p → ∑_{u∈S} γ(I_u)`.  The limit depends only on `S`, hence only on the window
  function and `v` — **NOT on `x`.  That is precisely the `x`-independence `SampledUniformCount`
  asks for.**

The bounded-error form is the right one: edge effects of a fixed-length window are `O(1)` in `p`,
not `o(p)` in disguise, so nothing is being smuggled.

**Where the route now stands.**  Everything analytic is proved; the whole remaining gap is the
single hypothesis `hdecomp` — identifying `S` from `cfDigit_agree_depth`.  Two sub-obligations:

1. **The window function.**  Show the image digit at position `j` is a fixed function of a
   fixed-length window of the input digits.  All the ingredients exist
   (`cfDigit_agree_depth` + `budget_le` + the two measure bounds); what is missing is the
   *definition* of `F` and the statement that the machine's emission is what `runWord` computes
   (the handoff's "remaining bookkeeping on the window lemma": `TriggerGap`, and identifying the
   pullback matrix's first column with `Conv.of`'s `(p', q')`).
2. **Finiteness of `S`.**  `S` is finite only after the digit cutoff `K`; uncapped it is
   countably infinite and the limit/sum exchange needs the repo's existing summability inputs
   (`CFAeKhinchin.summable_logMul_vol_cfCylinder`, `summable_sqLog_gaussMeasure_cfCylinder`).

**Next attack (lap 23): obligation 1, starting with the emission bookkeeping.**  It is the older
of the two and was already queued in the 2026-09-29 handoff.  Concretely: turn the φ-machine's
operational emission trigger into `TriggerGap`, and prove `A_e = (0 1; 1 e)` matches
`Conv.of [e] = ⟨0,1,1,e⟩` (hand-checked already; the recursions agree).  That makes
`BddDistortion` / `EmitRowBound` theorems rather than hypotheses, and it is what lets `F` be
defined at all.

### 2026-09-29 lap 21 — THE ROUTE IS NOT BUDGET-LIMITED (`VandeheyS7Budget.lean`)

The question this lap had to settle: `cfDigit_agree_depth` needs `δ_L · scale u m` small, where
merging gives `δ_L ~ φ^{-2L}` and the cutoff costs `S^m`.  Can `m` be taken PROPORTIONAL to `L`?

**Yes, with an explicit constant, and the constant is positive for every finite cutoff `K`.**

* `goldenRatio_pow_le_fib` : `φ^k ≤ fib (k+2)`, a two-step induction off `φ² = φ + 1` — the same
  recursion as `fib`, which is why it is exact rather than an estimate.
* `fib_prod_ge` : `φ^{2k} ≤ fib(k+2)·fib(k+3)`, i.e. `δ_{k+3} ≤ φ^{-2k}`.
* `budget_le` : `S^m · δ_L ≤ exp(m log S − 2k log φ)` for `L = k+3`.
* `budget_tendsto_zero` : for any `c < 2 log φ / log S`, the product along `m = ⌊ck⌋` decays
  geometrically.
* `not_budget_of_large` (degenerate case): past that threshold the exponent is positive and the
  bound says nothing, so `2 log φ / log S` is sharp.

All axiom-clean.  **Why this matters for the route, not just the bookkeeping:** raising `K` to
shrink the exceptional mass raises `S = 4(K+1)²e^{2η}` and so shrinks `c` — but only
logarithmically, and never to zero.  So the two limits can be taken in the order `K` first, then
`L → ∞`, and there is no circularity.  A positive proportion of the image digits is determined
by a bounded window of input digits.  That was the last thing that could have killed Route A on
arithmetic grounds.

**Next attack (lap 22): assembly into `SampledUniformCount`.**  Every analytic input now exists.
What remains is bookkeeping of a kind the repo already does elsewhere: the determined image
digits give block counts that depend only on the input window, so their Cesàro averages converge
by the input's CF-normality (frequency EXISTENCE only — no value, per
`affineCFN_of_uniformFreq`).  Concretely: state the "window-determined block count" Prop, prove
it from `cfDigit_agree_depth` + `budget_le` + the two measure bounds, and then reduce
`SampledUniformCount` to it.  Expect this to be several laps; it is assembly, not new
mathematics, and the guard rule applies to each new Prop.

### 2026-09-29 lap 20 — the scale cutoff is closed, reusing the repo's Khinchin machinery

The lap-19 gap (`gaussMeasure_exceptional_le` is at a FIXED scale, but `cfDigit_agree_depth`
needs `ε = δ · scale u i`) is now closed.  The instrument was already in the repo:
`CFLogTail.logTailFn K` (log of the digit when it exceeds `K`, else `0`) with the Markov bound
`gaussMeasure_logBadZone_raw_le`, whose `n`'s cancel.  Three new theorems, all axiom-clean:

* `log_digit_succ_le` : `log(a+1) ≤ log(K+1) + log 2 + logTailFn K x`, pointwise.  True in both
  regimes — for `a ≤ K` the tail term is `0`, for `a > K` it is `log a` and `log(a+1) ≤ log(2a)`.
* `log_scale_le` : summing along the orbit,
  `log (scale u n) ≤ 2n(log(K+1) + log 2) + 2·logBirkhoffSum K n u`.
  (`cfDigit u j = cfDigit (gaussMap^[j] u) 0` is `rfl`, so the Birkhoff sum matches on the nose.)
* `scale_le_exp` / `gaussMeasure_scale_bad_le` : off the log-tail bad zone `scale u n ≤ S^n` with
  `S = 4(K+1)²e^{2η}`, and that bad zone has mass `≤ (∫ logTailFn K dγ)/η` UNIFORMLY in `n`.
  `integral_logTailFn_tendsto_zero` sends it to `0` as `K → ∞`.

**Confirmed: one integral underwrites both named hypotheses.**  `∫ log(1+a) dγ < ∞` is what
`VandeheyS7Clock` cites for the clock rate AND what pays for the scale cutoff here.  That is a
structural fact about the route, not a coincidence — record it before it gets re-derived.

The transfer chain is now complete except for assembly:

    spread_runWord_le → abs_sub_runWord_le → cfDigit_agree_depth
      exceptional set:  gaussMeasure_exceptional_le  (fixed scale)
      scale cutoff:     gaussMeasure_scale_bad_le    (removes the u-dependence)

**Next attack (lap 21): assemble, and state the残 gap honestly.**  Combine the two measure
bounds into a single "for a.e. `u`, for all large `n`, the first `m(n)` digits of the image are
determined by the last `n` input digits" statement, choosing `m(n)` so that
`δ_n · S^{m(n)} → 0` — merging's `δ_n = 1/(fib(n-1)fib(n))` is exponentially small with rate
`φ²`, so `m(n) = c·n` works for `c < 2 log φ / log S`.  THEN the remaining step to
`SampledUniformCount` is the Cesàro/ergodic bookkeeping: digit-block frequencies along the clock.
Do the `m(n)` arithmetic first — it is pure inequality work and it pins the constant `c`, which
is the quantity that decides whether the route closes.

### 2026-09-29 lap 19 — the exceptional set has small Gauss mass

`gaussMeasure_exceptional_le` (axiom-clean): at a fixed scale `ε ∈ (0,1]`,

    gaussMeasure (⋃_{i<m} (gaussMap^[i])⁻¹ (boundaryBad ε))  ≤  m · 6√ε / log 2 .

Linear in the depth `m` and in `√ε`.  Merging supplies `ε` exponentially small in the word
length, so this is summable — the Borel–Cantelli input.

Reuse, not rebuild: `gaussMeasure_preimage_iterate` was already in `CFPin.lean` (invariance, so
each level contributes the SAME mass — no Jacobian), and `gaussMeasure_le_volume` was already in
`CFDigitLaw.lean` (density ≤ 1/log 2).  New here: `boundaryBad_eq_iUnion` (reindexed as an
explicit countable union of intervals) and `measurableSet_boundaryBad`.

**The one honest gap, deliberately separated.**  This statement is for a FIXED `ε`, but
`cfDigit_agree_depth` needs `ε = δ · scale u i`, which depends on `u`.  The missing step is a
CUTOFF: on the set `{u : scale u m ≤ S}` the fixed-scale bound applies with `ε = δS`, and the
complement `{u : scale u m > S}` must be shown small.  Since `log (scale u m) = 2∑_{i<m}
log(cfDigit u i + 1)`, that is exactly a large-deviation statement for the Khinchin integral
`∫ log(1+a) dγ < ∞` — the same integral `VandeheyS7Clock` cites for the clock rate.

**Next attack (lap 20):** state `ScaleCutoff` as a named Prop (guard rule: content locator +
degenerate case) — `∀ η > 0, ∃ S, ∀ m, gaussMeasure {u | scale u m > S^m} < η` or the Cesàro form
— and prove the pieces that do not need the ergodic theorem: `log (scale u m) = 2∑ log(aᵢ+1)`
(`Finset.prod_range` + `Real.log_prod`), monotonicity, and the reduction of `SampledUniformCount`
to `ScaleCutoff` + what is already proved.  Check `CFDigitLaw.lean` / `CFBlockFreq.lean` first:
the repo may already have the Birkhoff average of `log(1+a)` from the Khinchin work
(`KHINCHIN.md`).

### 2026-09-29 lap 18 — DEPTH-`m` DIGIT AGREEMENT IS PROVED

`cfDigit_agree_depth` (axiom-clean): if `|u − v| < δ` and at every level `i < m` the point
`gaussMap^[i] u` lies in `(0,1)` and avoids `boundaryBad (δ · scale u i)`, then
`cfDigit v i = cfDigit u i` for all `i < m`.  Here `scale u i = ∏_{j<i} (cfDigit u j + 1)²` is
the accumulated one-step cost from lap 17.

Two things made it clean:

* **The shift identity is `rfl`.**  `cfDigit x i = cfDigit (gaussMap^[i] x) 0` holds definitionally
  because `cfDigit x n = ⌊(gaussMap^[n] x)⁻¹⌋₊`.  So the induction carries ONLY the metric
  invariant `|gaussMap^[i] u − gaussMap^[i] v| < δ · scale u i`, not any digit bookkeeping.
* **Strictness on both sides.**  `cylinder_of_not_boundaryBad` (refactored out of lap 16's proof)
  gives `1/(n+1) < v < 1/n` STRICTLY, and the strict upper bound is exactly what keeps
  `gaussMap v > 0` so the induction can take another step.

So the merging → digits transfer is complete at every depth.  The chain is now:

    spread_runWord_le → abs_sub_runWord_le → cfDigit_agree_depth
                                           ↘ volume_boundaryBad_le (per level)

**Next attack (lap 19): the measure of the pullback union.**  The only remaining gap in the
transfer is that the exceptional set is `⋃_{i<m} (gaussMap^[i])⁻¹ (boundaryBad (δ · scale u i))`,
and its measure must be shown small.  Two facts do it: `gaussMeasure` is `gaussMap`-INVARIANT (so
each pullback has the same measure as the set itself, no Jacobian to track), and
`volume_boundaryBad_le` bounds each at `6√(δ · scale u i)`.  What must be controlled is
`∑_{i<m} √(scale u i)` against `√δ` — and `scale` is exponential in `∑ log(aᵢ+1)`, which is
`O(m)` a.s. by the SAME Khinchin integral `∫ log(1+a) dγ < ∞` that `VandeheyS7Clock` cites for
the clock rate.  Note that coincidence: one integral underwrites both named hypotheses.
First step: find/prove `gaussMeasure` invariance in the repo (`CFInvariance.lean` is the likely
home) and state the pullback bound.

### 2026-09-29 lap 17 — one Gauss step costs exactly `(n+1)²`

`gaussMap_eq_sub` and `abs_gaussMap_sub_le`, both axiom-clean.  Inside a depth-one cylinder the
integer part of `x⁻¹` is the SAME integer for both points, so it cancels and

    gaussMap u − gaussMap v = u⁻¹ − v⁻¹ = (v − u)/(u v),   hence
    |gaussMap u − gaussMap v| ≤ (n+1)² |u − v|

with `n` the shared digit.  Exact, not an estimate: the only inequality is `u, v > 1/(n+1)`.

So a depth-`m` agreement costs `∏_{i<m} (aᵢ+1)^{-2}` in `δ`.  Merging supplies
`δ_n = 1/(fib(n-1)fib(n))`, which is exponentially small — the right order to pay this, since
`∑ log(aᵢ+1)` is `O(n)` almost surely (finite Khinchin mean, the same integral
`∫ log(1+a) dγ < ∞` that `VandeheyS7Clock`'s docstring cites for the clock rate).

**Next attack (lap 18): the depth-`m` induction.**  Iterate `abs_gaussMap_sub_le` with the shift
identity `cfDigit w (k+1) = cfDigit (gaussMap w) k` (proved in `CFAffineFamily.lean`).  The clean
statement to aim for:

    ∀ i < m, gaussMap^[i] u ∉ boundaryBad (δ · ∏_{j<i} (cfDigit u j + 1)²)
      →  ∀ i < m, cfDigit v i = cfDigit u i

i.e. the exceptional set is a FINITE union of depth-one bad sets pulled back along `gaussMap`,
each of measure `O(√(δ ∏ …))`.  Bounding that union is where the Khinchin integral enters; do the
induction first and leave the measure of the pullback union as the named node after it.

### 2026-09-29 lap 16 — digit agreement off the boundary set (lap 15 is now load-bearing)

`cfDigit_zero_eq_of_not_boundaryBad` : if `u ∈ (0,1)` is not within `δ` of ANY endpoint `1/k`,
and `|u − v| < δ`, then `cfDigit v 0 = cfDigit u 0`.  Axiom-clean.  With
`volume_boundaryBad_le` the exceptional `u` have measure `≤ 6√δ`, so the first CF digit is
locally constant at scale `δ` off a set of measure `O(√δ)`.

That closes the merging → digits transfer at depth one:

    abs_sub_runWord_le  (|u − v| ≤ δ_n, no state)
      +  cfDigit_zero_eq_of_not_boundaryBad  (digits agree off boundaryBad)
      +  volume_boundaryBad_le  (that set has measure ≤ 6√δ_n)

Supporting lemmas, all elementary and reusable: `cfDigit_zero` (`= ⌊x⁻¹⌋₊`), `floor_inv_spec`
(`1/(n+1) < u ≤ 1/n` for `n = ⌊1/u⌋₊ ≥ 1`), `cfDigit_zero_eq_of_mem` (converse).

**Next attack (lap 17): depth `m`.**  `cfDigit v i = cfDigit u i` for all `i < m`.  The honest
route is induction on `i` through `gaussMap`: if `u, v` share digit `0` and both lie in the same
depth-one cylinder, then `|gaussMap u − gaussMap v| ≤ |u − v| / (u v) ≤ (n+1)² |u − v|`, so the
scale degrades by the SQUARE of the digit at each step.  That is why the depth-`m` bad set needs
`δ` exponentially small in `m` — and merging supplies exactly that (`δ_n = 1/(fib(n-1)fib(n))`).
Formalise the one-step expansion bound first; it is a two-line `gaussMap` computation given
`Int.fract` on the relevant interval.

### 2026-09-29 lap 15 — the trigger window is quantitative: `volume (boundaryBad δ) ≤ 6√δ`

`VandeheyS7Boundary.lean`.  Merging gives two output points within `δ`; a CF digit is `⌊1/x⌋`,
so the digits agree UNLESS a point is within `δ` of a depth-one cylinder endpoint `1/k`.  That
bad set is `boundaryBad δ`, and `volume_boundaryBad_le` bounds it by `6√δ`.  Axiom-clean.

**The rate is `√δ`, not `δ`, and that was the thing to get right.**  The endpoints `1/k` are
infinitely many and accumulate at `0`, so "`2δ` per endpoint" DIVERGES — an obvious-looking route
that does not work.  The split is by scale: discard `(0, 2√δ)` wholesale (measure `2√δ`), and
above that scale only the `k ≤ 1/√δ` endpoints are reachable, contributing `2δ(1/√δ + 1) ≤ 4√δ`.

Consequence worth recording: **no digit cutoff is needed.**  The accumulation at `0` was the
reason to fear one, and paying `√δ` instead of `δ` buys it off.  Since merging supplies
`δ = 1/(fib(n-1)fib(n))`, exponentially small, `√δ` is still exponentially small and the loss is
free.  A cutoff would have had to be carried through the entire Cesàro argument.

**Next attack (lap 16): depth `m`.**  Same statement for `cfCylinder w` with `|w| = m`: the bad
set is the `δ`-neighbourhood of the depth-`m` endpoints.  The depth-`m` cylinder containing a
point of digit-sum-scale `Q` has length `~1/Q²`, so the same scale split should give
`O(√δ)` again with an `m`-dependent constant; the clean route is probably induction on `m` using
`gaussMap`'s expansion `1/x²` rather than re-running the covering.  Then: digits agree off
`boundaryBad`, and `SampledUniformCount` is Cesàro bookkeeping on a full-measure set.

### 2026-09-29 lap 14 — the projective-to-absolute bridge

Merging is proved in the Hilbert metric, but CF digits are read off an ABSOLUTE position
(`digit u = ⌊1/u⌋`), so the bound has to be converted.  It converts exactly:

    abs_sub_le_of_hdist_le :  hdist u v ≤ ε  →  |u − v| ≤ max u v · (exp ε − 1)

and since the machine's output point is in `(0,1)` the `max` is harmless.  `abs_sub_runWord_le`
is the merging bound in that form, still with no initial state on the right.  Axiom-clean.
Content locator `abs_sub_le_of_hdist_le_zero`: at `ε = 0` it collapses to `u = v`, so all the
content is in the exponential factor.

**Next attack (lap 15): digit determination.**  With `|u − v| ≤ δ_n → 0`, two output points have
the same first `m` CF digits as soon as both lie strictly inside the same depth-`m` cylinder.
Prove the one-digit case first — `u, v ∈ (1/(k+1), 1/k) → both have first digit k` — then the
depth-`m` version by iterating, and identify the exceptional set (points within `δ_n` of a
cylinder endpoint) whose Gauss measure `→ 0`.  That exceptional set IS the `ρ(∂U) = 0` trigger
window of DIRECTION item 3, and once its measure is shown to vanish, `SampledUniformCount` is a
Cesàro bookkeeping exercise over a set of inputs of full measure.

### 2026-09-29 lap 13 — MERGING IS DONE: loss of memory, uniform over states (`VandeheyS7Word.lean`)

`spread_runWord_le` : for every initial state `s`, every even word length `n ≥ 3`, and all
`x, y > 0`,

    hdist ((runWord s w).mob x) ((runWord s w).mob y) ≤ 1 / (fib(n-1) · fib(n)) .

The state does not appear on the right.  The infinite `ℤ[φ]` state set is invisible at this
range, which is exactly the merging the finite-chain citation was for.  Axiom-clean.

How it goes, in three steps and no dynamics:

* `wordState w = A_{a₁}⋯A_{aₙ}` and `runWord s w = s.comp (wordState w)` (`runWord_eq_comp`).
* **Fibonacci growth of both rows** (`fib_le_rowMin`).  Prepending `A_a` sends
  `(a b; c d) ↦ (c, d; a + Ac, b + Ad)`, so `rowMin₁(A_a W) = rowMin₂(W)` and
  `rowMin₂(A_a W) ≥ rowMin₁(W) + rowMin₂(W)` — a Fibonacci recursion read straight off the matrix
  product.  No continuants, no Gauss measure, no CF theory.
* **`det = (-1)^n`** (`det_wordState`), so `ad/bc = 1 + 1/(bc)` and
  `log(ad/bc) ≤ ad/bc − 1 = 1/(bc) ≤ 1/(fib(n-1)fib(n))` (`spread_wordState_le`).  Then
  `hdist_comp_le` (lap 12) removes the initial state.

Note the Birkhoff coefficient (lap 11) is NOT used on this route; it is the quantitative
refinement, kept because it gives a per-two-digit rate.

**Next attack (lap 14): wire merging into `SampledUniformCount`.**  With the window lemma
(`windowBound`) and merging both in hand, `VandeheyS7Clock.lean`'s `SampledUniformCount q r ℓ` is
the remaining crux node.  The step to find: `spread_runWord_le` bounds the spread of the machine's
OUTPUT POINT; turn that into a bound on the discrepancy of the sampled digit counts (the trigger
windows with `ρ(∂U) = 0` from DIRECTION item 3).  Read `VandeheyS7Clock.lean`'s docstring first
and identify precisely which quantity the spread bound has to control.

### 2026-09-29 lap 12 — nonexpansiveness, and calculus was not needed

The expected lap-12 step was mean-value bookkeeping on `birkhoff_derivative_le`.  It is not
needed.  That every nonnegative Möbius map is NONEXPANSIVE for the Hilbert metric is a polynomial
identity: for `0 < u ≤ v` and nonnegative `A,B,C,D`,

    v(Au+B)(Cv+D) − u(Av+B)(Cu+D) = (v−u)(ACuv + BC(u+v) + BD) ≥ 0
    v(Av+B)(Cu+D) − u(Au+B)(Cv+D) = (v−u)(ACuv + AD(u+v) + BD) ≥ 0

i.e. `u/v ≤ f(v)/f(u) ≤ v/u` (`mob_ratio_le`, `mob_ratio_ge`), hence `mob_nonexpansive` — with NO
hypothesis on the determinant, so it holds for every `MobState` in either orientation.  All
axiom-clean.

The payoff is `hdist_comp_le`: `hdist ((s.comp t).mob x) ((s.comp t).mob y) ≤ hdist (t.mob x)
(t.mob y)`.  The initial state `s` can only SHRINK what the input word `t` produces, so a
diameter bound for the word alone bounds the spread from every initial state at once.  That is
the loss of memory, and it is exactly what the infinite `ℤ[φ]` state set made unobtainable by the
finite-chain route.

**Next attack (lap 13): the word diameter goes to zero.**  Combine `hdist_comp_le` with
`hdist_image_le` applied to the word state `W = A_{a₁}···A_{a_n}`: the image diameter is
`log (ad/bc)`, and `det W = ±1` gives `ad/bc = 1 ± 1/(bc)` with `bc` a product of consecutive
continuants, so the diameter is `≤ 1/(bc) → 0`.  Note this route needs NO contraction factor at
all — `gaussPair_birkhoffCoeff_le` (lap 11) becomes the quantitative refinement rather than the
load-bearing step.  Formalise `runWord`'s entries as continuants (the `Conv` fold in
`VandeheyS7Convergent.lean` is the right instrument; `cfP`/`cfK` are NOT, see the handoff gotcha)
and prove `q_n → ∞`.

### 2026-09-29 lap 11 — merging: the contraction factor is UNIFORM (`VandeheyS7Merge.lean`)

Next-action #1 from the handoff is done, and it gave more than expected.  Two Gauss branches
compose to `A_a A_b = (1, B; A, 1+AB)` (`gaussPair`), strictly positive in all four entries with
determinant exactly `1` — so the Birkhoff diameter is finite after two digits, from any state.
The surprise: with `ad = 1+t`, `bc = t`, the coefficient collapses to `(√(1+t) − √t)^2`
(`birkhoffCoeff_one_add`), which is DECREASING in `t`.  Large digits contract more; the worst
case is the smallest product `t = AB = 1`, i.e. `a = b = 1`.  Hence

    gaussPair_birkhoffCoeff_le :  birkhoffCoeff (A_a A_b) ≤ 3 − 2√2 ≈ 0.1716

for EVERY pair of digits — no digit bound, no positive-frequency argument, no large deviations.
All axiom-clean.

**Next attack (lap 12):** the mean-value bookkeeping.  `birkhoff_derivative_le` bounds the
derivative in the log coordinate; combine it with `gaussPair_birkhoffCoeff_le` to get
`hdist (s.mob x) (s.mob y) ≤ (3−2√2) · hdist x y` for `s = gaussPair a b`, then iterate along the
input word to get `hdist → 0` geometrically.  That is the loss of memory, and it feeds
`SampledUniformCount`.

newest first)

### 2026-09-29 — lap 1 of the §7 objective: targets frozen, and the endgame is OFF ℤ

`src/NormalNumbers/VandeheyS7.lean` (new, in the root import).

**Frozen (never weakened):** `AffineCFN q r` (`∀ x, IsCFNormal (Int.fract x) → IsCFNormal
(Int.fract (q*x+r))`), `AffineUniformFreq q r` (the crux: every genuine word has an
`x`-INDEPENDENT frequency limit in the image; no value asserted), `IsQuadOverRat`,
`VandeheyS7Problem1`, `vandeheyS7_mul_phi := AffineCFN φ 0`, `vandeheyS7_add_phi := AffineCFN 1 φ`.
An `Audit` section pins all three headline Props by `rfl`, and
`vandeheyS7_mul_phi_of` / `vandeheyS7_add_phi_of` prove in-kernel that the two instances really
are instances of the general Prop (so the general form cannot silently drift off them).

**The lap's advance on the crux.**  The attack map's §3 asserted that Vandehey's either-or
endgame "works verbatim for any `M`", so that the whole problem reduces to frequency EXISTENCE.
That is now a THEOREM, axiom-clean:

    affineCFN_of_uniformFreq : 0 < q → AffineUniformFreq q r → AffineCFN q r

for EVERY real `q > 0` and EVERY real `r` — no integrality, no quadraticity, nothing about ℤ[φ].
Both instances are reduced (`vandeheyS7_mul_phi_of_uniformFreq`, `vandeheyS7_add_phi_of_uniformFreq`).

Two things made it port.  (i) The integer version (`Literature.mobiusCFN_of_uniformFreq`) pins the
unknown limit with `exists_cfNormal_with_cfNormal_image`, a Γ-orbit argument that does not exist
over ℤ[φ]; the replacement pin is the MEASURE-theoretic witness
`exists_feasible_cfNormal_affine` (both `x₀` and `q x₀ + r` CF-normal, from two conull sets
meeting on the feasible window), which never looks at the arithmetic of the coefficients and so is
indifferent to the unit group.  (ii) That witness needs `-q < r < 1`, which `r = φ` violates;
`affineCFN_add_int` / `affineUniformFreq_add_int` show both Props depend on `r` only mod 1, so
`Int.fract` reduces the general `r` to the window.

**Consequence to carry: the ℤ[φ] wall is entirely on the frequency-EXISTENCE side.**  No part of
what remains needs a limit VALUE.  Route A's nodes (window/bounded-distortion lemma, distributional
merging, trigger windows) all feed `AffineUniformFreq` and nothing else.

Guard rule discharged: content locators `affineUniformFreq_one`, `affineCFN_int_translate`;
degenerate case `not_affineCFN_zero` proves the `q = 0` instance FALSE (the junk expansion of `0`
contains no `[1]`, while `γ(I_[1]) > 0`), so `q ≠ 0` in `VandeheyS7Problem1` is load-bearing.

**Lap 2 (same day), DIRECTION item 2 — the obstruction as Lean: DONE.**
`src/NormalNumbers/VandeheyS7Wall.lean`, four theorems, all axiom-clean.

* `finite_intCast_abs_le` — the content locator for Vandehey's finiteness: over ℤ a bound on
  the absolute value bounds the set.  This, and nothing about the dynamics, is the certificate.
* `infinite_zPhi_abs_le_one` — **the certificate has no ℤ[φ] analogue**: `{x ∈ ℤ[φ] : |x| ≤ 1}`
  is INFINITE, witnessed by the powers of `ζ = φ − 1 = φ⁻¹ ∈ (0,1)`.  Dirichlet's unit theorem
  made concrete; `IsZPhi.mul` is where `φ² = φ + 1` enters.
* `infinite_zPhiMatrix_det_one_bounded` — the matrix form: infinitely many determinant-one
  matrices over ℤ[φ] with every entry bounded by 1 (`!![1, ζ^n; 0, 1]`).
* `conj_goldenRatio_integral_forces_diagonal` — **pathwise merging is impossible.**  If `V`, `N`
  are integral and `diag(φ,1) · N = V · diag(φ,1)` then `V 0 1 = V 1 0 = 0`.  So no coupling or
  synchronising-word merging argument exists for `x ↦ φx`, and Vandehey §5's Saloff-Coste–Zúñiga
  citation must be replaced by a DISTRIBUTIONAL statement (Birkhoff–Hopf cone contraction).

Scope stated honestly in the module docstring: this kills the finiteness LEMMA over ℤ[φ], which
is all the Theorem 1.1 proof uses; it does not compute the actual reachable set.

**Lap 3 (same day), DIRECTION items 3–4: the pipeline is FACTORED.**
`src/NormalNumbers/VandeheyS7Clock.lean`, all axiom-clean.

`VandeheyOut.mobiusUniformFreq_of_runClock` — the restatement that made Thm 1.1 assemble — has a
proof that is ONE rescaling and nothing else: no transducer, no output stream, no determinant, no
state set.  So it ports verbatim to a real affine map, and the whole of §7 Problem 1 now reads

    affineCFN_of_runClock : 0 < q → RunClock ℓ rate → SampledUniformCount q r₀ ℓ → AffineCFN q r₀

with both φ instances instantiated (`vandeheyS7_mul_phi_of_runClock`, `..._add_phi_of_runClock`).
The two named hypotheses are the finite-state step, split along its real fault line:

* `RunClock ℓ rate` — monotone clock, positive `x`-independent rate.  Formally MAP-FREE (it
  does not mention `q`, `r₀`), which is the half of the bundle that is not about the image at
  all.  Believed fine: the attack map's 2026-08-24 measurement has `l(n) = c₁n(1+o(1))`
  surviving the loss of Lemma 2.2 because `∫log(1+a)dγ < ∞`; `c₁ ∈ [0.965, 0.989]`.
* `SampledUniformCount q r₀ ℓ` — `x`-independent Cesàro limit for each word's count sampled
  along the clock.  **This is the entire remaining crux**, and the only place the lost ℤ[φ]
  finiteness has to be replaced (trigger windows + distributional merging, Route A nodes 2–3).

Content locator `affineUniformFreq_of_runClock_locator` (identity clock, rate 1) discharges the
guard rule; `not_affineCFN_zero` already rules out vacuity.

**Lap 4 (same day), Route A node 1: the compact-fiber substitute is PROVED.**
`src/NormalNumbers/VandeheyS7Distortion.lean`, all axiom-clean.

The 2026-08-24 correction 2 (drop "compact in PGL₂(ℝ)", keep BOUNDED DISTORTION) is now cashed
in.  `MobState` is a Möbius state in the shape every post-emission Raney state has (`c ≥ 0 < d`,
positive determinant) — over ANY ring, which is the point — with
`distortion s = (c + d)/d`, and

  `MobState.mob_ratio_comparable` : for `0 ≤ u ≤ v ≤ 1`,
     `(v−u)/distortion ≤ (M v − M u)/(M 1 − M 0) ≤ (v−u)·distortion`.

This is precisely the rôle the finite state set played in Vandehey §5–§6.  There one takes a
maximum of per-state constants over a finite set; here ONE constant covers the whole family, and
that two-sided comparability is all his `f_j^±` Riemann squeeze ever consumes.
`uniform_comparable_of_bddDistortion` states the consequence along a whole state sequence.

So the open obligation is narrowed to the HYPOTHESIS `BddDistortion s` — Route A's window lemma,
now a named Prop.  Guard rule: `distortion_id` (content locator; identity has distortion 1 and
the theorem degenerates to equality) and `not_bddAbove_distortion` (distortion is unbounded over
the ambient family, so `BddDistortion` is a real restriction, not a theorem of the setting).

**Lap 5 (same day): distortion is an EXACT COCYCLE, and that is the window lemma's mechanism.**
`src/NormalNumbers/VandeheyS7Cocycle.lean`, all axiom-clean.

`MobState` is now closed under composition (`comp`, the matrix product; the nonnegativity fields
were added for this), and the denominators satisfy

  `den_comp` : `den (s ∘ t) x = den t x * den s (t x)`  — EXACTLY, no constant, no inequality.

Denominators are a cocycle over the action.  Hence, with the two-point distortion
`distOn s u v = den s v / den s u` (and `distortion s = distOn s 0 1`),

  `distOn_comp` : `distOn (s∘t) u v = distOn t u v * distOn s (t u) (t v)`,
  `distOn_le_one_add` : `distOn s u v ≤ 1 + (v−u)·distortion s` (no upper bound on `v` needed),
  `distortion_comp_le` : `distortion (s∘t) ≤ distortion t · (1 + |t([0,1])|·distortion s)`.

**Why this is the mechanism.**  The post-emission state is `A_out⁻¹ · M₀ · A_{a₁}⋯A_{aₙ}`.  The
right factor is a composition of Gauss inverse branches — its distortion is the classical Rényi
constant, which is exactly the probes' measured "`log 4` for every integer control".  The left
factor is the drifting ℤ[φ] part with no finiteness certificate.  `distOn_comp` says the drifting
factor is only ever evaluated ON THE INNER IMAGE, and `distOn_le_one_add` says its contribution
→ 1 as that image shrinks.  That is the structural reason the probes measured ℤ[φ] distortion
SATURATING at ≈ 2.5 instead of drifting, while the conjugate place ran to 10^644 — and it is the
inductive step any window bound must run on.

**Lap 6 (same day): reading is FREE; emitting is the whole problem.**
`src/NormalNumbers/VandeheyS7Branch.lean`, all axiom-clean.  (`MobState.hdet` relaxed from
`0 < det` to `det ≠ 0` — Raney states have `det = ±D`, and the comparability ratio of
`VandeheyS7Distortion` is orientation-blind, so the refactor cost nothing.)

The `φ`-machine is now a Lean object: `gaussBranch a : y ↦ 1/(a+y)` (totalised at `a = 0`),
`phiState = diag(φ,1)`, `runWord` the fold.  Two facts, and they are sharper than the attack map
expected.

1. **Reading an input digit is free.**  Right-composition by `A_a` sends the lower row `(c,d)` to
   `(d, c + a·d)`, so with `a ≥ 1`, `c ≥ 0` it lands in `c ≤ d` FROM ANYWHERE and stays.  Hence
   `distortion_runWord_le_two`: after at least one input digit the distortion is `≤ 2`, from any
   initial state, with NO arithmetic hypothesis and no finiteness.  This is the in-kernel form of
   the probes' "real place flat, no drift", and over ℤ it is Rényi's bounded-distortion property.
2. **Emitting swaps the rows.**  `emit e s` is left-multiplication by `(−e,1;1,0)`, i.e.
   `(a,b;c,d) ↦ (c−e·a, d−e·b; a, b)` (`mob_emit` proves it is `z ↦ 1/z − e`).  So
   `distortion_emit : distortion (emit e s) = (s.a + s.b)/s.b` — the UPPER row's ratio, while
   reading controls the LOWER row's.  Reading pushes the state into the good region; emitting
   throws it back out.  **That exchange is the entire content of the window lemma.**

So the obligation is sharpened from `BddDistortion` (a sequence of abstract states) to
`EmitRowBound` (one explicit arithmetic ratio `(a+b)/b` of two ℤ[φ] numbers, at emission times
only), and `bddDistortion_of_emitRowBound` proves the two are the same statement.  `EmitRowBound`
is exactly what both 2026-08 probes measured saturating at ≈ 2.5.

**Lap 7 (same day): THE BURST PENALTY IS A CONSTANT, not a function of the burst length.**
`src/NormalNumbers/VandeheyS7Burst.lean`, all axiom-clean.  This is the lap that dissolves the
loss of Vandehey's Lemma 2.2.

The obvious estimate loses a factor per emitted digit, so a burst of `k` emissions with no
intervening read would cost `2^k`, and Lemma 2.2 (which bounded bursts) was MEASURED not to port
(`burst ≤ C + log(1+a)/Lévy`, unbounded, tracking `0.843·ln a`).  The dissolution is that a burst
should never be analysed digit by digit at all:

1. **A burst of `k` emissions is ONE pullback.**  It is left-multiplication by `B⁻¹` for
   `B = A_{e₁}⋯A_{e_k}`, whose columns are the continuants `(p_{k−1},q_{k−1})`, `(p_k,q_k)`.
   `distortion_pullback` (EXACT, for arbitrary `P, Q`):

       distortion_after = distortion_before · (β − M 1)/(β − M 0),   β = P/Q .

   The whole burst costs ONE factor: the ratio of the distances from the two image endpoints to
   the convergent `β = p_{k−1}/q_{k−1}`.
2. **That factor is ≤ 2 whatever `k` is.**  The burst emits `e₁…e_k`, so the image lies in the
   cylinder `C = [e₁,…,e_k]`, endpoints `p_k/q_k` and `(p_k+p_{k−1})/(q_k+q_{k−1})`, and `β` is
   outside `C` with

       far  = |β − p_k/q_k|                     = 1/(q_{k−1}q_k),
       near = |β − (p_k+p_{k−1})/(q_k+q_{k−1})| = 1/(q_{k−1}(q_k+q_{k−1})),

   so `far/near = (q_k+q_{k−1})/q_k ≤ 2` since `q_{k−1} ≤ q_k`.  **The burst length does not
   appear.**  `burst_ratio_le` proves the consequence; `one_le_burst_ratio` records that the
   lower side is free, so all the content is on the upper side.
3. `distortion_pullback_le` assembles it: pre-burst distortion `≤ 2` (which reading gives for
   free, lap 6) plus the geometric input gives post-burst distortion `≤ 4`.  A **window bound of
   4 along the whole run.**

**Still owed (the only gap between here and the window lemma):** the continuant bookkeeping —
that the emitted word's matrix is the continuant matrix, `q_{k−1} ≤ q_k`, and the two distance
identities above.  All standard and self-contained.  `ConvergentGap` names exactly that input,
and `burst_ratio_le` is stated so it plugs in as `hfar : v − β ≤ 2*(u − β)`.

**Lap 8 (same day): `ConvergentGap` is PROVED.**
`src/NormalNumbers/VandeheyS7Convergent.lean`, all axiom-clean.

`Conv` is the continuant state `(p',q',p,q)` with the recursion
`(p',q',p,q) ↦ (p, q, p' + a·p, q' + a·q)`, folded over the word; `Conv.Good` is the invariant
(`0 ≤ p'`, `0 ≤ q' ≤ q`, `1 ≤ q`, `Δ² = 1` for `Δ = p q' − p' q`), carried one step at a time
(`Good.step`, the determinant by `linear_combination`).  Then:

* `conv_far_eq` — **the gap identity**: `p/q − p'/q' = ((q+q')/q)·((p+p')/(q+q') − p'/q')`.
  `Δ` CANCELS, so the determinant is needed only as a nonzero, never at its value `±1`.
* `conv_ratio_le_two` — the constant is in `[1, 2]`, and `q' ≤ q` is the whole of it.
* `conv_far_le_two_near` — `far ≤ 2·near`, for EVERY word of positive digits, of EVERY length.
  The burst length appears nowhere.
* `conv_single` — content locator: one digit, `β = 0`, ratio `(e+1)/e ≤ 2`, visible by hand.

So the geometric input of lap 7 is no longer owed, and the window-lemma chain is complete as
mathematics:  reading ⇒ distortion ≤ 2 (lap 6) · burst = one pullback with penalty ≤ 2 (lap 7,
now unconditional by this lap) ⇒ **distortion ≤ 4 along the whole run**.

**Still owed on the window lemma (bookkeeping only, no new mathematics):** wire `Conv.of` to the
machine — that the emitted word's pullback matrix has first column `(p', q')` of `Conv.of` of the
emitted word, and that the image interval really lies in that word's cylinder (the emission
trigger).  Then `distortion_pullback_le` applies verbatim and `BddDistortion`/`EmitRowBound` are
theorems.

**Lap 9 (same day): THE WINDOW LEMMA IS ASSEMBLED.**
`src/NormalNumbers/VandeheyS7Window.lean`, axiom-clean.

`windowBound` : a state of distortion `≤ 2` — which reading gives for free — whose image
endpoints sit in the emitted word's cylinder has **post-burst distortion `≤ 4`**, with the
emitted word's LENGTH appearing nowhere.  Four laps meet in its proof: `distortion_runWord_le_two`
(lap 6), `distortion_pullback` (lap 7, exact), `conv_far_le_two_near` (lap 8).

Supporting: `cylNear`/`cylFar`/`cylBeta`; `conv_near_ne_zero` (the near distance is `Δ/((q+q')q')`
— the ONLY use of the continuant determinant in the whole development, and only as a nonzero);
`TriggerGap` (the emission trigger in the one form the estimate consumes); `triggerGap_endpoints`
(content locator — the cylinder's own endpoints satisfy it, so the hypothesis is not empty).

**The remaining bookkeeping on this node, with no estimate in it:** turn the machine's operational
emission trigger into `TriggerGap`, i.e. show the image interval lies in the emitted word's
cylinder (which is what emission MEANS), and identify the pullback matrix's first column with
`Conv.of`'s `(p', q')` (checked by hand: `A_e = (0 1; 1 e)` and `Conv.of [e] = ⟨0,1,1,e⟩`, and the
recursions agree).  Then `BddDistortion` / `EmitRowBound` are theorems.

**Lap 10 (same day): the Birkhoff–Hopf coefficient, and its analytic core PROVED.**
`src/NormalNumbers/VandeheyS7Birkhoff.lean`, axiom-clean.

The second half of `SampledUniformCount` is MERGING.  Vandehey cites Saloff-Coste–Zúñiga for a
finite chain; that is unavailable twice over here (infinite state set, and pathwise merging is
PROVABLY IMPOSSIBLE — `conj_goldenRatio_integral_forces_diagonal`).  So the replacement is
distributional: Birkhoff–Hopf contraction of the Hilbert projective metric.  Landed:

* `hdist`, `mob_mem_Icc`, `hdist_image_le` — a state with POSITIVE entries maps `(0,∞)` into
  `[b/d, a/c]`, so the image has Hilbert diameter `≤ log(ad/(bc))`.  Finite exactly when all four
  entries are positive: **positivity, not finiteness, is the right hypothesis over ℤ[φ]**.
* `birkhoffCoeff a b c d = (√(ad) − √(bc))/(√(ad) + √(bc))` — this is `tanh(Δ/4)` in these terms.
  `birkhoffCoeff_lt_one` (a genuine contraction factor as soon as `bc > 0`),
  `birkhoffCoeff_nonneg`, plus both guard-rule cases: `birkhoffCoeff_of_eq` (singular ⇒ 0,
  constant map) and `birkhoffCoeff_bc_zero` (triangular ⇒ 1, NO contraction — positivity of all
  four entries is load-bearing).
* **`birkhoff_denom_bound`** — the whole analytic content, in one inequality:
  `ac x² + (ad+bc) x + bd ≥ x(√(ad)+√(bc))²`, by AM–GM on `ac x² + bd ≥ 2x√(ac·bd)` with
  `(ac)(bd) = (ad)(bc)` identifying the geometric mean.
* `birkhoff_derivative_le` — assembles it: `x(ad−bc)/((cx+d)(ax+b)) ≤ birkhoffCoeff`, i.e. the
  action is `birkhoffCoeff`-Lipschitz in the log coordinate, modulo mean-value bookkeeping.

**What is left on this node:** the mean-value step (derivative bound ⇒ Lipschitz bound in the log
coordinate) — no further inequality and no dynamics — and then the loss-of-memory statement for a
composition, which needs `bc > 0` along the run, i.e. the states to be strictly positive rather
than merely nonnegative.  **That positivity is the next real question**, and it is a statement
about the φ-machine, not about the metric.

**NEXT (lap 11).**  Strict positivity of the run states: show `b, c > 0` after enough input
digits (`gaussBranch` has a zero in the corner, so a single step is not enough — two steps
should be: `A_a A_b = (1, b; a, ab+1)`, all positive for `a,b ≥ 1`).  That, with
`birkhoff_derivative_le`, gives a uniform contraction factor `< 1` per two input digits, which is
the loss of memory that replaces Vandehey's finite-chain merging.

**(superseded) NEXT (lap 10): the SECOND half of `SampledUniformCount`.**  With the window lemma in hand the
remaining crux is the distributional merging — Birkhoff–Hopf cone contraction of the Hilbert
projective metric, NOT coupling (`not_synchronizing`-style pathwise merging is provably impossible
here, `conj_goldenRatio_integral_forces_diagonal`).  `mob_ratio_comparable` is already the right
language: a uniform distortion bound gives uniform two-sided comparability, which is exactly a
Hilbert-metric diameter bound on the cone of image measures, and a bounded-diameter image is what
makes the transfer operator a strict contraction.  First target: state the contraction as a Prop
on `MobState` sequences and prove that `distortion ≤ K` gives a finite Hilbert diameter.

**(superseded) NEXT (lap 9).**  Either (a) finish that wiring — define the emission trigger as a predicate on
`MobState` and prove the cylinder containment by induction on the burst, discharging
`EmitRowBound`; or (b) open the SECOND half of `SampledUniformCount`, the distributional merging
(Birkhoff–Hopf cone contraction on the Hilbert projective metric), which is the remaining crux
once the window lemma lands and which `mob_ratio_comparable` is already the right language for.
(a) is finite and closes a node; (b) is the harder one.  Take (a) first — it converts four laps
of structure into a discharged hypothesis.

**(superseded) NEXT (lap 8).**  Prove `ConvergentGap` for the real thing: define the continuants of the
emitted word, prove `q_{k−1} ≤ q_k` and the two distance identities (`|p/q − p'/q'| = 1/(qq')`
from `det = ±1`), and discharge `ConvergentGap`.  That closes the window lemma
(`BddDistortion` / `EmitRowBound`), leaving `SampledUniformCount`'s SECOND half — the
distributional merging / trigger windows — as the remaining crux.

**(superseded) NEXT (lap 7).**  Attack `EmitRowBound` directly.  The geometry that should give it: emission
fires only when the image interval `M([0,1])` lies inside a cylinder `(1/(e+1), 1/e)`, which pins
`b/d` and `(a+b)/(c+d)` both to that cylinder; combined with the free bound `(c+d)/d ≤ 2` this
gives `(a+b)/b ≤ 2·(e+1)/e ≤ 4` for a SINGLE emission.  The open part is a BURST of consecutive
emissions with no intervening read, where the crude factor compounds — which is exactly the
content of the lost Lemma 2.2 (`burst ≤ C + log(1+a)/Lévy`, unbounded, measured 0.843·ln a).
So the next target is: state the emission trigger as a hypothesis, prove the single-emission
bound, and then find what replaces the burst bound.  Note `∫ log(1+a) dγ < ∞` is still available,
which is why the run clock survives; the question is whether a MULTIPLICATIVE burst penalty can
be averaged the same way.

**(superseded) NEXT (lap 6).**  Close the quantitative loop.  Two sub-nodes, in order:
(i) the Rényi bound for the inner factor — `distortion` of any composition of Gauss inverse
    branches `A_a : y ↦ 1/(a+y)` is ≤ 4, by induction through `distortion_comp_le` (or directly:
    a Gauss branch has `c = 1, d = a`, so `distortion = (1+a)/a ≤ 2`, and the image has length
    `1/(a(a+1)) ≤ 1/2`, so the product telescopes).  This is self-contained and should close.
(ii) the emission rule, which is what makes `|t([0,1])|` small often enough.  Needs the
     φ-transducer as a Lean object; `distortion_comp_le` is the shape its invariant takes.

**(superseded) NEXT (lap 5).**  Build the `φ`-transducer as a Lean object so `BddDistortion` can be attacked:
states as `MobState`s carrying `IsZPhi` entries, the update `M_{n+1} = A_out⁻¹ M_n A_{a_{n+1}}`,
and the emission rule.  Then the window lemma itself, remembering correction 1: Vandehey's
Lemma 2.1 is an INTEGER DESCENT and does not port, so the proof must be new.  The likeliest
route is that emission fires exactly when the image interval falls deep into a cylinder, and
pulling the digits off re-expands the map — i.e. the renormalisation ENFORCES the distortion
window; `mob_ratio_comparable` is already the right language to state that in.

**(superseded) NEXT (lap 4).**  Attack `SampledUniformCount` for `q = φ`.  The first sub-node is Route A's
window lemma stated for the REDUCED post-emission states in terms of BOUNDED DISTORTION (not
compactness in PGL₂(ℝ) — correction 2 of 2026-08-24; the raw state set is unbounded in the
PROVED case too).  That needs the φ-transducer's state as a Lean object, which does not exist
yet: building it (states as Möbius maps over ℤ[φ], update `M_{n+1} = A_out⁻¹ M_n A_{a_{n+1}}`,
distortion as a real functional) is the lap-4 deliverable, with the window lemma as the first
disclosed `sorry` on it.

**(superseded) NEXT (lap 3), DIRECTION items 3–4.**  Factor the Thm 1.1 pipeline so its finite-state step is a
NAMED hypothesis, then state the compact-fiber substitute that discharges it: the bounded-
distortion window lemma for reduced post-emission states (NOT the integer descent — corrected
2026-08-24), and the distributional merging statement.  Every node wires to `AffineUniformFreq`,
which `affineCFN_of_uniformFreq` has already shown is the entire remaining problem.

**(superseded) NEXT (lap 2), DIRECTION item 2 — the obstruction as Lean.**  State and prove, against the
existing Raney transducer, that the reachable ℤ[φ] state set is infinite (unit drift), and the
non-merging fact (`M⁻¹VM` integral for `M = diag(φ,1)` forces `V` diagonal).  Then factor the
Thm 1.1 pipeline so its finite-state step is a NAMED hypothesis that a compact-fiber substitute
can discharge.

### 2026-09-28 — OPERATOR OBJECTIVE items 1-3, all three landed

1. **`moshchevitinShkredov_cf_false` PROVED** (`MoshchevitinShkredovRefuted.lean`, wired into
   the root import).  Witness `x = [0;1,2,3,…]` from `exists_irrational_mem_iInter_cfCylinder`
   on the nested words `[1,…,s+1]`; `exists_irrational_cfDigit_succ` is the reusable form.
   Strictly increasing digits ⇒ the first letter of a genuine block pins its unique start
   position ⇒ every block occurs at most once ⇒ every frequency is `O(1/p)`, so the criterion's
   hypothesis is vacuous at `σ = 0` while `γ(I_1) = log₂(4/3) > 0`.  Maze:
   `hall_moshchevitin_shkredov_cf_false`.
2. **`conjC3_of_geom_input_band'`** (`C3MrtBlockDefect.lean`) is the C3 headline with `hURM`
   discharged by `uniformResonantMass_holds`.  `C3MrtURMLowHigh.lean` retired as the redundant
   second route: its sorried narrow high range `|t| < 2δ` had no consumer and is removed; its
   sorry-free lemmas stay.  Maze: `hall_urm_low_high_split`.
3. **`exists_jointFreq_limit` retired.**  Its `Synchronizing` hypothesis is unsatisfiable, and
   that is now a THEOREM, not just a probe: `not_synchronizing_of_injective_quotient` — an
   automaton with a quotient on which every letter acts injectively has no synchronizing word.
   For the det-`±D` transducer the quotient is the row-lattice class in `ℙ¹(ℤ/D)` and each
   `B_a ∈ GL₂(ℤ/D)`.  Axiom-free.  Maze: `hall_vandehey_synchronizing_transducer`.  The live
   transfer principle is `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`, whose
   hypothesis `ClassEquidistribution` is now the single crux of the Vandehey front.

### 2026-09-28 lap 1 (review) — the output side opened; crux re-aimed

Reviewed the last three laps: all three had gone into the transducer's *input* side (Raney §2,
the pin, Doeblin) while §4.3/§5/§6 — the piece that decides whether the input side is worth
anything — had never been touched.  Course-corrected in `DIRECTION.md` CURRENT DIRECTIVE.

The structural find that makes §5–§6 elementary: our own
`tendsto_jointCount_of_classEquidistribution` returns the joint (window, state) limit in
**factorized** form `ν t · γ(I_q)`.  Vandehey only has `ρ ≪≫ μ̃` (Remark 3.6) and therefore
needs a genuine measure to get countable additivity; with the product form, countable
additivity reduces to countable additivity of `γ` alone, and the infinite CF alphabet is
escaped by a finite digit-truncated family of mass `> 1 − ε`.  That is also exactly the
tightness patch the published §3 owes and never pays.

Landed in the kernel (`VandeheyOutputFreq.lean`, all `#print axioms`-clean):
`gaussMeasure_allWordsEvent`, `exists_boundedWords_sum_gt`, `wCount_le_of_finset`,
`eventually_wCount_le`, plus the guard-rule quartet for the new `Prop` `JointStateFreq`.


### 2026-09-29 lap 48 — the bad-state bootstrap is de-circularised (`VandeheyS7Sep.lean`)

**Advance on the crux (`OrbitWordBound`).**  The directive's obstruction (2) — "the per-state
distortion bound fails at states whose image straddles `1/k` far below the scale of `E`, and the
crux's own `w = []` case is what must control them, a bootstrap" — is now a *counting* statement
with no circularity, because `ImageTight` is an INDEPENDENT hypothesis of the assembled chain
(`vandeheyS7_mul_phi_of_orbitWordBound`), so it may be used freely while proving the word bound.

Proved, all axiom-clean:

* `dist_inv_ge_of_digits_le` — **the separation estimate**: if the first THREE CF digits of
  `t ∈ (0,1)` are `≤ T`, then `|t − 1/k| ≥ 1/(2(T+1)³)` for every `k ≥ 1`.  Three cases
  (`k = a₀`, `k < a₀`, `k > a₀`) with gaps `S/(a₀(a₀+S))`, `1/(a₀(a₀−1))`, `(1−S)/((a₀+S)(a₀+1))`;
  the second digit bounds `S` from below, the third bounds `1 − S` from below.
* `two_digits_insufficient` — two digits are NOT enough (`a₀ = a₁ = 1` puts `t` arbitrarily near
  `1/2`), so the third digit is load-bearing, not slack.
* `exists_large_digit_of_near_inv` — the contrapositive: near a reciprocal ⇒ a digit `> T` among
  the first three.  This is "bad state ⇒ huge output digit" in the kernel.
* `blockCount_nearInv_le` — `#{visits to nearInv(1/(2(T+1)³))} ≤ 3·#{visits to cellSet [] (T+1)} + 6`.
* `exists_nearInv_freq_le` — **the payoff**: `ImageTight y` ⇒ for every `ε` there is a scale `η`
  at which the orbit of `y` spends frequency `≤ ε` within `η` of the reciprocals.

**NEXT (lap 49).**  The remaining half of the distortion route: at a *good* output position (image
point `η`-far from every `1/k`) the post-emission state's image interval `J` has `|J| ≥ η`-type
lower bound, hence `uniform_comparable_of_bddDistortion` applies and the pullback of `I_w` has
Gauss mass `≤ C γ(I_w)`.  Formalize "reduced state + image not straddling a reciprocal at scale
`η` ⇒ `|J| ≥ η`" against `MobState`, then sum: frequency ≤ (good positions, distortion bound) +
(bad positions, `exists_nearInv_freq_le`).  Note the good-position estimate is still where the
predictability obstruction (`not_predictableHitPrinciple`) bites; the honest next probe is to see
whether the good-state pullback bound is uniform enough to survive the `s_n` dependence, or
whether a Lean witness refutes it.

### 2026-09-29 lap 49 — the good half, and the exact price of the split (`VandeheyS7Good.lean`)

* `MobState.width_ge_of_mem_of_far` — two points of the image at distance `≥ η` force the image
  to be `≥ η` wide.  For a *reduced* state the two points are the current output point and the
  reciprocal `1/k` the state straddles, so lap 48's "far from every `1/k`" is exactly a lower
  bound on the image width.
* `MobState.sub_le_of_image_le` — the pullback bound: a sub-interval of `[0,1]` whose image has
  length `≤ L` has length `≤ distortion · L / η` once the image is `≥ η` wide.
* `splitConstant_not_absolute` — **the price, in the kernel.**  The good/bad split delivers
  `freq(I_w) ≤ (D/η)·γ(I_w) + ε(η)`, and the factor `D/η` beats any candidate absolute `C`.  So
  the split ALONE cannot produce `OrbitWordBound`: `ImageTight` is rateless, and a rateless error
  cannot pay for a scale-dependent constant.  (Shape statement, not a refutation of the crux.)
* `TailRate y A` (`freq(digit ≥ T) ≤ A/T`) + `imageTight_of_tailRate` — the named missing input.
  It is the `w = []` case of the crux in QUANTITATIVE form.

**NEXT (lap 50) — the fixed-point bootstrap.**  Run the split under `TailRate y A` instead of
`ImageTight`: bad positions at scale `η = 1/(2(T+1)³)` then cost `3A/(T+1) + o(1)` rather than a
rateless `ε`, while the good constant is `D·2(T+1)³`.  Balancing gives a word bound
`freq(I_w) ≤ f(A, γ(I_w))`; specialising it back to `w = [a]`, `a ≥ T`, and summing returns a
tail rate `A' = g(A)`.  If `g` has a fixed point below the trivial bound `A = 1`, the bootstrap
CLOSES the crux with an absolute constant.  Deliverable: state `g` in Lean and decide whether the
loop contracts — a kernel refutation (no contraction) is an equally valid outcome and would
redirect the route to the arithmetic of `Φ` as the directive's fact (γ) demands.

### 2026-09-29 lap 50 — the hit principle is TRUE for window predictors (`VandeheyS7WindowHit.lean`)

The lap-49 "price" analysis pointed at the wrong culprit.  The `1/η` in the split is not the
binding constraint: the binding constraint is the *measure → frequency* step, i.e. the hitting
principle for predictable targets.  `not_predictableHitPrinciple` (lap ~44) refutes it for
arbitrary sequences and arbitrary predictors — but it is TRUE, with an ABSOLUTE constant, when the
predictor reads a finite window and the point is genuinely CF-normal:

* `gaussMeasure_append_le` — quasi-multiplicativity `γ(I_{v++u}) ≤ 8 log 2 · γ(I_v) γ(I_u)`,
  from `volume_cylinder_append_le` plus the two-sided Gauss-density window.
* `windowHit_le` — for a CF-normal `x`, a finite family `V` of length-`k` windows and a target
  word `u(v)` per window with `γ(I_{u(v)}) ≤ m`:
  `∑_{v∈V} freq(I_{v ++ u(v)}) ≤ 8 log 2 · m + ε` eventually.  **No dependence on `k`, on `|V|`,
  or on where the targets sit.**

So the crux would follow with constant `8 log 2` if the transducer state at input time `n` were
a function of the last `k` digits (for `k` large, up to error `ε`).  `no_window_function` says it
is not one EXACTLY; the open point is the APPROXIMATE version, and uniform loss of memory
(`hdist_runWord_le`, rate `(3−2√2)^{⌊k/2⌋}`) is the only candidate mechanism.

**NEXT (lap 51).**  State `ApproxWindowState k δ`: there is a map `F : (words of length k) →
MobState` with `hdist (s_n.mob t) ((F (window n)).mob t) ≤ δ` for all `t ∈ (0,1)`, `n ≥ k`.  Then
(a) prove `orbitWordBound_of_approxWindowState` — the assembly of `windowHit_le` with the
Hilbert-metric comparison (a `δ`-Hilbert perturbation moves the pullback of `I_w` into the
pullback of a slightly enlarged word set, whose mass is `(1+O(δ))γ(I_w)`), and (b) attack
`ApproxWindowState` itself from `hdist_runWord_le` — the honest obstruction is that the
contraction bounds the image DIAMETER, so the remaining question is whether the EMITTED-digit
normalisation `O_n⁻¹` restores location-independence.  A kernel refutation of (b) is as valuable
as a proof, and would finally force the route onto the arithmetic of `Φ` (directive fact γ).

### 2026-09-29 lap 51 — quasi-Bernoulli for arbitrary targets (`VandeheyS7QuasiBern.lean`)

Lap 50's mass bound only covered cylinder targets; the approximate-window route produces
*intervals* `F(v)⁻¹(I_w)`.  Upgraded, via the repo's own correlation-decay theorem
`gaussMeasure_cylinder_mixing` at gap `g = 0`:

* `gaussMeasure_inter_preimage_le` — `γ(I_v ∩ T^{−|v|}A) ≤ (1 + 8 log 2) γ(I_v) γ(A)` for EVERY
  measurable `A ⊆ (0,1)`.  (Strictly generalises `gaussMeasure_append_le`.)
* `gaussMeasure_inter_preimage_Ioo_le` — the interval form
  `γ(I_v ∩ T^{−|v|}(a,b)) ≤ ((1+8log2)/log2) (b−a) γ(I_v)`.

**NEXT (lap 52).**  The one remaining ingredient of an interval-target window-hit theorem is the
FREQUENCY side: CF-normality gives cylinder frequencies, and the hit set `I_v ∩ T^{−k}(a,b)` is
not a cylinder.  Two routes: (i) cell frequencies — along an irrational orbit
`cellSet w T = I_w \ ⋃_{1≤a<T} I_{w++[a]}` exactly, so `blockCount(cellSet w T)` is a finite
signed combination of cylinder counts and CF-normality gives its limit; then `CellCover` covers
the interval with total mass `≤ (1/log2)(b−a)+δ`.  (ii) direct outer approximation of `(a,b)` by
the finitely many length-`n` cylinders meeting it (`sum_gaussMeasure_cfCylinder_meeting_le`
already exists in `VandeheyS7Cell`).  Route (ii) looks shorter and avoids the cell-frequency
build; do it first, then assemble `windowHit_Ioo_le` and finally
`orbitWordBound_of_approxWindowState`.

### 2026-09-29 lap 52 — CF-normality determines CELL frequencies (`VandeheyS7CellFreq.lean`)

Route (i) of lap 51's plan, taken instead of (ii): it has no exceptional set, hence no residue
term to absorb.

* `blockIndic_cellSet_eq` — pointwise on irrationals, `1_{cellSet w T} = 1_{I_w} − ∑_{1≤a<T}
  1_{I_{w++[a]}}` (a point of `I_w` has a genuine digit, which either reaches the threshold or
  equals exactly one sub-threshold `a`).
* `blockCount_cellSet_eq` — the orbit-count form.
* `blockCount_freq_cellSet_of_isCFNormal` — the cell frequency of a CF-normal point converges to
  `γ(I_w) − ∑_{1≤a<T} γ(I_{w++[a]})`.

With `CellCover` (covers an interval by cells, total mass `≤ (1/log2)(b−a)+δ`, ALL irrationals of
the interval covered) and lap 51's quasi-Bernoulli bound for arbitrary targets, the three
ingredients of an interval-target window-hit theorem are now in place.

**NEXT (lap 53).**  Assemble `windowHit_Ioo_le`:
1. the hit-set identity `I_v ∩ T^{−|v|}(cellSet c S) = cellSet (v++c) S` along irrational orbits
   (same shape as `VandeheyS7Boot.mem_cellSet_nil_of_mem_cellSet`);
2. frequency of each hit cell from `blockCount_freq_cellSet_of_isCFNormal` at the word `v ++ c`;
3. mass of each hit cell `≤ (1+8log2) γ(I_v) γ(cellSet c S)` from
   `gaussMeasure_inter_preimage_le`, summed over the cover to `≤ C γ(I_v)(b−a)`;
4. sum over `v ∈ V` with `sum_gaussMeasure_le_one_of_length`.
Then `orbitWordBound_of_approxWindowState` becomes a Hilbert-perturbation argument on top of it,
and `ApproxWindowState` is the last open obligation of the whole route.

### 2026-09-29 lap 53 — the cell mass identity closes the frequency/mass mismatch

Lap 52's cell-frequency limit was the alternating sum `γ(I_w) − ∑_{1≤a<T} γ(I_{w++[a]})`, which
is an upper bound for `γ(cellSet w T)` — the WRONG direction for the assembly, which needs the
limit to be at most the quasi-Bernoulli mass.  `gaussMeasure_cellSet_eq` closes the gap: the two
are EQUAL, because the only points of `I_w` missed by the cell and its sub-threshold extensions
have digit `0` at position `|w|`, hence are rational, hence Gauss-null.  Consequence
`blockCount_freq_cellSet_mass`: the cell frequency of a CF-normal point converges to
`γ(cellSet w T)` itself.

**NEXT (lap 54).**  Unchanged from lap 52's plan, now unblocked: the hit-set identity
`I_v ∩ T^{−|v|}(cellSet c S) = cellSet (v++c) S` along irrational orbits, then `windowHit_Ioo_le`
(frequencies from `blockCount_freq_cellSet_mass`, masses from `gaussMeasure_inter_preimage_le`,
cover from `cellCover_inv_log_two`, window sum from `sum_gaussMeasure_le_one_of_length`).

### 2026-09-29 lap 54 — the hit cell (`VandeheyS7HitCell.lean`)

* `mem_cellSet_append_iff` — along irrationals, `t ∈ cellSet (v ++ c) S ↔ t ∈ I_v ∧
  G^{|v|}t ∈ cellSet c S`.  The window-then-cell event IS a single cell, so CF-normality pins its
  frequency (lap 53) with no extra machinery.
* `cellSet_append_subset` / `gaussMeasure_cellSet_append_le` — `γ(cellSet (v++c) S) ≤
  (1 + 8 log 2) γ(I_v) γ(cellSet c S)`, combining the identity (mod the rational null set) with
  lap 51's quasi-Bernoulli bound.

**NEXT (lap 55).**  `windowHit_Ioo_le`, now pure bookkeeping: for each window `v`, `CellCover`
supplies `F_v` covering the target interval `(a_v,b_v)` with `∑_{c∈F_v} γ(cellSet c) ≤
(1/log2)(b_v−a_v)+δ`; pointwise the orbit's hit implies membership in some `cellSet (v++c₁) c₂`;
`blockCount_freq_cellSet_mass` gives each frequency, `gaussMeasure_cellSet_append_le` each mass,
`sum_gaussMeasure_le_one_of_length` the sum over windows.  Constant
`C = (1+8log2)/log2 ≈ 9.0`.

### 2026-09-29 lap 55 — `windowHit_Ioo_le` LANDED (`VandeheyS7HitIoo.lean`)

The interval-target window-hit theorem is proved, axiom-clean:

* `blockCount_hit_Ioo_le` — per window: `freq{ n : Gⁿx ∈ I_v ∧ G^{n+|v|}x ∈ (a,b) } ≤
  (1+8log2)((b−a)/log2 + δ) γ(I_v) + δ`.
* `windowHit_Ioo_le` — summed over a same-length window family:
  `≤ (1+8log2)/log2 · L + ε`, where `L` bounds the target interval lengths.
  **The constant ≈ 9.0 is absolute** — independent of the window length `k`, of the number of
  windows, and of where the targets sit.

So the crux `OrbitWordBound` now has a complete proof MODULO one hypothesis: that the transducer
state at input time `n` is, to accuracy `ε`, a function of the last `k` input digits.  Everything
else — the covering, the quasi-Bernoulli masses, the cell frequencies, the window sum — is in the
kernel.

**NEXT (lap 56).**  Define `ApproxWindowState` and prove `orbitWordBound_of_approxWindowState`:
given `F : (length-k words) → MobState` with the state's action `δ`-close to `F(window)`'s on
`(0,1)`, the output-word event `G^ℓ y ∈ I_w` at the times matched by the clock pulls back to
`G^n x ∈ (F(window))⁻¹(I_w)` up to a `δ`-collar; the collar's frequency is `O(δ)` by
`windowHit_Ioo_le` applied to the two collar intervals, and the main term is one more application
with `L = |(F v)⁻¹(I_w)| ≤ distortion · γ(I_w)/η` (lap 49).  Then `ApproxWindowState` itself is
the single remaining open obligation of Vandehey §7 Problem 1 on this route.

### 2026-09-29 lap 56 — the ergodic side is FINISHED (`VandeheyS7Reduction.lean`)

* `WindowedPullback q r₀ Λ` — the one remaining hypothesis, purely about the machine: for a
  CF-normal input and an image word `w`, the image orbit's visits to `I_w` are, up to frequency
  `ε`, matched by input times at which the input lies in an interval **determined by the last `k`
  input digits** and of length `≤ Λ γ(I_w)`.
* `orbitWordBound_of_windowedPullback : WindowedPullback q r₀ Λ → OrbitWordBound q r₀
  ((1+8log2)/log2 · Λ)` — the crux, discharged from it.
* `vandeheyS7_mul_phi_of_windowedPullback` / `..._add_phi_...` — the frozen §7 targets on three
  inputs: the cited `GaussACRigidity`, `ImageTight` on the image, and `WindowedPullback`.

Compare lap 47 (three hypotheses, the crux an ergodic statement about a moving target).  The
whole ergodic side — covering, quasi-Bernoulli masses, cell frequencies, the window sum, the
absolute constant — is now in the kernel, and the open obligation is a statement about the
`φ`-transducer only.

**NEXT (lap 57).**  Attack `WindowedPullback` itself.  Its three components, in order of risk:
(a) the interval per window is `(F v)⁻¹(I_w)`, with `|·| ≤ distortion · γ(I_w)/η` by lap 49 —
needs the bad-position frequency of lap 48 to make `η` legitimate;
(b) the state must be a window function up to `δ` — `no_window_function` refutes the EXACT
version, `hdist_runWord_le` is the only candidate mechanism for the approximate one, and the
honest question is whether the emitted-digit normalisation `O_n⁻¹` restores location-independence;
(c) the clock: input times vs output positions, `RunClock` rate `≈ 1` (`VandeheyS7Clock`).
(b) is the decisive one; a kernel refutation there would force the route onto the arithmetic of
`Φ` as directive fact (γ) demands.

### 2026-09-29 lap 57 — the SHAPE is a window function, the LOCATION is not (`VandeheyS7Shape.lean`)

Attacking `WindowedPullback`'s decisive component: is the transducer target window-determined?
Answer, made precise:

* `MobState.mob_ratio_near_affine` — a Möbius state distorts RELATIVE lengths inside an interval
  of length `ε` by at most `1 + distortion·ε`, two-sided.  Exact algebra: the ratio is
  `((cβ+d)(cα+d))/((cv+d)(cu+d))`, and all four points lie in `[α,β]`.
* `mob_ratio_near_affine_le` + `tendsto_windowShapeError` — a state reading a depth-`k` cylinder
  (length `≤ 2/2ᵏ`) with distortion `≤ K` distorts relative lengths by `1 + 2K/2ᵏ → 1`.

**So the length coordinate of the target IS window-determined, uniformly in the prefix; the
location coordinate is the entire remaining content of `WindowedPullback`.**  That matches
`no_window_function` exactly (it refutes location-determinacy, not shape-determinacy) and
explains why laps 38–47's diameter bounds never sufficed.

**NEXT (lap 58) — the newly visible option.**  Restate the crux so that only relative lengths
enter.  Concretely: in `WindowedPullback`, replace "an interval `(A v, B v)` determined by `v`"
by "an interval of LENGTH `≤ Λ γ(I_w)` whose location is arbitrary", and ask what the window-hit
theorem gives then.  `windowHit_Ioo_le` as proved needs the location (it feeds `A v, B v` into
the cover), so the honest first probe is whether a location-free variant is TRUE: does a
CF-normal orbit satisfy `freq{n : G^{n+k}x ∈ J_n} ≤ C·|J| + ε` for every predictable family of
intervals of length `≤ |J|` with ARBITRARY location?  `not_predictableHitPrinciple` suggests not
in general; the question is whether the length-`k` window structure saves it.  A kernel answer
either way is lap 58's deliverable.

### 2026-09-29 lap 58 — the lap-58 probe is ANSWERED, and the attack moves to `ℤ[φ]` (`VandeheyS7Lattice.lean`)

**The probe (location-free hit principle) is dead, and for a reason no structure can repair.**
Let `J_n` be predictable from `x₁…x_n` with a gap `k` before the observation `G^{n+k}x`.  Fix any
`x` at all: the prefixes `x₁…x_n` are pairwise distinct, so the *function* `F_n` may be defined to
send that one word to the length-`δ` interval centred at `G^{n+k}x` (and anywhere else off it).
That is a legitimate predictable family with hit frequency `1`.  So "predictable + small +
CF-normal" carries **zero** information about the hit frequency no matter how large the gap `k`
is: only finiteness of the predictor's range (a *window* predictor) can help, and that case is
already proved (`windowHit_Ioo_le`).  Do not re-open this; the directive's fact (γ) — the
arithmetic of `Φ` — is genuinely forced.

**So this lap attacked the arithmetic.**  New module `VandeheyS7Lattice.lean`, all axiom-clean:

* For the additive instance `Φ = [[1,φ],[0,1]]` with `O_n, P_n ∈ SL₂(ℤ)`, every entry of the state
  `s_n = O_n⁻¹ Φ P_n` lies in `ℤ[φ]` and `det s_n = 1`: **the state is a point of the Hilbert
  modular group `SL₂(ℤ[φ])`**, not just of `SL₂(ℝ)`.  That is the structure the route has never
  used.
* `one_le_abs_zval_mul_zconj` / `abs_zval_ge_inv_abs_zconj` — `|ξ|·|ξ'| ≥ 1` for `0 ≠ ξ ∈ ℤ[φ]`.
* `dist_rat_ge` — `|ξ − p/q| ≥ 1/(q·|qξ' − p|)`.
* `abs_zconj_sub_rat_ge` — **Galois repulsion**: `|ξ − p/q| ≤ δ` forces
  `|ξ' − p/q| ≥ 1/(q²δ)`.  Hugging a rational costs conjugate height at the reciprocal rate.
* `zquot_sub_rat_ge` — the form the state needs: an image endpoint is a quotient `β/δ` of
  `ℤ[φ]`-numbers, and `|β/δ − p/q| ≥ 1/(q·|δ|·|qβ' − pδ'|)`.  **A bad state is expensive**: a
  state whose image straddles `1/k` at scale `≪ γ(I_w)` must sit far out in the *second*
  archimedean factor.
* `abs_coeff_le_of_bounded`, `finite_bounded_zPairs` — bounded together with its conjugate ⟹
  finitely many.  So states bounded in *both* factors form a finite set; discreteness, from the
  arithmetic side, of what `no_window_function` refutes dynamically.

**The honest accounting this buys, and the next attack.**  The conjugate component of `s_n` is
`≍ q_ℓ(y)·q_n(x)`, i.e. `e^{Θ(n)}`.  So the repulsion bound forbids badness at scale `δ` only for
`n ≲ log(1/δ)` — it does **not**, by itself, bound the frequency of bad times, and lap 59 must not
expect it to.  What it does give is the right frame: *bad time at scale `δ`* is a Diophantine
coincidence between the `ℤ[φ]`-lattice point `s_n` and a rational `p/q` with `q ≲ 1/δ`, and the
crux's bad half is now the **counting** question "how many `n < N` admit such a coincidence".
That is a lattice-point count in `SL₂(ℤ[φ])` (a Hilbert-modular/Duke-type count), not an ergodic
statement about a moving target — a different and better-posed wall than the self-joining one.
Lap 59: formalise the count's *statement* (`BadTimeCount`), and try the easy half — an upper bound
for a single `q` via the repulsion bound plus the exponential growth of `q_n`.

### 2026-09-29 lap 59 — the lap-58 probe, now in the kernel (`VandeheyS7Gap.lean`)

Lap 58's prose argument is a theorem, at **every** gap `k`:

* `exists_predictor_all_hit` — for any sequence `u`, any width `δ > 0` and any gap `k`, the
  predictor `F l := u (l.length + k) − δ/2` reads only the prefix `u₀…u_{n−1}` and yet its
  announced interval of width `δ` contains `u_{n+k}` for every `n`.  Hit frequency `1`.
* `not_gappedHitPrinciple k` — so the gapped principle fails against a sequence with *perfect*
  marginals (`cycGrid 10`, `δ = 1/2`): frequency `1` where it allows `6/10`.

**Consequence, and it is a route fact:** "predictable + narrow + CF-normal orbit" carries zero
information about hit frequency, for any gap.  Only *finiteness of the predictor's range* helps,
and that case is already proved (`windowHit_Ioo_le`).  So the location-determinacy demanded by
`WindowedPullback` is not an artefact of the statement — it is its entire content, and no
re-statement of the ergodic side can dodge it.  `VandeheyS7Lattice` is the live attack.

### 2026-09-29 lap 60 — a bad state is priced (`VandeheyS7Bad.lean`)

Directive fact 2's bad state, priced from the arithmetic instead of assumed away:

* `conj_comb_ge_of_close` — an endpoint `β/δ` within `δ₀` of `p/q` forces
  `|qβ′ − pδ′| ≥ 1/(q·|δ|·δ₀)`.
* `conjHeight_ge_of_bad` — for an endpoint in `[0,1]` and `δ₀ ≤ 1`, the **conjugate height**
  `max(|β′|,|δ′|)` of the state's entries is `≥ 1/(3q²·|δ|·δ₀)`.  Badness at scale `δ₀` against a
  denominator-`q` rational costs conjugate height at the reciprocal rate.

Both axiom-clean.  This converts the crux's bad half from a refuted-as-soft ergodic statement into
a **lattice-point count** in `SL₂(ℤ[φ])`.

**NEXT (lap 61).**  Name the count.  Define `BadTime x n δ₀ q` (the state at input time `n` is
`δ₀`-bad against some `p/q`), and state `BadTimeCount`: `#{n < N : ∃ q ≤ 1/δ₀, BadTime …} ≤ C δ₀ N`.
Then attack the *single-`q`* case first, where `conjHeight_ge_of_bad` plus the exponential growth
of `q_n(x)` should give an honest upper bound on the number of admissible `n` in a dyadic block —
and if it does not, record which half of the exponent defeats it, since that is the number the
whole route now turns on.

### 2026-09-29 lap 61 — the bad set has measure `√δ`, not `δ` (`VandeheyS7BadSet.lean`)

Before counting bad times, calibrate the target.  `badSet δ = {x ∈ (0,1) : |x − 1/k| < δ for some
k ≥ 1}` is the set of positions where directive fact 2's distortion failure happens, and

* `volume_badSet_le` : `|B(δ)| ≤ 6√δ` for `0 < δ ≤ 1`, axiom-clean.

The exponent is `1/2`, not `1`: the endpoints `1/k` accumulate at `0`, so `B(δ)` swallows an
interval of length `≈ √δ` there, and the `K = ⌈δ^{−1/2}⌉` separated intervals contribute another
`2δK ≈ 2√δ`.  The two terms genuinely trade off — dropping the accumulation term would leave a
bound minimised at `K = 1`.

**Route consequence.**  Any bad-state budget must be written in `√δ`.  This is still enough for the
ε-scheme (the bad frequency need only tend to `0` with the scale), but a lap that writes `C·δ` is
off by an unbounded factor and will read as a spurious contradiction.  Lap 60's plan to count bad
times is hereby calibrated; lap 62 should state `BadTimeCount` with the `√` in it from the start.

### 2026-09-29 lap 62 — the lap-48 bad set is small, unconditionally (`VandeheyS7BadMass.lean`)

Joining lap 61's measure estimate to lap 48's `nearInv η` (the set where bounded distortion
fails):

* `measurableSet_nearInv`, `volume_nearInv_le` : `|nearInv η| ≤ 7√η`;
* `gaussMeasure_nearInv_le` : `γ(nearInv η) ≤ 7√η / log 2`.

Both axiom-clean and **unconditional** — no `ImageTight`.  Compare `exists_nearInv_freq_le`, which
buys the same smallness in *frequency* at the cost of the chain's second hypothesis.  So the split
is now exact: the **measure** half of "bad states are rare" is free; the **measure → frequency**
half is the whole cost, and `not_gappedHitPrinciple` says that half cannot be soft.

**NEXT (lap 63).**  Try to make the frequency half unconditional too, for the INPUT orbit, where
CF-normality is a hypothesis we hold: cover `nearInv η` by the `K = ⌈η^{−1/2}⌉` intervals plus
`(0, 1/K + η)` (the covering is already written), push each through the cell cover
(`cellCover_inv_log_two`, the same route `windowHit_Ioo_le` uses for a single interval), and sum.
That gives `freq{n : Gⁿx ∈ nearInv η} ≤ C√η + ε` for CF-normal `x` with no second hypothesis — and
would remove `ImageTight` from lap 48's separation step, leaving it needed only on the IMAGE.

### 2026-09-29 lap 63 — interval frequencies, unwindowed (`VandeheyS7IooFreq.lean`)

* `blockCount_freq_cellSet_nil` — the nil-word case `blockCount_freq_cellSet_mass` was missing
  (it needed `w ≠ []` only to call `blockCount_freq_of_isCFNormal`; for `w = []` the cylinder is
  `(0,1)` and the frequency is `1`).  With it, **every** cell of a cover has a frequency.
* `blockCount_Ioo_le` — hence for a CF-normal `x` and any `(a,b) ⊆ [0,1]`,
  `freq{n : Gⁿx ∈ (a,b)} ≤ (b−a)/log 2 + 2δ`.  No window, absolute constant, axiom-clean.

This is the unwindowed companion of `windowHit_Ioo_le` and it is what lap 64 needs.

**NEXT (lap 64).**  `blockCount_nearInv_freq_le`: sum `blockCount_Ioo_le` over the `K+1` intervals
of lap 62's covering (`K = ⌈η^{−1/2}⌉`, each clipped to `[0,1]`, total length `≤ 7√η`) with
`δ = ε/(2(K+1))`, to get `freq{n : Gⁿx ∈ nearInv η} ≤ 7√η/log 2 + ε` for CF-normal `x`,
**unconditionally**.  That discharges the INPUT half of lap 48's bad-position control, leaving
`ImageTight` needed only on the image.

### 2026-09-29 lap 64 — the bad set is rare for the input orbit, unconditionally

Added to `VandeheyS7IooFreq.lean`, all axiom-clean:

* `blockCount_inter_Ioo` — orbit points lie in `(0,1)`, so a target may be clipped for free.
* `blockCount_Ioo_le'` — interval frequencies for **any** `a ≤ b` (unclipped).
* `blockCount_nearInv_freq_le` — **the payoff**: for CF-normal `x`, `0 < η ≤ 1` and any `ε > 0`,
  `freq{n : Gⁿx ∈ nearInv η} ≤ 7√η/log 2 + ε`, with **no second hypothesis**.

Compare `exists_nearInv_freq_le` (lap 48), which bought the same smallness by spending the chain's
`ImageTight`.  The INPUT half of lap 48's bad-position control is now discharged; `ImageTight`
survives only where it must, on the IMAGE orbit, where CF-normality is the conclusion rather than
a hypothesis.

**NEXT (lap 65).**  Two live threads, take the first:
1. Re-run lap 48's separation step (`VandeheyS7Sep`, `exists_nearInv_freq_le`'s consumers) on the
   new unconditional bound and see how far up the chain the removal of `ImageTight` propagates —
   if `WindowedPullback`'s exceptional set can be stated with input-side badness only, the chain
   loses a hypothesis outright.
2. Back to the arithmetic (`VandeheyS7Lattice`/`VandeheyS7Bad`): the bad-time count.

### 2026-09-29 lap 65 — anchored targets escape the refutation (`VandeheyS7Anchor.lean`)

Thread 1 of lap 64 first, honestly: `exists_nearInv_freq_le` is applied to the **image** orbit, so
lap 64's unconditional input-side bound does not remove `ImageTight` from the chain by
substitution.  But chasing why produced the better result.

**The observation.**  A transducer state acts by a *monotone* Möbius map, so the pullback of an
output event "the next output digit is large" (`= cellSet [] T`, i.e. exactly what `ImageTight`
talks about) is **downward-closed** in `(0,1)` — anchored to an endpoint, not free-floating.  And:

* `subset_Ioc_of_downwardClosed` — a downward-closed `A ⊆ (0,1)` with `|A| ≤ c` satisfies
  `A ⊆ (0,c]`.  Monotonicity converts a measure bound into *containment in a fixed interval*.
* `anchoredHitCount_le`, `anchoredHitFreq_le` — hence for CF-normal `x` and **any** predictable
  family of endpoint-anchored targets with `u n ≤ c`, `v n ≥ 1 − c`:
  `freq{n : Gⁿx < u n ∨ Gⁿx > v n} ≤ 2c/log 2 + ε`.  All axiom-clean.

**The route fact this establishes.**  The two obligations of the §7 chain are *not* two instances
of one difficulty:

| half | pullback | status |
|---|---|---|
| tail cell / large digit (`ImageTight`, directive fact 2's bad states) | endpoint-anchored | soft — `anchoredHitFreq_le` |
| general word `I_w` (the crux) | interior, free location | refuted soft — `not_gappedHitPrinciple` |

So `ImageTight` is the *reachable* hypothesis, and the crux is the genuinely hard one — which is
where the directive already points.

**NEXT (lap 66).**  Cash the anchored principle: prove `ImageTight (Int.fract (q*x+r₀))` from
(i) the state's monotonicity, (ii) the length bound on the pullback of `(0,1/T)` (lap 49's
`sub_le_of_image_le` with the distortion bound), (iii) `anchoredHitFreq_le`, and (iv) the clock.
If it lands, the §7 chain drops from three hypotheses to two.

### 2026-09-29 lap 66 — `ImageTight` reduces to an ANCHORED pullback (`VandeheyS7Tight3.lean`)

The anchored principle is cashed:

* `AnchoredPullback q r₀ Λ` — the image orbit's visits to the tail cell `cellSet [] T` are, up to
  frequency `ε`, matched by input times at which the input lies below its own lower threshold or
  above its own upper one, both within `Λ/T` of the endpoint.
* `imageTight_of_anchoredPullback : AnchoredPullback q r₀ Λ → ImageTight (fract (q x + r₀))` for
  every CF-normal `x`.  Axiom-clean.

**Why this is strictly weaker than `WindowedPullback`.**  `WindowedPullback` must name an interval
*determined by the last `k` input digits* — location-determinacy, which `no_window_function`
refutes exactly and `not_gappedHitPrinciple` shows cannot be softened.  `AnchoredPullback` names no
window, lets the thresholds depend on `n` arbitrarily, and constrains only their *size*.  That
freedom is legitimate only because the tail-cell target is endpoint-anchored (lap 65), and the size
`Λ/T` is what bounded distortion already supplies.

So the §7 chain's second obligation has moved from an assumption about the image to a soft
statement about the machine.

**NEXT (lap 67).**  Build a witness for `AnchoredPullback` from the repo's transducer layer:
(a) the state's monotonicity (`MobState.mob` is monotone in `t` — sign of `ad − bc`), so the
pullback of `(0,1/T)` is downward- or upward-closed;
(b) `sub_le_of_image_le` / `spread_runWord_le` for the `Λ/T` size, with the distortion bound;
(c) the clock (`VandeheyS7Clock`) to match output positions to input times.
(a) is the piece to formalise first, and it is elementary: `mob_strictMono_or_strictAnti`.

### 2026-09-29 lap 67 — the state is monotone, so its pullbacks are anchored (`VandeheyS7Mono.lean`)

The structural input lap 66 named, proved from algebra with no calculus:

* `mob_sub_mob` — `s.mob t₂ − s.mob t₁ = (ad − bc)(t₂ − t₁)/((ct₂+d)(ct₁+d))` for `0 ≤ t₁,t₂`.
* `mob_lt_mob_of_det_pos` / `..._neg` — strict monotonicity on `[0,∞)`, sense given by `det`.
* `downwardClosed_mob_lt`, `upwardClosed_mob_lt`, `anchored_mob_lt` — hence the sublevel set
  `{t ∈ (0,1) : s.mob t < r}` is downward-closed or upward-closed: **every** state's tail-cell
  pullback is anchored to an endpoint.  All axiom-clean.

**NEXT (lap 68).**  Mirror `subset_Ioc_of_downwardClosed` for upward-closed sets
(`subset_Ico_of_upwardClosed`), then package: state + measure bound on the pullback ⟹ the pullback
lies in `(0,c]` or `[1−c,1)`, i.e. exactly an `AnchoredPullback` threshold pair.  After that the
only gaps to a witness are the size bound `Λ/T` (lap 49's `sub_le_of_image_le`) and the clock.

### 2026-09-29 lap 68 — the anchoring is packaged

* `subset_Ico_of_upwardClosed` (in `VandeheyS7Anchor`) — the mirror of lap 65's lemma.
* `MobState.mob_pullback_anchored` (in `VandeheyS7Mono`) — **the packaging**: a state plus a
  measure bound `≤ c` on its tail-cell pullback puts that pullback inside a *fixed* interval at one
  end, `(0,c′)` or `(1−c′,1)` for any `c′ > c`.  Exactly an `AnchoredPullback` threshold pair.
  Axiom-clean.

So the remaining gaps between the repo and a witness for `AnchoredPullback` — and hence to
discharging `ImageTight` outright — are now only two, both already named in the repo:
1. the **size** bound: `volume (state pullback of (0,1/T)) ≤ Λ/T`, which is lap 49's
   `sub_le_of_image_le` with the distortion bound `≤ 4` (`VandeheyS7Distortion`);
2. the **clock**: matching output positions to input times (`VandeheyS7Clock`, rate `≈ 1`).

**NEXT (lap 69).**  Item 1: state and prove `volume_mob_preimage_le` — for a `MobState` of
distortion `≤ K` whose image has width `≥ η`, the pullback of an output interval of length `L` has
length `≤ K·L/η`.  The pieces are in `VandeheyS7Distortion`/`VandeheyS7Good`; this is the
assembly into the measure form `mob_pullback_anchored` consumes.

### 2026-09-29 lap 69 — the size bound (`MobState.mob_sublevel_subset`)

Gap 1 of lap 68 is closed, and closed in a better form than planned — no measure theory at all:

* `mob_zero_nonneg`, `mob_one_nonneg` — the image stays in `[0,∞)` (from the structure's sign
  fields).
* `mob_sublevel_subset` — for a state of image width `≥ η` and any `r ≥ 0`, the sublevel set
  `{t ∈ (0,1) : s.mob t < r}` is contained in `(0, D·r/η]` or in `[1 − D·r/η, 1)`, `D` the
  distortion.  Axiom-clean.

The proof is lap 49's `sub_le_of_image_le` applied to the *anchored endpoint pair* — `(0,t)` in the
increasing case, `(t,1)` in the decreasing one — which is available precisely because lap 67 made
the state's monotonicity explicit.  So the containment is derived directly, without going through
`volume` and `mob_pullback_anchored`'s measure hypothesis.

This is exactly `AnchoredPullback`'s `Λ/T` with `Λ = D/η` and `r = 1/T`.

**NEXT (lap 70).**  Gap 2, the clock: match output positions `ℓ` to input times `n` so that a
visit of the image orbit to `cellSet [] T` is a visit of the input orbit to a sublevel set of the
state at time `n` (`VandeheyS7Clock`, `VandeheyS7Emit`).  With that, `AnchoredPullback` has a
witness modulo the image-width floor `η`, and the floor is itself the bad-state question — but now
only for the TAIL half, where lap 65's principle applies.

### 2026-09-29 lap 70 — `AnchoredPullback` from a state clock (`VandeheyS7Clock2.lean`)

* `MobState.exists_thresholds` — lap 69's containment in the `(u,v)` form `anchoredHitCount`
  consumes (with the degenerate `u = 1, v = 0` branch when the size bound exceeds `1`).
* `StateClock q r₀ η K` — the remaining obligation, isolated: a sequence of states of width `≥ η`
  and distortion `≤ K` matching the image orbit's tail-cell visits to input times at which
  `Gⁿx` lies in `{t : (s n).mob t < 1/T}`.  **No location claim, no window, no measure** — it is
  the defining property of a transducer plus a width floor.
* `anchoredPullback_of_stateClock : StateClock q r₀ η K → AnchoredPullback q r₀ (2K/η)`.
  Axiom-clean.

Chained with lap 66: `StateClock → AnchoredPullback → ImageTight`.  So the chain's second
hypothesis is now downstream of a statement with no ergodic content at all.

**NEXT (lap 71).**  Build `StateClock` itself from the repo's transducer layer
(`VandeheyS7Emit`, `VandeheyS7Clock`, `VandeheyRunClock`).  Two sub-obligations, in order:
(a) the state-orbit identity — the output point at the matched position IS `(s n).mob (Gⁿx)`;
(b) the width floor `η`, which is the *tail* half of the bad-state question and therefore now
falls under lap 65's anchored principle rather than under the refuted soft route.

### 2026-09-29 lap 71 — the width floor is a fixed point, and the coefficient is all of it (`VandeheyS7Fix.lean`)

`StateClock`'s only non-bookkeeping content is the width floor `η`.  Tracing where it comes from
closes a loop, and the loop is now priced in the kernel:

* the floor fails exactly when the image orbit visits `nearInv η` (`width_ge_of_mem_of_far`);
* lap 48's `blockCount_nearInv_le` bounds those visits **unconditionally**, but by
  `3 · freq(cellSet [] (T+1))` — three times the tail frequency `ImageTight` is about;
* so `StateClock → AnchoredPullback → ImageTight` gives `x ≤ b + λ x` with `λ = 3`.

* `le_div_of_self_le_add` — with `0 ≤ λ < 1` the loop closes: `x ≤ b/(1−λ)`.
* `no_bound_of_one_le_coeff`, `tailBootstrap_coeff_three_gives_no_bound` — with `λ ≥ 1` it bounds
  nothing, and that is a witness, not a gap in the search.

**So the whole of the remaining tail obligation is the coefficient.**  Two attacks, and the second
is the one that does not loop:

1. charge bad times *injectively* to tail-cell times (`λ = 1`) and gain the rest from the free
   scale separation between the floor `η` and the threshold `T` — i.e. lap 49's `TailRate`;
2. **a width floor that is not routed through the image at all.**  The state's width is an
   arithmetic quantity: for the additive instance it is controlled by the `ℤ[φ]` denominator entry
   (`VandeheyS7Lattice`), so a lower bound on it is a *height* statement about `SL₂(ℤ[φ])` points.
   Directive fact (γ) again, and the only non-circular route.

**NEXT (lap 72).**  Attack 2: relate `MobState.width` to the `ℤ[φ]` entries — `width = |det| /
((c+d)d)`, so a width floor is exactly an upper bound on the denominator entries' size, i.e. a
height bound on the state as a lattice point.  Prove the identity first; it is elementary and it
is what lets `VandeheyS7Lattice`'s finiteness/repulsion results speak about widths.

### 2026-09-29 lap 72 — the width is arithmetic (`VandeheyS7Width.lean`)

Attack 2 of lap 71, landed:

* `width_eq` — `width s = |ad − bc| / ((c+d)·d)`, an identity;
* `width_eq_det_div` — equivalently `|det| / (distortion · d²)`;
* `width_ge_of_height` — so a width floor **is** a height bound: a lower bound on `|det|` plus an
  upper bound on `distortion · d²` gives one;
* `width_ge_of_zdet` — and for the additive instance, where `det = m₁ + m₂φ ∈ ℤ[φ]`, Galois
  repulsion supplies the determinant half for free:
  `width ≥ 1 / (|m₁ + m₂ψ| · distortion · d²)`.  **A width floor with no ergodic input.**

All axiom-clean.  The tail obligation of the §7 chain is now a lattice-height statement about
`SL₂(ℤ[φ])` points — the shape directive fact (γ) asks for, and, unlike the lap-71 bootstrap, one
that never mentions the image orbit.

**NEXT (lap 73).**  The height bound itself: for the additive instance the state is
`s_n = O_ℓ⁻¹ Φ P_n`, so `d` and `det′` are explicit in `q_ℓ(y)`, `q_n(x)` and `√5`.  Write those
two quantities out (`d = q_{ℓ−1}(y)·(p_n + φ q_n) − …`, `det = 1` for the shear, so `|det′| = 1`!)
— note the shear has determinant `1` exactly, which makes `width_ge_of_zdet` read
`width ≥ 1/(distortion · d²)` with no conjugate at all.  The remaining question is then purely
`d = O(1/√η)`, i.e. the state's denominator entry does not grow — which is a statement about the
CLOCK staying synchronised, not about equidistribution.

### 2026-09-29 lap 73 — the unimodular case: width floor **=** height bound

For the additive instance `det Φ = 1` and the convergent matrices are unimodular, so `|det| = 1`
and the conjugate drops out of lap 72's bound entirely.  What is left is an equivalence:

* `width_eq_of_det_one` — `width = 1/((c+d)·d)`;
* `width_ge_of_det_one_of_height` — `(c+d)·d ≤ H ⟹ width ≥ 1/H`;
* `height_le_of_width_ge` — **and conversely** `width ≥ η ⟹ (c+d)·d ≤ 1/η`.

So nothing is lost in the reduction: `StateClock`'s width floor *is* the statement that the
state's denominator entries stay bounded.  And since `s_n = O_ℓ⁻¹ Φ P_n` with `O_ℓ ≈ Φ P_n` (that
is what the emitted matrix tracks), bounded entries is precisely **the clock staying
synchronised** — a bookkeeping statement about the transducer's run, not an equidistribution one.

**NEXT (lap 74).**  Prove synchronisation: `‖O_ℓ⁻¹ Φ P_n‖ = O(1)` along the run, from
`VandeheyS7Emit`'s emission rule (the machine emits precisely while the image is inside a
cylinder, which is what keeps `O_ℓ` tracking `Φ P_n`).  That is the last piece of `StateClock`, and
with it the §7 chain drops to two hypotheses: `GaussACRigidity` (cited) and the crux
`WindowedPullback`.

## Lap 75 (2026-09-29) — S7-BD landed, and S7-WF is a PIGEONHOLE

**S7-BD** (`VandeheyS7Decomp`, commit `facfb1d`): the block decomposition (BD), the inverse clock,
the tick→every-time interpolation `freq_le_of_clock`, the named residual `BlockAverageBound`, the
reduction `freq_le_of_blockAverage`, and the bridge `integral_blockHitCount_le` showing the
**γ-average** of the in-block hit count already meets the crux's constant.  The crux's residual is
therefore exactly "empirical block average = expected block average for a predictable family",
= directive fact (α).

**S7-WF** (`VandeheyS7WidthFreq`): *the frequency form of the width floor needs NO ergodic input.*
Block lengths telescope to the clock (`sum_blockLength`: `Σ_{n<p} Lₙ = N p`), so
`L · #{n<p : Lₙ ≥ L} ≤ N p` — Markov with no measure (`card_longBlock_le`).  With a clock rate
`N p ≤ Λ p`, `freq{Lₙ ≥ L} ≤ Λ/L` (`freq_longBlock_le`), and via the named geometric input
`NarrowForcesBlock` (the CONVERSE of lap 74's `fib_sq_mul_width_le_of_forced`: a state too narrow
to emit has fallen `log(1/width)` behind, and the next input digit pays it back as one long block),
`freq{n : width(sₙ) < η} ≤ Λ/L(η) → 0` (`freq_narrow_le`, `narrow_freq_tendsto_zero`).

Nine laps had treated the width floor as needing new ergodic input; it needs only the clock's own
budget.  Lap 74: a width floor CAPS the block length.  Lap 75: the block-length budget FORCES the
width floor in frequency.  Same hypothesis, both directions now in the kernel.

### Residual after lap 75

1. **`BlockAverageBound`** — fact (α), the open heart.  The ONLY remaining measure-theoretic debt.
2. **`NarrowForcesBlock`** — geometric, named, unconditional-looking: needs the emitter's
   "cannot emit ⟹ image straddles a boundary 1/k, and width < η ⟹ the straddle is at depth
   ≳ log(1/η)" made precise for the actual Raney states.  Next lap's target.
3. **The clock rate `N p ≤ Λ p`** — a Lévy-type bound on the image expansion.  The counting side
   already supplies tail control freely (`tailFreq_le_of_levyBound`); check whether it gives this.
4. **`BlockCoupling`** for the actual transducer — bookkeeping, not mathematics.

### Lap 75 addendum — S7-LAG: lap 75's own bridge was the wrong shape

`VandeheyS7Lag` **corrects** lap 75's `NarrowForcesBlock`.  That hypothesis ("width(sₙ) < η ⟹
Lₙ ≥ L", the burst at the SAME input time) is not what the geometry delivers: a state too narrow to
emit straddles a boundary `1/k`, and the next input digit shrinks `J` without necessarily moving it
off the boundary, so the state can stay narrow *and silent* for several input times before the burst.
`freq_narrow_le` is a true theorem about a hypothesis the transducer does not satisfy in that form.

The correct bridge is amortized, and is now in the kernel:

* `MobState.deficit s = -log (width s)` — the emitter's lag; `deficit_nonneg` when `width ≤ 1`.
* `MobState.lt_width_iff_deficit` — narrowness *is* large lag, exactly.
* `card_gt_le_sum_div` — Markov for a nonnegative sequence.
* `freq_narrow_le_of_lag` / `narrow_freq_tendsto_zero_of_lag` — **from the single hypothesis
  `Σ_{n<p} deficit(sₙ) ≤ Λ p` ("the emitter's lag is O(1) on average")**,
  `freq{n : width(sₙ) < η} ≤ Λ / log(1/η) → 0`, uniformly in `p`.  This is the directive's
  frequency form, from a hypothesis strictly weaker than `NarrowForcesBlock` and of the right shape.
* `deficit_telescope_le` — `c·N p ≤ deficit(s₀) + Σ_{n<p} ξ n` when each step raises the lag by
  `≤ ξ n` and lowers it by `≥ c` per emitted digit.  This is simultaneously the clock rate
  `N p ≤ Λ p` that `freq_longBlock_le` wants, and the reason handoff idea 3 bites:
  `ξ n ≍ 2 log a_{n+1}` for the Raney transducer, and CF-normality does **not** bound
  `(1/p) Σ log a`.  So the clock rate is a genuine residual.

### Residual after the lap-75 addendum

1. **`BlockAverageBound`** — fact (α), the open heart, the only measure-theoretic debt.
2. **`Σ deficit ≤ Λ p`** (average lag) and the per-step inequality `hstep` for the Raney states —
   both geometry of `Φ` and the emission rule; the shapes are now fixed by `deficit_telescope_le`.
3. **`BlockCoupling`** for the actual transducer — bookkeeping.

### Lap 75, third commit — S7-RD: the read's price on the lag, two-sided and exact

`VandeheyS7Read` discharges the `ξ n` of `deficit_telescope_le` into real geometry, with no slack:

* `MobState.readWidth_eq` — the exact post-read width
  `|det|·(1/(a(a+1))) / ((c/a+d)(c/(a+1)+d))`.
* `MobState.read_den_bounds` — the denominator product is squeezed in `[d², (c+d)²]`.
* `MobState.readWidth_le` — `readWidth a ≤ distortion·width/(a(a+1))`, **attained at `c = 0`**.
* `MobState.readWidth_ge` — `width/(distortion·a(a+1)) ≤ readWidth a`, also attained.  Two-sided,
  so a read can never OVERpay the lag and no slack accumulates along the orbit.
* `MobState.deficit_read_le` — the lag form:
  `deficit(after reading a) ≤ deficit(before) + log(a(a+1)) + log distortion`.

So `ξ n = log(a_{n+1}(a_{n+1}+1)) + log K ≍ 2 log a_{n+1}`, exactly as `deficit_telescope_le`
predicted, and the clock rate `N p ≤ Λ p` requires `(1/p) Σ log a` bounded — which CF-normality
does not give (handoff idea 3).  **That is now a kernel-grounded statement about the route, not a
heuristic**: the clock rate is a genuine residual, and the CF-normal `x` with `a_{k!} = 2^{k!}`
is a live candidate to refute it.

### Residual after lap 75 (three commits)

1. **`BlockAverageBound`** — fact (α), the open heart; the only measure-theoretic debt.
2. **The clock rate `N p ≤ Λ p`** — now known to be equivalent to a Cesàro bound on `log a`,
   which CF-normality does NOT supply.  Either the emission gain `2 log fib(L+1)` absorbs it
   (the burst pays for itself: a large `a` costs `2 log a` of lag and immediately buys
   `L ≍ 2 log a / log φ²` output digits, so the SAME `Σ log a` appears on both sides and cancels),
   or the route needs a genuinely different clock.  **Next lap: prove the cancellation.**
   This is the sharpest open question and it is fully within reach: `deficit_telescope_le` plus
   `deficit_read_le` plus lap 74's `fib_sq_mul_width_le_of_forced`.
3. **`BlockCoupling`** for the actual transducer — bookkeeping.

### Lap 75, fourth commit — S7-ST: the straddle cap, and the wall LOCATED

`VandeheyS7Straddle` finally uses `VandeheyS7Lattice.zquot_sub_rat_ge` (built around lap 30 and
unused since) for the thing it was made for:

* `notMem_uIcc_of_gap` — elementary: a point further from `u` than `v` is cannot lie between them.
* `image_no_rational_of_zquot` — **the straddle cap.**  If an image interval has one endpoint a
  `ℤ[φ]`-quotient `β/δ` with `|β'| ≤ B`, `|δ'| ≤ D`, and width `< 1/(Q²·|δ|·(B+D))`, then it
  contains **no** rational of denominator `≤ Q`.  So it straddles no digit boundary of depth `≤ Q`
  and the emitter must fire.  This is the arithmetic of `Φ` doing work no distortion estimate can:
  the underlying repulsion is false over `ℚ(φ)` and true over `ℤ[φ]`.

Why this matters for the route: straddling is simultaneously (β) — the reason the pullback needs a
width floor — and the obstruction to the S7-RD cancellation (a read of `a` costs `2 log a` of lag
and the emitter buys it back as `L ≍ 2 log a / log φ²` digits **only if the narrow image lies in a
cylinder at all**).  One cap answers both.

**The wall, now located.**  The cap is effective only while `|δ|(B+D) ≪ 1/width`.  For the Raney
state `Oₙ⁻¹ Φ Pₙ` the conjugate height runs like `q_out·q_in`, so `log(|δ|(B+D)) ≍ 2λn` while the
lag to drain is `O(1)`: **Galois repulsion controls the straddle at the first `O(1)` scales and
weakens linearly thereafter.**  What is missing is therefore not a sharper repulsion estimate but
equidistribution in the *second archimedean place* — the frequency with which the conjugate height
is large relative to the scale.  That is the self-joining wall, and it is now a quantitative
statement rather than a slogan.

### Residual after lap 75 (four commits)

1. **`BlockAverageBound`** — fact (α); with the above, it is visibly the same question as
   second-place equidistribution.  The only measure-theoretic debt.
2. **Second-place frequency**: `freq{n : conjugate height of sₙ ≥ 1/width(sₙ)} → 0`.  This is the
   sharp form of the wall and the right next target; `finite_bounded_zPairs` (discreteness) is the
   only tool in the repo pointed at it.
3. **The clock rate** `N p ≤ Λ p` — follows from the S7-RD cancellation once the straddle cap
   applies at the relevant scale, i.e. from 2.
4. **`BlockCoupling`** — bookkeeping.

### Lap 75, fifth commit — S7-DC: the straddle cap is asymptotically vacuous (REFUTED, in kernel)

`VandeheyS7Decouple` settles the question the previous commit raised, with a kernel certificate
rather than by hand:

* `exists_zeta_pow_pair` — the coefficient pair of `ζⁿ`, `ζ = φ − 1`.
* `exists_bounded_zval_large_zconj` — for every `R`, a `ℤ[φ]`-number of modulus `≤ 1` with
  conjugate `≥ R`.  (`abs_zval_ge_inv_abs_zconj` applied to `ζⁿ`: the norm is a unit, so shrinking
  one place inflates the other at exactly the reciprocal rate.)
* `exists_unit_zval_large_zconj` — the same with modulus in `[1,3]`, so the real place is bounded
  **below** too: a state denominator of size `≍ 1` with an unbounded conjugate.
* `straddle_threshold_lt` — hence for every depth `Q` and every `ε > 0` there is such a denominator
  whose cap threshold `1/(Q²·|δ|·|δ'|)` is `< ε`.

**Verdict: the straddle cap cannot be applied at a fixed scale along the orbit.**  For `Oₙ⁻¹ Φ Pₙ`
the conjugate height runs like `q_out·q_in ≍ e^{2λn}` while the real place and the lag stay `O(1)`,
so Galois repulsion controls the straddle only at the first `O(1)` scales.  **No sharpening of the
repulsion estimate can fix this** — the two archimedean places of `ℚ(φ)` are independent, which is
precisely the statement that the relevant homogeneous space is the 2-dimensional Hilbert modular
surface, not the modular curve.  Sub-route closed.

### Residual after lap 75 (five commits), and the honest shape of the wall

1. **`BlockAverageBound`** = fact (α) = **equidistribution in the second archimedean place**.  After
   S7-ST and S7-DC these are visibly the same statement, and the identification is now kernel-backed
   at both ends: the cap is sharp where it applies (S7-ST) and provably unavailable beyond
   (S7-DC).  This is the whole remaining debt.
2. **The clock rate** `N p ≤ Λ p` — reduces to 1 via the S7-RD cancellation.
3. **`BlockCoupling`** — bookkeeping.

**Next lap.**  The only route left that is not the bare wall: find a form of second-place control
that CF-normality of `x` does supply.  Candidates, in order: (i) the second place enters only through
`B` (the state's own conjugate entries) and `Q` (the depth) — and `Q` is at our disposal, so ask
whether a *depth-1* straddle cap (`Q = 1`, avoid only `1/1` and `1/2`) survives, since its threshold
degrades only as `1/|δ'|` rather than `1/(Q²|δ'|)`; (ii) average the cap over the orbit instead of
applying it pointwise — `finite_bounded_zPairs` bounds how OFTEN both places can be small
simultaneously, which is a counting statement, not an equidistribution one.

### Lap 75, sixth commit — S7-TD: the whole §7 front rests on ONE named hypothesis

`VandeheyS7Transduce` completes the directive's move (a) against the real definition:

* `TransducerData q r₀ C` — what the Raney machine must supply, for each CF-normal `x` and each
  admissible `w`: a clock `N`, the pulled-back block sets `S`, `BlockCoupling`, clock regularity
  `N(n+1)/N n → 1`, and `BlockAverageBound (C·γ(I_w))`.
* `orbitWordBound_of_transducerData` — that gives the crux `OrbitWordBound q r₀ C`.
* `vandeheyS7_mul_phi_of_transducerData`, `vandeheyS7_add_phi_of_transducerData` — **both frozen
  targets from three hypotheses**: cited `GaussACRigidity`, `ImageTight`, `TransducerData`.
  All axiom-clean.

The value is in the separation, since the three components of `TransducerData` differ wildly:

| component | status |
|---|---|
| `BlockCoupling` | bookkeeping about the Raney machine; no mathematics |
| clock regularity | by S7-RD/S7-LAG ⟺ a Cesàro bound on `log aₙ`; CF-normality does NOT give it, so a real but FINITE debt |
| `BlockAverageBound` | fact (α); by S7-ST/S7-DC the same statement as second-place equidistribution — the wall, and now the ONLY wall on the front |

Nothing else on the §7 route is open: everything that is not (α) is proved or reduced to these two
named, finite obligations.

### Where a future lap should go

1. **The clock-rate debt is the only tractable thing left.**  It is NOT the wall.  Attack:
   the S7-RD cancellation (`deficit_read_le` pays `2 log a`, lap 74's
   `fib_sq_mul_width_le_of_forced` buys `L ≍ 2 log a / log φ²`) needs the straddle cap only where
   the state is narrow, and S7-DC kills the cap only where the conjugate height is LARGE.  Ask
   whether those two regimes are disjoint — i.e. whether a narrow state necessarily has SMALL
   conjugate height.  `finite_bounded_zPairs` says both places small simultaneously is a finite
   condition, which is the right shape.  This is the one open question on the front that is not
   the wall, and it is concrete.
2. `BlockCoupling` for the actual machine (`VandeheyLRTransducer` has `lrStep_spec`, `lrRun_eq`,
   `act_startState_eq` — the recursion is already there).
3. (α) itself stays parked behind the wall, as the directive requires.

### Lap 75, seventh commit — S7-CR: the last non-wall question, answered NO

`VandeheyS7ConjRow` settles the question S7-TD raised.

**1. The conjugate bottom row is an integer translate of the real one.**  For the additive instance
`Φ = [[1,φ],[0,1]]`, `Φ' = [[1,ψ],[0,1]]`, and the two differ only in the `(1,2)` entry, so for
`s = O⁻¹ Φ P`:

    row₂(s') − row₂(s) = (ψ − φ)·(O⁻¹)₂₁·row₂(P) = −√5·(O⁻¹)₂₁·row₂(P).

`addStateBottom_sub` (the algebra) and `conjRow_sub_eq` (the `√5` form).  This pins the second place
to the first via ONE integer plus the input convergent's bottom row — and is also why the conjugate
height grows like `q_in`.

**2. Narrow does NOT imply small conjugate height.**  `narrowState m` (`a,b,c,d = 1,0,1,m`) has
`width = 1/(1+m)`, and its bottom-row entries are rational, hence *their own* conjugates:
`exists_narrow_state_large_conj` gives, for every `ε, R`, a state of width `< ε` with conjugate
entry height `> R`.

**Verdict: the two bad regimes overlap.**  The regime where the S7-RD cancellation needs the
straddle cap (narrow) is not disjoint from the regime where S7-DC kills the cap (large conjugate
height).  So the clock-rate debt does **not** close by disjointness; it sits behind second-place
control exactly as fact (α) does.

### State of the §7 front at the end of lap 75

`vandeheyS7_mul_phi_of_transducerData` / `_add_phi_` (axiom-clean): both frozen targets from
cited `GaussACRigidity` + `ImageTight` + `TransducerData`.  Inside `TransducerData`:

* `BlockCoupling` — bookkeeping, `VandeheyLRTransducer` has the recursion (`lrStep_spec`,
  `lrRun_eq`, `act_startState_eq`).  The only thing left that is pure labour.
* clock regularity — behind second-place control (S7-CR).
* `BlockAverageBound` = fact (α) — behind second-place control (S7-ST + S7-DC).

**Every non-wall question on the front is now closed, four of them negatively and in the kernel.**
A future lap has exactly two honest options: (i) grind `BlockCoupling` out of
`VandeheyLRTransducer`, which is real but adds no mathematics; (ii) attack second-place
equidistribution directly, which the directive currently forbids as the self-joining wall and which
would need an altitude lap to re-authorise.  **That choice is above a grind lap's pay grade and
should be made by the next review lap.**

### Lap 75, eighth commit — S7-SC: S7-TD's bundle was VACUOUS; repaired

Found by asking whether this lap's own `BlockCoupling` can be satisfied for free.  **It can.**

* `blockCoupling_trivial` — take `S n j = {_t | G^{N n+j} y ∈ A}` (constant-true or constant-false).
  Nothing in `BlockCoupling` ties `S n j` to the transducer state.
* `blockAverageBound_trivial_iff` — with that `S`, `BlockAverageBound` unwinds **exactly** to the
  clock-tick form of the crux's own conclusion.  So `TransducerData` was a faithful restatement of
  `OrbitWordBound`, not a reduction of it.  S7-TD's headline claim was inflated.

Unaffected: `blockCount_clock_eq` (BD) is a true and useful identity, and
`integral_blockHitCount_le` a true and useful measure bound.  The error was treating the *bundle* as
content-bearing.

**The repair.**  `StateCoupling` pins the sets: `S n j` must be
`stateBlockSet (s n) w j = (s n).mob⁻¹(G^{-j} I_w ∩ (0,1)) ∩ (0,1)` for a family of `MobState`s.
Not satisfiable for free — the sets are determined by `s`, and their `γ`-masses are then pinned by
`MobState.gaussMeasure_preimage_tower_le`.  `StateData` is the honest bundle;
`orbitWordBound_of_stateData`, `vandeheyS7_mul_phi_of_stateData`,
`vandeheyS7_add_phi_of_stateData` re-derive the frozen targets from it.  All axiom-clean.

**Corrected headline for lap 75**: the §7 front is `GaussACRigidity` (cited) + `ImageTight` +
`StateData`, and `StateData`'s only non-bookkeeping component is `BlockAverageBound` **for the
pinned pullback sets** — which is fact (α) precisely because those sets carry the `γ`-mass bound
that makes empirical-vs-expected the whole question.

**Lesson to carry**: an existentially-quantified hypothesis bundle must have its witnesses PINNED or
it reduces to its own conclusion.  Check every future `∃ N S, …` reduction against a
`*_trivial` lemma before claiming it reduces anything.

### Lap 75, ninth commit — S7-AU: the vacuity audit of every §7 hypothesis bundle

S7-SC's lesson was applied to every `∃`-bundle on the front.  Verdicts:

| bundle | `∃` over | verdict |
|---|---|---|
| `ImageTight` | `T` | **sound** — `cellSet [] T` shrinks in `T`, so the frequency claim has content at every `T`. |
| `AnchoredPullback` | `u, v, c` | **sound** — `anchoredHitCount` counts the EXCEPTIONAL orbit times, so the cheap `c = 0` makes the count `0` and the hypothesis *stronger*, not weaker.  At least as strong as `ImageTight`, which is what the reduction needs. |
| `StateClock` | `s : ℕ → MobState` | **sound overall, EMPTY below `T ≈ 1/η`** — now certified. |
| `BlockCoupling`/`TransducerData` | `S` | **vacuous**; repaired in S7-SC. |

Certified here: `lowState η` (image `[0,η]`, width exactly `η`, distortion exactly `1`,
`mob t = η·t`).  When `η·T < 1` its image lies entirely below `1/T`, so every orbit time is counted
and `StateClock`'s inequality holds for free — `blockCount_le_card_lowState`.  So `StateClock` says
nothing at thresholds `T < 1/η`, and a future lap must use it at `T ≥ 1/η`, where the width floor
forces the image interval (length `≥ η ≥ 1/T`) to stick out above `1/T` and the condition becomes a
real constraint on `Gⁿx`.  **This is the quantitative form of directive fact (β): the interesting
regime is exactly target scale at or below the state width.**

Only one bundle on the front was ever vacuous, and it was this lap's own.  The pre-existing
reductions survive the audit.

### Lap 75, tenth commit — S7-RC: the read as a composition, so the lag chains

S7-RD priced a read through the *formula* `readWidth s a = |s.mob(1/a) − s.mob(1/(a+1))|`.
`deficit_telescope_le`'s `hstep` needs the price as a statement about the **next state**.  Link
supplied:

* `MobState.readState a` — the digit map `t ↦ 1/(a+t)` as a `MobState` (`0,1,1,a`, det `−1`).
* `MobState.width_comp_readState` — `(s.comp (readState a)).width = s.readWidth a`.
* `width_comp_readState_le` / `le_width_comp_readState` — S7-RD's two-sided bound, transferred.
* `MobState.deficit_comp_readState_le` — **exactly `hstep`'s shape**, with
  `ξ = log(a(a+1)) + log distortion` and no emission gain yet.

`MobState.comp` is already a cocycle (`VandeheyS7Cocycle`), so the lag estimate is now chainable
along the actual input orbit.  Orientation note: `readState a` reverses the interval
(`mob 0 = 1/a > 1/(a+1) = mob 1`), which is why `width` as an absolute value is the right invariant
and why `readWidth` was defined with those endpoints in that order.

**What is still missing for a real `hstep`**: the EMISSION half, i.e. a state for the output digit
and the gain `2 log fib(L+1)` as a composition on the other side
(`sₙ₊₁ = (emissions)⁻¹ ∘ sₙ ∘ readState aₙ₊₁`).  Lap 74's `fib_sq_mul_width_le_of_forced` is the
estimate; what is missing is its `comp` form, exactly as `width_comp_readState` was missing here.
**That is the single most mechanical remaining task on the front and the right next grind step.**

### Lap 75, eleventh commit — S7-E2: the emission gain in `comp` form; `hstep` complete

Emission is **not** a `MobState` composition on the left (`[[-b,1],[1,0]]` has a negative entry, and
the nonnegative upper row is what makes the family closed under `comp`).  State it in the direction
that IS a composition: `s = R_w.comp s'`, `s` before emitting `w`, `s'` after.

* `MobState.mob_nonneg` — a state maps `[0,∞)` into `[0,∞)`.
* `MobState.width_comp_eq` — **exact**:
  `(R.comp t).width = |det R| · t.width / (den_R(t.mob 0) · den_R(t.mob 1))`.
  So emission *widens*: the pre-emission state is the narrow one, by the factor `den²`.
* `MobState.width_comp_le` — the `R.d²` form.
* `MobState.deficit_comp_ge` — **the emission gain**: a unimodular `R` with `d ≥ D > 0` costs the
  pre-emission state `2 log D` of extra lag, i.e. emitting buys `2 log D` back.
* `MobState.deficit_comp_fib_ge` — the `fib` form, matching lap 74.

**`hstep` is now fully assembled from kernel theorems:**

| `deficit_telescope_le` term | supplied by |
|---|---|
| `+ ξ n` (read cost `≍ 2 log aₙ₊₁`) | `deficit_comp_readState_le` (S7-RC) |
| `− c·Lₙ` (emission gain `2 log R.d`) | `deficit_comp_ge` (S7-E2) |

**The analysis on the lag/clock side is DONE.**  The only remaining gap on that side is identifying
`R.d` for the actual emitted block with `cfK` of the emitted word — transducer bookkeeping inside
`StateCoupling`, not analysis.  The next grind lap should do exactly that and nothing else on this
side; any further estimate-sharpening here is wasted (lap-75 idea 4).

### Lap 75, twelfth commit — S7-CY: `R.d = cfK w`; the lag side has NO analytic gap left

S7-E2 reduced the emission gain to `2 log R.d` and flagged one gap: identifying `R.d` with the
continuant of the emitted word.  Closed.

* `MobState.cylState w` — the cylinder map `t ↦ [0; a₁,…,aₙ + t]`, i.e.
  `readState a₁ ∘ ⋯ ∘ readState aₙ`.
* `MobState.cylState_bd` — the convergent identification, as ONE simultaneous induction:
  `(cylState w).d = cfK w` and `(cylState w).b = cfNum w`.  The continuant recursion
  `cfK (a::b::l) = a·cfK(b::l) + cfK l` **is** the `comp` recursion `d(a::w) = a·d w + b w` paired
  with `b(a::w) = d w`.  The repo's `cfNum` convention (`cfNum [] = 0`) is what makes this come out;
  `cfP [] = 1` would not.
* `MobState.cylState_det` — `|det| = 1`, discharging `deficit_comp_ge`'s unimodularity hypothesis.
* `MobState.deficit_comp_cylState_ge` — **the emission gain with no free parameters**: emitting `w`
  buys `2 log (cfK w)` of lag.
* `MobState.deficit_comp_cylState_fib_ge` — the `fib` form, matching lap 74.

**`deficit_telescope_le`'s `hstep` is now discharged end to end into kernel theorems** — read
(S7-RC) and emission (S7-E2 + S7-CY).  There is no remaining analytic gap on the lag/clock side of
the §7 front.

### The front at the end of lap 75 (twelve proof commits)

    vandeheyS7_mul_phi / _add_phi
      ⇐ GaussACRigidity (cited)  +  ImageTight (audited sound)  +  StateData

and inside `StateData`:

| component | status |
|---|---|
| `StateCoupling` | pure transducer bookkeeping — the ONLY labour left, and it is labour, not mathematics |
| clock regularity | `hstep` fully supplied (S7-RC + S7-E2 + S7-CY); needs `Σ log aₙ` control, which is behind second-place equidistribution (S7-CR) |
| `BlockAverageBound` | fact (α) = second-place equidistribution (S7-ST + S7-DC) — the wall |

**Next lap**: `StateCoupling` for the Raney machine, and nothing else on this side.  The altitude
fork (re-authorise the second place, or not) is still open and still belongs to a review lap.

## Lap 79 (2026-09-29) — the crux constant is a MODULUS, not a multiple of γ(I_w)

`VandeheyS7Modulus` (S7-MD) prices the two halves of the distortion route against each other,
kernel-checked:

    freq(w) ≤ inf_{S>0} [ A/(c·S) + Cp·γ(I_w)·exp(2S) ]   (`slotCount_le_of_modulus`)
            ≤ 4A/(c·log(1/γ(I_w))) + Cp·√γ(I_w)           (`slotCount_le_modulus`)

The `exp(2S)` is S7-PB's pullback factor `2K/η` at the width floor `η = exp(−2S)` that S7-SK's
Chebyshev buys for a bad-time frequency `A/(cS)`; the factor `1/η` is SHARP by directive fact (β).
Consequence, and it is route-decisive:

* **`OrbitWordBound q r₀ C` (freq ≤ C·γ(I_w)) is NOT reachable from bounded distortion plus a
  first moment on the height.**  Forcing the second term down to `O(γ)` needs `S ≥ ½log(1/γ)`,
  which buys only `O(1/log(1/γ))` on the first.  The sharp form would need an exponential moment
  — `Σ_{m<q} 1/width_m = O(q)`, i.e. `Σ d_m² = O(q)` — and since `P(width < η) ≍ η` the integral
  `∫dη/η` diverges logarithmically, so that moment is not expected to hold.  (Not yet a kernel
  refutation: it refutes the ROUTE's arithmetic, not the statement.)
* **A modulus suffices downstream.**  `GaussACRigidity` is invoked to turn "visit frequencies
  uniformly AC" into "= γ".  Any modulus `freq(I) ≤ μ(|I|)` with `μ(t) → 0` makes every limit
  point of the empirical measures absolutely continuous, and the unique-AC-invariant-measure form
  of the cited rigidity closes it.  So the shape of the cited ergodic input should move from
  "density ≤ C" to "absolutely continuous", and `OrbitWordBound`/`OrbitACBound` should be
  restated with a modulus.  **This is a directive-level decision** (the current directive pins
  `OrbitWordBound` as the objective and forbids touching `GaussACRigidity`), so it is logged here
  for the next altitude lap, not acted on.

Next attack (either order):
1. `ClassFreqBound net w (Cp·γ/η)` — the honest η-dependent per-cell hypothesis S7-MD consumes.
   Mechanism: S7-MY (`memory_joint_le`, constant `8 log 2`) for the frequency, S7-PB
   (`gaussMeasure_preimage_tower_le`, factor `2K/η`) for the mass.  Missing link: the cluster set
   is an interval, not a cylinder — cover it by finitely many cylinders/cells (S7-CellFreq,
   S7-HitCell have the cell algebra) — plus `CellMemory` (the cell index is a bounded-memory
   function of the input digits), which stays the wall.
2. `MeanSlack` — positive recurrence of the height walk (mean of `log d`).

## S7-CN (lap 80): the operator check on `CellMemory` — answered

`src/NormalNumbers/VandeheyS7CellNoMerge.lean`.  Verdict: **`CellMemory` is NOT refuted by the
`no_window_function` / `exists_predictor_all_hit` witnesses.**  Those quantify over two unrelated
initial states; `CellMemory` is about one run `runState Φ x ·` (one `Φ`, one input), so nothing
transfers.  No Maze row is owed.

What was proved instead, in the kernel (`disc s t := T · adj S`, the discrepancy matrix):

* `disc_comp_right` — `disc (s·r) (t·r) = (det r) • disc s t`.  **Reading is inert**: the
  discrepancy of two histories is carried through a window of ANY length unchanged as a Möbius
  map.  Entrywise form of directive fact (γ); no contraction, ever, from the read action.
* `disc_comp_left` / `disc_emitStep` — an emission replaces `disc` by `E₂ · disc · adj E₁` with
  `E_i` the read matrices of the two emitted digits.  This is the only step that can move the
  discrepancy at all.
* `mob_eq_of_disc_smul_one` — `disc` is a complete invariant: scalar ⟹ same Möbius map.
* `cellMemory_selIndic_congr` — `CellMemory` forces the selection to agree at any two times with
  the same `L`-digit window.  This is the instrument a refutation would need: two run times, same
  window, different selection.

**Consequence for the route (next attack).**  The whole content of `CellMemory` sits in the LEFT
action: the needed statement is a Birkhoff–Hopf contraction for `M ↦ E₂ · M · adj E₁` over the
read matrices the run actually emits.  A memory-loss argument phrased on the input digits cannot
work and should not be attempted again.

## S7-LD (lap 80): the lag and the two-sided width ledger — the `MeanSlack` prerequisite

`src/NormalNumbers/VandeheyS7LagLedger.lean`, all `#print axioms`-clean.

* `lag Φ x n := n − runClock Φ x n` is **monotone** (`lag_mono`) and equals the stall count
  (`lag_eq_card_stalls`).  One read, at most one emission per step: a stall can never be repaid.
* `width_comp_readMap_le_div` — reading digit `a` divides the width by at least `a`
  (`(s·r).d = s.c + s.d·a`, `(s·r).c = s.d`, `|det readMap| = 1`); `width_comp_readMap_le` is the
  qualitative form.
* `width_le_width_of_emitStep` — emitting never narrows (`u.d = t.b ≤ t.d`,
  `u.c+u.d = t.a+t.b ≤ t.c+t.d`).
* `width_emitStep_le` — emitting widens by at most `(b+1)²` (`t.d ≤ (b+1)u.d` and
  `t.c+t.d ≤ (b+1)(u.c+u.d)` from `u.b ≤ u.d`, `u.a+u.b ≤ u.c+u.d`).

**What this says about `MeanSlack` (next attack).**  `log (1/width)` is a walk with increments
`≥ log a` per read and `≥ −2 log(b+1)` per emit, reflected above by `width ≤ 1`, and the lag is
monotone.  So `MeanSlack` (`Σ slack ≤ A·q`, i.e. bounded MEAN, not merely a linear clock) is
equivalent to the stalls being rare enough that the accumulated lag stays `O(1)` on average.
Heuristic to test next: a state of width `w` straddles a cylinder endpoint with probability
`≍ √w`, which would make the lag grow like `log n` and make `MeanSlack` **false** by a log factor
(while `ClockLinear`, already derived from it, would survive).  The decisive probe is therefore a
lower bound on the stall frequency, not another attempt to prove `MeanSlack`.  If that heuristic
holds, `WidthFreqBound` at a FIXED `η` fails too and the front must be restated with `η = η(q)`.

### Gotcha (lap 80)
`Finset.range_succ` does not exist in this mathlib; the insert form is `Finset.range_add_one`.
Always `ls` before `cat >` a new module: `VandeheyS7Lag.lean` and `VandeheyS7Ledger.lean` both
already existed and were clobbered (recovered via `git checkout`).

## S7-SM (lap 80): the straddle set has mass `≍ √w` — `MeanSlack` is probably FALSE

`src/NormalNumbers/VandeheyS7StraddleMass.lean`, axiom-clean.

    straddleSet w := {z | ∃ k ≥ 1, z < 1/k < z + w}
    K·w ≤ volume (straddleSet w)                    for 1 ≤ K, w ≤ 1/(K(K+1))   (straddle_volume_ge)
    volume (straddleSet w) ≤ K·w + (1/K + w)        for 1 ≤ K                   (straddle_volume_le)

Both are `≍ √w` at `K ≍ 1/√w`; the lower bound is `K` disjoint windows `(1/k − w, 1/k)`, the upper
splits at the `K`-th endpoint.

**The route consequence.**  The stall rate is `≍ √w`, not `≍ w`.  With the lag monotone (S7-LD)
and `w ≍ e^{−λ·lag}`, `d(lag)/dn ≍ e^{−λ·lag/2}` gives `lag n ≍ (2/λ)·log n`, hence
`Σ_{m<q} slack m ≍ q log q`: **`MeanSlack` (`≤ A·q`) is false by exactly one log factor**, while
`ClockLinear` (all the front's clock actually needs) survives.  Consequently `WidthFreqBound` at a
FIXED `η` also fails, and the front must be restated with `η = η(q) → 0` — the same shape change
S7-MD already forced on `OrbitWordBound` (a modulus, not a constant).

**Next attack (in order).**
1. Formalize the frequency statement: the orbit's visit frequency to `straddleSet w` is `≍ √w`
   for a CF-normal point (a finite union of intervals — CF-normality, not a new wall).
2. Restate `WidthFreqBound`/`MeanSlack` with `η(q)`, and re-price the front (S7-FS/S7-CA) against
   a shrinking `η`.  If the front survives `η(q) = q^{−c}`, the §7 chain is back on a provable
   input; if it does not, the width-floor route is refuted and that is a Maze row.

## S7-SS (lap 80): a stall IS a straddle — the run/`straddleSet` bridge

`src/NormalNumbers/VandeheyS7StallStraddle.lean`, axiom-clean.  `straddleSet` was also sharpened
to the half-open form `z ≤ 1/k < z + w` (same mass bounds, `Ioc` windows in the upper bound) so the
bridge lands on the nose.

* `straddle_of_not_emittable` — a non-emittable state whose image avoids `0` has
  `lo ≤ 1/a < lo + width` with `a = ⌊1/lo⌋`, i.e. `lo ∈ straddleSet (width t)`.  The proof is the
  contrapositive of `exists_emit`: `⌊1/lo⌋` is the ONLY candidate digit.
* `stall_straddles` — at any stall time of the run the post-read state's left endpoint straddles.

So with S7-SM: **a stall forces one explicit orbit quantity into a set of measure `≍ √w`.**  The
remaining step to the `MeanSlack` verdict is the frequency statement (CF-normality on a finite
union of intervals), not a new wall.  The `lo = 0` case is excluded and is the genuine boundary:
an image touching `0` admits every digit as a candidate.

### S7-SS addendum: the converse, and the honest status of the `MeanSlack` verdict

`not_emittable_of_strict_straddle` — if some `1/k` lies **strictly** inside the image then no digit
can be emitted, because between `1/(b+1)` and `1/b` there is no other reciprocal at all.  With
`straddle_of_not_emittable` this characterises the stall times up to the boundary case
`lo = 1/(b+1)`:

    stall  ⟺  the image straddles a reciprocal.

**Correction to the S7-SM route note.**  The frequency step is NOT ordinary CF-normality work.
The straddling quantity is `min (t.mob 0) (t.mob 1)` — a function of the STATE, hence predictable
from `x₁…x_n` (directive fact (α)) — not a function of the orbit tail.  So CF-normality of `x`
says nothing about how often it lands in `straddleSet`, and the `√w` stall rate is a *heuristic*,
not a theorem: it presumes equidistribution of the state's left endpoint.

**That is the finding.**  `MeanSlack` and `CellMemory` are now two independent reductions that land
on the SAME wall — equidistribution of the state in the compact box (fact (δ)'s cell space).  Neither
is a genuine reduction of the crux; both are faithful restatements of it.  The next altitude lap
should therefore stop looking for a third hypothesis to factor the front through, and attack the
box-equidistribution statement directly, in the modulus shape S7-MD already forced.

## S7-PN (lap 80): the used centre's `pullLip` — lap 79's next action #1, discharged

`src/NormalNumbers/VandeheyS7PullNear.lean`, axiom-clean.

* `abs_entries_le_denMax` — every entry of a `MapState` is bounded by `denMax` in absolute value
  (from `0 ≤ b ≤ d`, `0 ≤ a+b ≤ c+d`, `0 < d`, `0 < c+d`).
* `denMax_sq_le_of_denRatio` — `denMax² = pullLip·|det| ≤ K·|det|/width`; along a run `K = 6`
  (S7-Box), so a wide state has `denMax ≤ √(6|det Φ|/η)`.
* `pullLip_le_of_near` — a centre entrywise `ρ`-close to `s` has
  `pullLip cen ≤ (E + 2ρ)² / (|det s| − 4ρ(E+ρ))` whenever `denMax s ≤ E` and the denominator is
  positive.  The numerator moves by `≤ 2ρ`, the determinant by `≤ 4ρ(E+ρ)`.

With `E = √(6|det Φ|/η)` this gives `P → 6/η` as `ρ → 0`, so **any `P > 6/η` is admissible for all
small `ρ`**: S7-CA's hypothesis `P` is discharged by a choice of `ρ`, not by an assumption.  What
remains to wire it into `classFreqSlack_of_cellMemory'` is the bookkeeping that `ρ` is already free
there (it is a net parameter), which is a one-lemma instantiation.

## S7-CB (lap 80): `P` is gone — `ClassFreqBoundSlack` from `CellMemory` and a fine enough net

`src/NormalNumbers/VandeheyS7CellNoP.lean`, axiom-clean.

* `boxScale Φ η := √(6|det Φ|/η)`; `denMax_runState_le` — a wide run state has `denMax ≤ boxScale`
  (from `denMax_sq_le_of_denRatio` and the run's band `denRatio ∈ (1/2, 6]`).
* `pullBound Φ η ρ := (boxScale + 2ρ)² / (|det Φ| − 4ρ(boxScale + ρ))`;
  `pullLip_cen_le` — every USED centre satisfies `pullLip ≤ pullBound`, unconditionally.
* `classFreqSlack_of_cellMemory_noP` — S7-CA with `P := pullBound`.  The only side condition is
  `0 < |det Φ| − 4ρ(boxScale + ρ)`: the net must be fine enough to see the determinant.

**So the §7 per-cell input is now exactly `CellMemory`.**  No `P`, no cover hypothesis, no clock
hypothesis.  The front is `CellMemory + MeanSlack ⟹ BlockAverageBound`, and lap 80 showed both of
those reduce to the same box-equidistribution statement.

## S7-CX (lap 80): what the crux SAYS — the block sets are the output's own digits

`src/NormalNumbers/VandeheyS7CruxMeaning.lean`, axiom-clean.

    Gⁿx ∈ mapBlockSet (runState Φ x n) w j   ⟺   G^(N n + j) y ∈ I_w ,   y = Φ.mob x, N = runClock

(`mem_mapBlockSet_iff`, straight from `runValue_spec`).  So `BlockAverageBound` is literally an
upper bound on the frequency with which the OUTPUT's digit string reads `w` — the conclusion
`IsCFNormal (Φ.mob x)` in upper-bound, clock-reparametrised form.

**This is the lap's sharpest statement of where the difficulty is.**  The crux is a faithful
restatement of the goal, not a weakening: there is no soft reformulation left to find, and every
route must produce real information about `y`.  Fact (α) is this seen from the input side; S7-CN's
discrepancy rigidity is it seen on the state; `CellMemory` and `MeanSlack` are it seen through the
cell decomposition and the height walk respectively.  All four are the same statement.

Practical consequence: with `ClockLinear` (a theorem, S7-CP) converting the `n`-average to a
`k`-average, the front's content is exactly
`limsup_k (1/k)·#{i < k : G^i y ∈ I_w} ≤ C·γ(I_w)`, so future work may be phrased about `y`
directly with the state entering only through the clock.  That is the recommended frame for the
next altitude lap.

## S7-SO (lap 80): the crux's counting function IS the output's block count

`src/NormalNumbers/VandeheyS7SlotOut.lean`, axiom-clean.

    slotCount Φ x w p  =  outCount Φ x w (runClock Φ x p)  =  #{ i < N p : Gⁱ y ∈ I_w }

exactly — no error term, no hypothesis beyond a genuine run (`slotCount_eq_outCount`, induction:
a stall contributes nothing, an emission contributes the output's digit at the new clock time via
S7-CX).

So the §7 front, stated with no state at all, is

    limsup_p  #{ i < N p : Gⁱ y ∈ I_w } / N p  ≤  C·γ(I_w),

i.e. **`OrbitWordBound` IS the upper-frequency half of `IsCFNormal (Φ.mob x)`**, along the
subsequence `N p` (which is monotone and unbounded, `runClock_tendsto`).  The reduction is faithful
and has no slack left to exploit: every remaining route must produce real information about `y`.

## S7-MR (lap 80): how far a MODULUS reaches — it must be SET-level

`src/NormalNumbers/VandeheyS7ModulusReach.lean`, axiom-clean.

`sqrt_modulus_sum_unbounded`: splitting mass `t` into `N` equal pieces turns the bound `√t` into
`N·√(t/N) = √(N t)`, which exceeds any `C`.  **A modulus is not subadditive**, so the standard
covering proof of absolute continuity does not run from a CYLINDER-level modulus.

This is not a proof artefact: the Bernoulli measure on CF digits restricted to `{1,2}` is singular
w.r.t. `γ` yet satisfies `ν(I_w) ≤ γ(I_w)^α` on every cylinder for suitable `α ∈ (0,1)` (both
sides decay geometrically; `α` is the ratio of the rates).  Cylinder moduli genuinely fail to
detect singularity, in this very digit system.

**Correction to S7-MD's route note**, which said "a modulus is all that absolute continuity of a
limit point requires".  True only for a SET-level modulus.  `OrbitACBound` must therefore read

    limsup_k #{ i < k : Gⁱy ∈ E }/k ≤ ω(γ E)     for every measurable E ⊆ (0,1),

not just for `E = I_w`.  The good news: S7-MD's two inputs — the pullback bound
`γ(s⁻¹E) ≤ (2K/η)γ(E)` (S7-PB) and `ClassFreqBound` — are already set-level statements; only the
packaging specialised them to cylinders.  The fix is a restatement, not new mathematics, but it
must be made BEFORE the AC step is attempted or the proof will not close.  This is now the
concrete content of next action #1.

## Lap 89 (2026-09-29) — route A: `RefCesaro` discharged, `BlockForget` refuted as stated

* **DONE**: `RefCesaro` is a theorem (`MapState.refCesaro_holds`, S7-RC), so route A's universality
  conclusion rests on `BlockForget` alone. Chain: S7-RQ (relative equidistribution, no distortion
  constant) → S7-RT (order-connected target) → S7-WS (state as a function of the word) → S7-RC.
* **CRUX ADVANCE (refutation)**: `BlockForget`'s `∀ z ∈ (0,1)` is FALSE. Witness in the kernel
  (S7-QD, `VandeheyS7Quadratic`): `√2−1` (all digits `2`) and `2√2−2` (digits `1,4,1,4,…`) are two
  `GL₂(ℤ)` cycles of `ℚ(√2)`, joined by the rational-entry state `t ↦ 2/(t+2)` of width `1/3`. For
  `w = [1]` the two block averages sit at `0` and `1/2` for every `T`.
* **NEXT ATTACK**: `BlockForgetGen` — the same statement with `z` restricted to CF-normal input
  points, which is all the architecture uses (step 2 of `exists_abs_slotCountFreq_sub_le` evaluates
  at `Gᵐx`; `isCFNormal_of_digit_shift` supplies normality of the shifts). Rebuild S7-BF on it, add
  the Maze row for the refuted uniform form, then test state-independence of the level constants
  `refLevel` with the S7-RQ machinery.

## C′ quant lap 1 (2026-10-02)

`cPrimeQuant_holds` now = `cPrimeQuant_of_parts` (glue PROVED, C = 5+128C₁, ρ₀ = min(ρ₁,1/3),
δ = ρ, H = ⌈1/ρ²⌉) from two named sorries in `src/NormalNumbers/CPrimeQuant.lean`:
- `orbitWeylQuant` — THE CRUX: limsup ‖fourierMean (orbit 4 x) h‖ ≤ C₁ρ(log(1/ρ)+log(|h|+1))².
  Next: fixed-`u` rerun of `PrimeModelFamilyGraded` (doc build gaps 1–4); first sub-step is gap 4
  (quantitative version of `isNormal_subsetLambert_of_KMT_along`: fourierMean of the orbit vs
  `windowMeanS`, error ≤ 2π|h|·TailOK).
- `orbitDefectLe_of_weyl` — trapezoid Erdős–Turán (4δ + 1/(δH) + Σ 2B(h)/h).  Route:
  `fourierCoeffOn_of_hasDeriv_right` on `trapUp/trapLo`, summable coefficients, pointwise Fourier
  series (`has_pointwise_sum_fourier_series_of_summable`).

Lap 1 cont.: gap 4 PROVED (`orbitWeylLe_of_window`); tail PROVED under ρ<1
(`tailOK_of_sqrtFreshMassLe`); `orbitWeylQuant` PROVED from `windowWeylQuant` — the crux is now
a pure window-mean bound on `windowMeanS P (JG P N) h N` (J-schedule unchanged; only the cutoffs
`y_j` and tiers `u_b` become fixed-`u`).  NEXT: new file with `yU u N j = ⌊N^{u⁻²2⁻ʲ}⌋`,
`uuU u b = u + b`, rerun `schedule_admissible` + `window_bound_schedule` → `windowMean_le_termsU`,
then limsup bounds per term.
Gap 3 PROVED: siteBudget is now min 2 (4π|h|4^{-(j+1)}) upstream (PrimeModelKMTGraded); C′ chain unchanged and green.  Without the cap, E1 is linear in |h| and the frozen ρ log³ rate is unreachable via ET.
Gap 1 (schedule) PROVED: src/NormalNumbers/CPrimeQuantSchedule.lean — QuantSchedule.windowMean_le_terms holds for every fixed u ≥ 10, no fresh-mass hyp.  NEXT: in CPrimeQuant.lean, make windowWeylQuant import the schedule and bound limsup of termE1 (via recipSumIoc_yG_le + epsG ≤ ρ+ε eventually), E4a (termE4a_le: 4e^20 e^{-u²/32}), E4b (≤0.6·1.6e^{-u}), E4c (→0 needs u ≥ ? — check termE4c_tendsto's use of uG), E5 (→0).

**CRUX PROVED (2026-10-02):** `orbitWeylQuant` / `windowWeylQuant` axiom-clean (C₁ = 10⁶, ρ₁ = 1/3, u = max(3000, ⌈log 1/ρ⌉)).  `cPrimeQuant_holds` now rests only on `orbitDefectLe_of_weyl` (trapezoid Erdős–Turán).  Then `cPrimeResidueRich_holds`.

## Erdős #257 all-primes lane (2026-10-02, allprimes lap 1)
- DONE: case (i) `isDisjunctive_subsetLambert_two_of_weakRate` proved (G4Base2WeakSched:
  `exists_cutoff_subset_weak`, `moment_cap_weak` with K = 2^{j+2}, j ≥ ⌈1/ε⌉+1). Axiom-clean.
- CRUX finding: `G4.SchedB.hypE_frame_excludes_logRate` (proved) — the HypE frame caps e ≤ 2^{8K²},
  and `four_mul_le_two_pow_NE'` (farC ≈ log log X ≈ e, an ALL-primes sum, against 2^N, N=100K²)
  caps it independently; log-rate sets (towerGapPrimes) cannot meet demand 1000K³. Maze row added.
  So S-restricting Mc alone is refuted; reopen node `SRestrictedFrame`.
- NEXT attack on crux: S-restrict farC (far tail over Y<p≤X needs only S-primes in subsetLambert?)
  — read where farC enters (G4Remainder / farBound) and whether its log log X is Σ_{p≤X} 1/p over
  all primes or structural (sample size).  Also the docstring claim "F_S(e+1)−F_S(e) ≤ log 2+o(1)
  ⇒ window hit" needs the window [M(K), cap(F_S)] nonempty with cap in terms of F_S.
- Phase 1 leftovers: towerGapPrimes_gapSet, squareBlockPrimes_weakRate/not_mertensRate need
  per-block Mertens Σ_{2^{2^m}≤p<2^{2^{m+1}}} 1/p = log 2 + O(2^{-m}) (two-sided, effective).
- DONE (lap 1b): `G4.sum_omegaS_add_le` (G4FarTailS) — S-restricted far-tail AP mean,
  Σ ω_S(n+ρ)·log2 ≤ |P|(log((X+ρ)/|P|) + F_S(X+ρ)). First half of `SRestrictedFrame`.
- NEXT: check that the base-2 witness's far term (hfar_two / farBound via omegaR) can consume
  ω_S instead of ω (where is omegaR introduced in the subset witness? G4SubsetCWitness / VeryLargeCov),
  then the Mc (term_b/term_c) S-restriction in G4SchedBE.
- DONE (lap 1c): `G4.farCS` + `sum_omegaS_shiftG_le`, `sum_abs_farPartW_subset_leS`, `farAvgS_leS`
  (G4FarTailS): the whole subset far-tail chain now closes with C_S = log((X+Dm)/|P|) + F_S(X+Dm)
  in place of farC.  In the base-2 frame F_S(X) ≤ F_S(e) + O(K²) (all-primes Mertens increment
  over the exponent window [e, mE+7]), so the far tail no longer forces e ≤ 2^{O(K²)}.
- NEXT: (a) an `S`-far-tail variant of the witness structure (ScheduleWitnessSC.hfar with farCS)
  and its PropD lemma (copy of gridFrameW_subset_propD wiring at G4SubsetJunk:372);
  (b) the Mc S-restriction (term_b/term_c in G4SchedBE).
- DONE (lap 1d): `G4SchedBE2` — budget layer with the moment order decoupled: `SchedB.Dec.HypE2 b K e s`
  (Mc = McE K s, `hbudget_holdsE_gen` takes `Σ_{sm} 1/p ≤ 3s+5` as hypothesis).
- NEXT: copy the witness assembly (G4SchedBEAssembly scheduleWitnessSE pieces used by
  G4Base2Sched.scheduleWitnessSC2) onto HypE2, with hfar via `farAvgS_leS`/farCS
  (needs a ScheduleWitnessSC variant whose hfar field uses farCS — see G4SubsetWitnessCov:75).
  Then the gap-set cutoff: first e with F_S(e) ≥ D has F_S(e) ≤ D+7 (increment from
  `sum_inv_primes_Ioc_le`, 4(1+log 2) < 7), take s ≈ (D+7)/3 + m₁.
- DONE (lap 1e): crux closed. `isDisjunctive_subsetLambert_two_of_divergent` (Erdos257Divergent)
  ⇒ `isDisjunctive_subsetLambert_two_of_gapSet`; `erdos257_allPrimes_of_cases` axiom-clean.
  See HANDOFF-2026-10-02-allprimes-lap1.md.

## Explicit-square lane (row 3), 2026-10-02 — crux plan
Done: `sqrt_bakerBanaji_hyp`, `ae_isNormal_of_polyDecay` (DecayAeNormal.lean),
`Derandomize.exists_primrec_avoid` + `coins_pre` (computable conditional-expectation greedy).
Remaining for `exists_computable_isNormal_sqrt_of_polyDecay`:
- C2 SqrtDigits: `⌊2^m √y⌋ = Nat.sqrt ⌊4^m y⌋`, `⌊2^n realOfDigits⌋ = Σ_{i<n} s_i 2^{n-1-i}` (proper digits);
  orbit dyadic visit `u_k ∈ [v/2^ℓ,(v+1)/2^ℓ)` ↔ `⌊2^{k+ℓ}x⌋ % 2^ℓ = v` — exact Nat test from e-prefix.
- C3 analytic: μ{|visit_N/N − 2^{-ℓ}| > t} ≤ c/(t²√N) via trapUp/trapLo = difference of hats,
  hat Fourier coeffs (1−cos 2πhL)/(2π²h²), Fourier series HasSum, Markov + second_moment_le.
- C4 assembly: index bad tests by (level n, ℓ, v) with N=n^4, tolerances, computable J from rational C',δ';
  avoidance ⇒ dyadic visit freqs along n^4 ⇒ all N ⇒ `equidistributed_of_badic` ⇒ normal.

### Row 3 CLOSED (lap 2, 2026-10-02)
`ExplicitSquare.exists_computable_normal_sq_not_normal` is proved; `#print axioms` shows only
propext / Classical.choice / Quot.sound.  It takes `BakerBanajiQuarterCantor` as a hypothesis
(cited, faithful-or-weaker), nothing else.
- `ComputableNormal.exists_computable_normal_of_digits` (generic: decay + Primrec binary floors
  ⇒ computable coins with normal image): `block_bound` (≤ c₁/n³ per dyadic block, via
  `visit_deviation` ρ=t=1/(4n), N=n^10), `level_bound` (≤ 2c₁/n²; `sum_blocks_le`),
  `tsum_tail_le`/`tele_sum` (explicit tails, J k = 2c₁·8^(k+1), n₀ = 8c₁+2), `dens_badT`,
  `normal_of_good` (subsequence n^10 + `tendsto_div_of_monotone_of_exists_subseq_tendsto_div`).
- `SqrtFloor`: `floor_sqrt`, `primrec_sqrt` (Nat.sqrt as a bounded count), `floor_mul_two_pow`,
  `cdL`/`sqrtPhi`/`primrec_sqrtPhi`, `floor_sqrt_digits`.
- `Bridge.floor_realOfDigits_mul_pow` made public.
Remaining in the file: row 5 only (operator: no mechanism, leave).
Note: Bridge edit forces rebuild of whole-Mathlib importers; parallel `lake build` hits
"Too many open files" here — build those modules one at a time, then the full build.

## Bugeaud 10.37 strengthened: normality profile (2026-10-04) — DONE
* `CantorLiouvilleAll.exists_computable_liouville_mem_cantorSet_normalProfile`: computable Liouville
  `x ∈ K` with `IsNormal b x ↔ ¬ 3 ∣ b` for all `b ≥ 2`.  `#print axioms` = propext, Classical.choice,
  Quot.sound.  CantorLiouvilleAll.lean sorry-free.
* Mechanism: `sum_Hf_le_b` (orbit of `b²` mod `3^{t+n}` fills residue classes mod `3^t`, `t = v₃(b²−1)`,
  via exact LTE `padicValNat_sq_pow_sub_one`), `secondMoment_le_b`, `run_split`/`fract_lt_of_mem_run`,
  `not_isNormal_of_three_dvd` (frequency of `[0,1/b)` ≥ 7/8 at `n = log_b 3^T`).
* New module `SchedFamily.lean`: base-`b` visit deviation / level tests, and the multi-base derandomizer
  (resolution `nr J / H b` makes total per-stage mass ≤ 3/(J+1)²).

## Finite-state lane E3 (proof/finstate), 2026-10-04 — leaves DONE
* All leaves in `FiniteStateSelection.lean` proved; `#print axioms` of `pulariDPDTQuestion_of_lit`,
  `pulariWeakening_of_lit`, `mirror_not_mealy` = propext, Classical.choice, Quot.sound (plus the
  cited `Literature.*` Props as hypotheses).
* New: `pulariDPDTQuestion_of_lit_three` (Q-DPDT for `k ≥ 3`) from `cpPrefix_count`.
* Next: base 2 (`PulariDPDTBaseTwo`) needs a different coder; stretch nodes in
  `FiniteStateSelectionStretch.lean` were out of scope this run (operator: do not touch).

## 2026-10-05 cantorbad lap 1
Advance: headline reduced (proved) to `casselsPower_descent` + three tractable leaves for a concrete
deletion descent (`descentLaw`). Next: decompose the crux via the dead-pick correction measure; see
HANDOFF-2026-10-05-cantorbad-lap1.md.

## 2026-10-05 cantorbad lap 1 (cont.)
Proved `cpt_mem_cyl`, `descent_bad`, `exists_alive` (19361c3c): the K ∩ BAD half is sorry-free; the
only open obligation in CantorBadNormal.lean is the crux `casselsPower_descent`.
Crux analysis (to be stated in Lean next lap, not yet recorded as declarations):
- Martingale peel: |ν̂(ξ)| ≤ ρ_s|ν̂_{s-1}(ξ)| + 2δ_s per block (ρ = uniform-block character, δ = dead
  fraction) gives only a floor O(δ/(1−ρ)); with fixed c, δ is heuristically bounded below (μ_K-typical
  cylinders meet ≍ 2^R rationals per stage, the EFS mechanism), so no decay from this alone.
- Error term per block is (1/2^R)Σ_dead (e(ξ y_repl) − e(ξ y_dead)), y_dead ≈ p/q, so the needed
  saving is cancellation of Σ_m e(h bᵐ(bᵈ−1) p/q) over the orbit of b mod q — next sub-leaf to state.
- Free-digit variant: control digits must be ≥ log 3/(2 log 2) ≈ 79% of each stage, so ≤ 21% of
  positions can be pure coins; freeCount would still grow linearly (enough for Cassels), but control
  digits depend on earlier free digits, so the product structure is still lost.

## 2026-10-06 cantorbad: crux structure (prose; Lean statements pending)
- Crux is `fourierPairRate_descent` (any W summable along sched; (log N)^{-3} enough).
- ×3-invariant route closed in Lean: `not_exists_timesThree_law_on_bad` (from cited EFS), Maze row.
- Sharper window: charge q² ∈ [3^{L−R}, 3^L) per R-digit stage → ≤ 2 obstacles per parent, ≤ 4 dead of 2^R
  (needs c ≤ 3^{-2R}/12). Fixed c forces bounded R, so the per-stage dead fraction δ is a fixed constant.
- Entanglement: adaptive digits at stage s depend on all earlier free digits, so only the LAST block
  before scale log₃|ξ| gives a clean factor; martingale peel gives |ν̂| ≤ Πρ + O(δ) (floor).
- The floor is real in the Bad₂ sibling (phases e(ξ a/2ⁿ) = 1 coherently); for BAD obstacles the floor
  term is Σ_dead e(h(bᵏ−bˡ)p/q): needs the first ~L base-b digits of rationals p/q (q ≈ 3^{L/2}) lying
  near the path to be equidistributed. Candidate literature input: He–Liao 2602.01307 Cor 6.5 (rationals
  equidistribute against Cantor cylinders) — transcribe as a Literature Prop and test.

## 2026-10-06 cantorbad lap 3: replacement-rule obstruction (Lean)
- `descent_eq_descentR`, `repC_ok` (proved): descentLaw = descentR repC, with repC the `Classical.choose`
  replacement. A proof of the crux therefore uses only `RepOK repC`, so in effect it covers every admissible rule.
- `AdversarialReplacement` (conjecture node, 50% after numerics: dead rate 1/3000 per stage at stages 2–6): some admissible rule steers `2ᵏx mod 1` on dead stages and
  breaks base-2 normality. If true, the frozen crux cannot be proved from `choose_spec`, which is route-decisive.
  Doubtful step: a lower bound η>0 on the density of dead stages.
- Next: (a) attack η (rationals near K: He–Liao 2602.01307 as a Literature Prop); (b) if the obstruction holds,
  ask the operator to sanction an alternative law with canonical replacement (uniform resampling) for the headline.
- Deeper η numerics: flat ≈1e-3 over stages 2–9 → `FinitelyManyDead` node (believed false 85%; would bypass Fourier via
  Cassels + rational shift). AdversarialReplacement back to 55%.

## 2026-10-06 cantorbad lap 4
Advance: rule-independent reduction stated in Lean, `fourierPairRate_descent_of_deadRateDecay`
(sorry, 75%), with node `DeadRateDecay` (Cesàro decay of P(DeadAt s); believed false 80%).
Peeling bound: only O(1) stages near scale log₃|ξ| contribute a floor, of size ≲ P(dead there),
for EVERY admissible replacement. With AdversarialReplacement this pins the crux to dead-stage decay.
Next: (1) prove the reduction (needs pair-averaged partial Cantor products, Cassels-style);
(2) attack DeadRateDecay vs. flat η: count rationals p/q, q² ≍ 3^L, within c₀/q² of K (He–Liao).

## cantorbad lap 4 (2026-10-06): operator resolution carried out
- New law `resLaw` (`descentU`/`buildU`/`selU`): stage s takes the first alive block among fresh
  coin blocks `blk ω s t` (`Nat.pair`), proved measurable and Bad (`cpt_bad_of_alive`).
  Headline now `exists_of_law resLaw`.  Old crux is the node `FourierPairRateChoose`.
- Crux decomposed (`fourierPairRate_resLaw` proved from leaves):
  `buildU_succ_uniform` (rejection sampling), `resLaw_fourier_telescope` (exact identity:
  only dead-children characters appear, uniformity is used here), `cassels_muK` (classical,
  inside CantorLiouvilleAll), and the real crux `deadCharCancel` (exponential sums
  e(h bⁿ p/q) over obstacle centres near K).
- DONE: `cassels_muK` proved (axiom-clean) via copied `pairSum_Bf_le_explicit_b`.
- DONE: `buildU_succ_uniform` proved (block independence via MS/indep_MS).
- Next:
  `buildU_succ_uniform`; then attack `deadCharCancel` (first: bound |deadErr| ≤ 4π|ξ|3^{-10S}).
- Telescope restructured to finite depth (no Cantor-tail measure): `norm_prefChar_le`,
  `fourierAbs_resLaw_le`, `fourierPairRate_resLaw` proved from leaves `prefChar_succ`,
  `norm_rhoS`, `norm_fourier_sub_prefChar` (all routine) and crux `deadCharCancel`
  (now uniform in depth S, with cosine-product tails `tailProd`).
