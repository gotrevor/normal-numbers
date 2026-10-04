# STATUS — normal-numbers 📊

## Joint Lambert update, 29 September 2026

The synchronized-word theorem is unconditional at proof commit `f6fbf87` on
`proof/joint-lambert-unconditional`, in the sibling checkout `normal-numbers-lambert`.
There are no remaining prime-distribution hypotheses on that theorem.
The old AGP target below is a separate analytic question, not a prerequisite.
The next Lambert target is an all-N occurrence count; its proposed stronger paper bound is
`N exp(-C (log log N)^2 log log log N)`, documented on that branch in
`docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`.  It is not yet formalized.


**Digit-reading dynamics of real numbers: normality, disjunctivity, CF-normality, and the
richness of arithmetic constants.** · **Build**: 🟢 green (10617 jobs) · **Updated**: lap 88 ·
2026-09-29 · `c3babcd`

One checkout on `wip/g5-prime-subset`, Lean/mathlib v4.33.1, every campaign branch merged
(2026-09-27, `f5034b6`).  Per-campaign detail and ledgers from before the merge are in
`archive/STATUS-to-2026-09-27.md`; the lap-by-lap log is `archive/PENDING_WORK-to-2026-09-27.md`.

## Where it stands

> **§7 campaign closed 2026-09-29 (laps 27–91).**  The problem is not solved; the deliverable is the
> map of closed routes with their kernel witnesses: **`docs/VANDEHEY-S7-FALSE-STARTS.md`**.  Read it
> before re-entering §7.  Short version: the crux `BlockForgetRun`/`BlockForgetAll` is the headline
> PLUS locality (S7-NR, S7-CK) — never a reduction; the scalar debts were artefacts of a transducer
> throttled to one digit per read (S7-WQ, S7-GR); and the wall is joint equidistribution of
> `(state, input point)`, in its sharpest form a no-concentration statement about the image orbit
> (S7-GS).

The live target is the operator's moonshot, **Vandehey Compositio 2017 §7 Problem 1**: is `φx`
CF-normal when `x` is?  Theorem 1.1 itself is PROVED (`vandehey_matrix_action_holds`, 2026-09-28),
and §7 is frozen as `vandeheyS7_mul_phi` / `vandeheyS7_add_phi`.  **The whole chain to both frozen
targets is three hypotheses wide** (`vandeheyS7_mul_phi_of_orbitWordBound`, `VandeheyS7Chain`,
axiom-clean): the cited `GaussACRigidity (C/log 2)`, `ImageTight` on the image, and the crux
`OrbitWordBound φ 0 C` — an upper bound `freq(I_w) ≤ C γ(I_w)` on every word's frequency in the
image expansion.  Leg 1 (`AffineImageIrrational`) is a theorem for both instances, the threshold
parameter is free, and the interval / word / cell shapes of the crux are mutually derivable.

As of **lap 76 the transducer is built** (`runState`/`runClock`, `VandeheyS7Run`…`RunPin`) and the
front is ONE hypothesis wide: `BlockAverageBound` for the explicit sets
`mapBlockSet (runState Φ x n) w j`.  **Lap 77 supplies directive fact (δ)** (`VandeheyS7Box`): the
width is exactly `|det| / (d·(c+d))`, the denominator ratio `(c+d)/d` is trapped in `(1/2, 6]`
along *any* run (reads contract it uniformly in the digit, emissions move it by ≤ 2), `|det|` is
conserved, and therefore **every run state of width `≥ η` lies in a fixed box of `ℝ⁴`** of side
`√(6|det Φ|/η)`.  So the predictor `n ↦ s_n⁻¹(I_w)` has PRECOMPACT range — the one soft escape
directive fact (α) leaves open — and the crux becomes class equidistribution over a *compact*
class space, not the self-joining wall.  `hΦ` is discharged outright (S7-IN): `MapState` has real
entries, so `z ↦ v + ε(z−u)` interpolates.  Four other fronts
carry proved-but-conditional headlines (Joint Lambert, C3/MRT, Elliott, the casting-out crux
leaves); their hypotheses are the standing debt.

**Lap 88 (review) changes the ROUTE.**  Route B — the absolute density bound `OrbitWordBound` plus
the cited `GaussACRigidity` — is demoted: its only surviving instrument is covering the
state-dependent target by a FIXED finite family, and that is unaffordable (state-blind covering
exhausts `(0,1)`; a `ρ`-net needs `ρ ≲ γ(I_w)`, hence `≍ρ^{-4}` cells and cover mass
`≍γ(I_w)^{-3}`, so the constant blows up with `|w|` — fact (ε)).  The repo already owns a SECOND
reduction of the same headline with **no cited input and no absolute continuity**: universality,
`affineCFN_of_uniformFreq` and `affineUniformFreq_of_runClock : RunClock + SampledUniformCount ⟹
AffineCFN`.  Lap 88 builds its architecture: with the skew product of S7-SK, the sliding-block
identity (`abs_slotCount_sub_sum_blockAvg_le`) makes the crux's frequency the Cesàro average of
block time-averages, and **`BlockForget`** — the block time-average forgets its initial state,
uniformly over states of width `≥ η` (an `x`-free statement, GREEN in both Route-A probes) — lets
ONE reference state replace them all, after which CF-normality evaluates the average
(`exists_uniform_slotCountFreq`, `VandeheyS7BlockForget`).  The analysis that needs is now in hand
too: **S7-EQ** (`tendsto_blockCount_Ioo`) computes the orbit frequency of an arbitrary INTERVAL
along a CF-normal orbit exactly, by a two-sided cylinder squeeze.

## Superseded overview (Theorem 1.1 era, kept for the reductions it names)

The live target is **Vandehey 2017 Theorem 1.1** (Möbius images of CF-normal numbers are
CF-normal), down to the single leaf `MobiusCFNScale`: `x ↦ p·x` for prime `p`.  Smith descent and
Serret killed composite determinants, the diagonal factor, division and all of `GL₂(ℤ)`.  The
transducer programme's **output** side (§4.3 Cesàro counting, §5 triggers, §6 assembly, the
`hK`/`hkK` trigger bounds, and the run↔CF-digit translation) is now closed; the crux is the
**input** side, `hjs`.  Lap 4 found two route-decisive defects there and the repairs for both: the
Raney automaton is period-2 in the sign of the determinant (so the uniform-length common reach
that `classEquidistribution_of_common_reach` demands is impossible — repaired by the row-swap
involution and the phase-corrected automaton on `RPlus D`), and the capstone's *factorized*
`JointStateFreq` hypothesis is numerically FALSE at `D = 3` (repaired by carrying a general
`ρ(q,t)`, with the escape mass controlled for free by `ρ(w,t) ≤ γ(I_w)`).  Joint Lambert has since become unconditional (`f6fbf87`).  The inherited Vandehey summary
above records the earlier shared-checkout state; current Lambert details follow below.
C3/MRT, Elliott and the casting-out crux leaves still carry conditional headlines.

## Joint Lambert quantitative count — DONE, 29 September 2026

The unconditional all-`N` occurrence count is proved and axiom-clean:
`jointWords_quantitative` gives `A(N) ≥ N exp(-C (log log N)² log log log N)` for every
`N ≥ N0`, and `jointWords_power_count` gives `A(N) ≥ N^(1-ε)` eventually, for every fixed
`ε > 0`.  Audit: `scripts/check-joint-lambert-count.sh`.  Details and the four findings
against the paper plan: `HANDOFF-2026-09-29-joint-lambert-count-DONE.md`.

## What's happened (newest first)

- **2026-09-29 (lap 88, review).**  ROUTE CHANGE, recorded in `DIRECTION.md`.  Fact (ε): route B's
  finite-cover instrument cannot give a `w`-uniform constant (state-blind covering has mass `1`; a
  `ρ`-net needs `ρ ≲ γ(I_w)`, giving cover mass `≍γ(I_w)^{-3}`), so route B's residual is
  irreducibly the weighted joint statement `ClassFreqBound` + an AC input.  Universality (route A)
  takes over: it already reduces the headline (`affineCFN_of_uniformFreq`,
  `affineUniformFreq_of_runClock`) with **no cited input**.  Two modules landed, both axiom-clean:
  **S7-BF** (`VandeheyS7BlockForget`, `32ae5b1`) — `blockAvg`, the sliding-block identity, the new
  `x`-free crux `BlockForget`, and `exists_uniform_slotCountFreq` (one constant `L` that EVERY
  affordable CF-normal input's crux frequency converges to: the `SampledUniformCount` shape); and
  **S7-EQ** (`VandeheyS7IntervalFreq`, `c3babcd`) — `tendsto_blockCount_Ioo`, the exact orbit
  frequency of an arbitrary interval for a CF-normal orbit, by a two-sided cylinder squeeze (the
  sharp form of S7-CV, factored out).  Laps 81–87's window-domination chain (S7-WC/WN/WD/WD′/CV) is
  kept: S7-WN and S7-CV are the analysis S7-EQ runs on.

- **2026-09-29 (lap 77, review).**  Course correction on the INSTRUMENT, not the target.  Laps
  58–76 hunted a **width floor**; that is only half of what compactness needs, and it is the hard
  half.  The other half — bounded distortion — is FREE: `denRatio := (c+d)/d` obeys `r ↦ 1+1/(r+a−1)`
  on a read (contracting *uniformly in the digit*) and moves by a factor in `[1/2,2]` on an
  emission, so along **any** run `r > 1/2` from step 1 and `r ≤ 6` from step 2, with no hypothesis
  on `x`, on `Φ`, or on normality.  With `width = |det|/(d(c+d))` exactly and `|det|` conserved,
  that puts every run state of width `≥ η` in a fixed box (`S7-BX`, `VandeheyS7Box`, `5a5f0ef`,
  eight lemmas axiom-clean) — **directive fact (δ)**, the precompactness fact (α) leaves room for.
  Also found and fixed: lap 76's "next action #1" was a misreading — `hΦ` is a triviality
  (`exists_mob_eq`, `S7-IN`), because `MapState` allows real entries and only bans `det = 0`; and
  the `∀ Φ` form of `hBA` was needlessly strong (`orbitWordBound_of_runBlockAverage_one`).
  `DIRECTION.md` CURRENT DIRECTIVE rewritten: next is `ClassFreqBound`, the joint state-cell /
  cylinder frequency bound.
- **2026-09-29 (lap 74, review).**  Course correction: nine of laps 58–73 had gone to the SECOND
  obligation (`ImageTight` → `AnchoredPullback` → `StateClock`) while the crux went untouched, and
  `StateClock`'s uniform width floor is the wrong shape — fact (β) exhibits states of arbitrarily
  small width, so the true transducer states admit no uniform floor.  `DIRECTION.md` now forbids a
  further uniform-`η` `StateClock` lap.  Landed instead the **measure side of the crux**
  (`VandeheyS7Pull`, `604dec8`, all axiom-clean): `volume_preimage_le` bounds the state pullback of
  an ARBITRARY set by `distortion/width` (via `Set.InjOn.invFunOn` +
  `LipschitzOnWith.hausdorffMeasure_image_le` + `μH[1] = volume`), `gaussMeasure_preimage_tower_le`
  shows **the tower is free** (the bound on `s⁻¹(G^{-j}I_w)` is independent of `j`, by Gauss
  invariance), and `blockPullback_sum_le` gives a whole emitted block of length `L` total mass
  `≤ (2K/η)·L·γ(I_w)` — linear in `L`, with exactly the density the crux demands.  Residual named:
  `WidthFloorFreq` + `BlockAverageBound`.
- **2026-09-29 (lap 30, review).**  Leg 1 of the ergodic route DISCHARGED, for both frozen
  instances: `VandeheyS7Golden.affineImageIrrational_goldenRatio` and
  `affineImageIrrational_add_goldenRatio` (axiom-clean).  If `φ x` (resp. `x + φ`) were rational
  then `z = Int.fract x` is a root of an explicit integer quadratic with leading coefficient
  `r.den²` — `(z+m)² + r(z+m) − r² = (z+m)²(1 + φ − φ²) = 0`, resp. `z² + (1−2s)z + (s²−s−1) = 0`
  — so lap 29's `cfDigit_le_of_quadratic` bounds its partial quotients and
  `not_isCFNormal_of_bddDigits` finishes.  Only `φ² = φ + 1` is used: no Lagrange, no eventual
  periodicity.  The chain to both frozen targets is now exactly `GaussACRigidity` (cited) plus the
  crux `OrbitCellBound`.  The review also pinned the crux's structure (see `DIRECTION.md` →
  CURRENT DIRECTIVE): it is predictable-set decoupling; the per-state distortion bound genuinely
  fails on states that straddle `1/k` below the cell scale; and `Γ ∩ Φ⁻¹ΓΦ = {±I}` makes the state
  set `PSL₂(ℤ)` itself, which is the structural source of `no_window_function`.

- **2026-09-29 (lap 27, review).**  A route-level correction on the §7 crux, plus the engine the
  corrected route needs.  (a) `cfCount_tendsto_of_decomposition`'s BOUNDED decomposition error is
  unattainable: the exceptional set of `cfDigit_agree_depth` has positive Gauss mass, so a
  CF-normal input meets it with positive frequency and the error is `Θ(p)`.  Replaced by
  `VandeheyS7Approx`: schemes `(S k, ε k → 0)` chosen before `x`, with `abs_sub_le_of_approx`
  keeping the limit attached to the scheme, `tendsto_div_of_approxScheme` the engine, and
  `sampledUniformCount_of_approxScheme` the crux with no existence hypothesis; `approxScheme_sqrt`
  witnesses that the weakening is strict.  (b) `VandeheyS7Memory.no_window_function` REFUTES the
  planned window function: `(1,3;0,8)` and `(1,7;0,32)`, both of distortion `1`, emit `2` and `4`
  after reading *any* word, so the emitted digit is not a function of the window for any window
  length.  `spread_runWord_le` bounds the image DIAMETER, never its LOCATION.  This is
  `hall_vandehey_synchronizing_transducer` again, reproved without the `ZMod D` quotient; new row
  `hall_emit_digit_window_function`.
- **2026-09-29 (laps 11–26, grind).**  The §7 analytic layer, all axiom-clean: uniform contraction
  `3−2√2` and the Birkhoff coefficient; `mob_nonexpansive` as a polynomial identity; merging
  `spread_runWord_le` from a Fibonacci row recursion plus `det = ±1`; `volume (boundaryBad δ) ≤
  6√δ`; one Gauss step costs exactly `(n+1)²`; `cfDigit_agree_depth`; the scale cutoff off the
  log-tail bad zone; `budget_le`/`budget_tendsto_zero` (so `m` may be proportional to the word
  length — the route is not budget-limited); `wordState_eq_conv` (the word matrix IS the
  continuant matrix, transposed); `triggerGap_of_mem_cyl`; `windowBound_runWord` unconditional
  along the run; `cfDigit_mob_eq_emitDigit`.

- **2026-09-28 (lap 4, review).**  Two route-decisive findings on the transducer's input side,
  plus the enabling algebra.  (a) `det (M · B j) = − det M`, so the Raney automaton carries a
  deterministic period-2 phase and NO uniform-length common reach exists — the hypothesis of
  `classEquidistribution_of_common_reach` is unsatisfiable for `lrDelta`.  Repair, in the kernel:
  `Mat2.balanced_decomp_unique` (the Raney factorization is unique — this PINS the
  `Classical.choose`-defined `lrDelta`/`lrOut` for the first time), the row-swap involution
  `ι M = J·M` with `lrDelta ∘ ι = ι ∘ lrDelta` and `lrOut ∘ ι = map not ∘ lrOut`, and the
  arithmetic core `lrDelta M j = [[0,D],[1,0]] ↔ D ∣ a+bj ∧ D ∣ c+dj` solved over `ZMod D`;
  numerically the phase-corrected automaton reaches `diag(1,D)` in exactly 2 digits for every
  prime `D ≤ 23`.  (b) `probes/raney_joint_product.py` REFUTES the factorized `JointStateFreq`
  at `D = 3` (four states' `ρ(q,t)/γ(I_q)` move 20 % across short `q`, ≈15σ); it holds at `D = 2`
  only because the stationary law is uniform there.  The capstone must carry a general `ρ`.
- **2026-09-28 (laps 2–3).**  The output side closed: the §4.3/§5/§6 engine
  (`VandeheyOutputFreq.lean`), the capstone `mobiusUniformFreq_of_transducer`, Lemma 2.2 in run
  form, `hK`/`hkK` for the concrete machine, the L/R run dictionary and the CF↔pattern bijection.
  Structural finding: rescale by RUNS, never by letters (the Gauss digit mean is infinite).
- **2026-09-28 (lap 1, review).**  Course-corrected: three laps had gone into the transducer's
  input side while the route-decisive output side was untouched.  `VandeheyOutputFreq.lean`
  opened with the factorized joint-frequency hypothesis `JointStateFreq δ s₀ ν` (limit
  `ν t · γ(I_q)` — the product form our ψ-mixing gives and Vandehey's Remark 3.6 does not),
  `gaussMeasure_allWordsEvent`, the finite digit-truncated escape
  `exists_boundedWords_sum_gt`, the pointwise split `wCount_le_of_finset`, and the engine
  `eventually_wCount_le`.  Guard rule discharged.  `DIRECTION.md` now carries a binding
  CURRENT DIRECTIVE.
- **2026-09-28.**  Vandehey §2 rebuilt on Raney normal form after refuting the paper's own
  Lemma 2.1 descent (`Mat2.vandeheyStep_not_terminating`); the transfer-operator pin freed of
  bijectivity; Doeblin at a single common target.
- **2026-09-28.**  Serret leaf discharged (`mobiusCFNGL2_holds`); Smith reduction to
  `MobiusCFNScale`; `moshchevitinShkredov_cf_false` proved; `UniformResonantMass` discharged.
- **2026-09-27.**  Every campaign branch merged into one checkout (`f5034b6`).

## Open fronts

### Joint Lambert: simultaneous disjunctivity (unconditional)

- **Proved:** `JointLambert.jointLambertDisjunctivity_unconditional` and
  `jointWords_two_four_unconditional` in `JointLambertUnconditional.lean` (`f6fbf87`).
  Every tuple of valid words across finitely many distinct bases occurs at common positions
  infinitely often, including bases 2 and 4.  No analytic hypotheses remain on this theorem.
- **Mechanism:** rescale the search and use `exists_pointwise_exponential_distribution`;
  the AGP and AGPExpRange statements remain separate open analytic targets.
- **Next mathematical target:** the quantitative all-N bound
  `N exp(-C (log log N)^2 log log log N)`.  The new paper argument uses primes near k^3,
  a gcd-weighted divisor average and three tail ranges.  It is not yet formalized.
- **Read:** [completed proof](docs/JOINT-LAMBERT-RESCALED-PROOF.md),
  [quantitative derivation](docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md),
  [original paper](papers/2026-09-26-joint-lambert-disjunctivity.md).

### Vandehey §7 Problem 1 (OPERATOR OBJECTIVE): is `φx` CF-normal when `x` is?
- **Frozen targets** (`VandeheyS7.lean`): `vandeheyS7_mul_phi := AffineCFN goldenRatio 0`,
  `vandeheyS7_add_phi := AffineCFN 1 goldenRatio`, `VandeheyS7Problem1` for the general quadratic
  form.  Open statements; `sorry`-free is not expected and they are never weakened.
- **The live chain, three hypotheses wide** (`VandeheyS7Chain`, axiom-clean):
  `vandeheyS7_mul_phi_of_orbitWordBound` ⊢ the frozen target from `GaussACRigidity (C/log 2)`
  (cited) + `ImageTight` on the image + the crux `OrbitWordBound φ 0 C`.  Same for `x + φ`.
- **Discharged legs.**  Leg 1 `AffineImageIrrational` (both instances, `VandeheyS7Golden`, lap 30);
  the geometric leg `CellCover (1/log 2)` (lap 29); the threshold parameter
  (`orbitCellBound_of_orbitWordBound`, lap 43); input tightness (`imageTight_of_isCFNormal`, lap 45);
  the three shapes of the crux are mutually derivable (S7-Q, `VandeheyS7Equiv`).
- **The measure side of the crux, done lap 74** (`VandeheyS7Pull`): `volume_preimage_le`
  (arbitrary target, factor `distortion/width`), `gaussMeasure_preimage_le` (factor
  `2·distortion/width`), `gaussMeasure_preimage_tower_le` (**the tower is free**),
  `blockPullback_sum_le` (a block of length `L` costs `(2K/η)·L·γ(I_w)`).
- **The wall, as Lean** (`VandeheyS7Wall.lean`): Thm 1.1's finite state set is a certificate about
  `ℤ` with no `ℤ[φ]` analogue (`ℤ[φ]ˣ` infinite; `M⁻¹VM` integral forces `V` diagonal).  The state
  is a point of `SL₂(ℤ[φ])` (S7-L) and `Γ ∩ Φ⁻¹ΓΦ = {±I}`, so the state set is literally `PSL₂(ℤ)`.
- **Refuted, with Lean witnesses** (do not retry): the window-function frame
  (`no_window_function`); bounded-error decompositions (the exceptional set has positive Gauss
  mass); the predictable-hit principle at every gap `k` (`exists_predictor_all_hit`, S7-G2); the
  lap-48 three-step bootstrap (`no_bound_of_one_le_coeff`, coefficient 3); the bad set is `√δ`,
  not `δ` (`volume_badSet_le`).  And lap 74: `StateClock`'s **uniform** width floor is impossible
  for the true transducer states (fact β), so only the frequency form is live.
- **The transducer, built lap 76** (`VandeheyS7Run`…`VandeheyS7RunPin`): `runState`/`runClock`
  realize the image orbit for ANY `Φ` with `Φ.mob x = y`, the clock ratio `N(n+1)/N n → 1` is a
  theorem, and `orbitWordBound_of_runBlockAverage` reduces the crux to `BlockAverageBound` for
  `mapBlockSet (runState Φ x n) w j` — explicit sets, nothing existential.
- **Fact (δ), lap 77** (`VandeheyS7Box`, axiom-clean): `width_eq` (`width = |det|/(d(c+d))`,
  exactly), `denRatio_comp_readMap` (`r ↦ 1+1/(r+a−1)`, a read contracts uniformly in the digit),
  `denRatio_emit_comparable` (an emission moves `r` by a factor in `[1/2,2]`),
  `half_lt_denRatio_runState_succ` + `denRatio_runState_le_six` (so `r ∈ (1/2,6]` along ANY run),
  `absDet_runState` (`|det|` conserved), and the headline `runState_entries_abs_le`: every run
  state of width `≥ η` has all four entries in `[−M,M]`, `M = √(6|det Φ|/η)`.
- **`hΦ` discharged, lap 77** (`VandeheyS7Interp`): `exists_mob_eq` — `z ↦ v + ε(z−u)` is a legal
  `MapState` (`det = ε ≠ 0`; the CONSTANT map is what `hdet` excludes).  The front is now
  `AffineImageIrrational + BlockAverageBound`.
- **What is left**: (1) `ClassFreqBound` — partition the state box into finitely many `ρ`-cells
  `B_i`, approximate `s_n⁻¹(I_w)` by the fixed set `E_i`, and bound the JOINT frequency
  `freq{n : s_n ∈ B_i ∧ Gⁿx ∈ E_i}`.  Summing over `i` without the state constraint is NOT allowed
  (it costs the factor `M`).  (2) the width floor in frequency form, still needed to reach the box
  at all; (3) `ClassFreqBound` itself — the compact-class-space analogue of Vandehey's class
  equidistribution, and the successor to directive fact (α).
- **Read:** `DIRECTION.md` CURRENT DIRECTIVE, `PENDING_WORK.md` lap-74 section,
  `papers/vandehey-2017-open-problem-attack-map.md`, the Maze rows
  `hall_emit_digit_window_function` and `hall_vandehey_synchronizing_transducer`.

### Vandehey 2017 Thm 1.1: Möbius images of CF-normal numbers are CF-normal (ONE leaf left)
- **The Smith reduction (2026-09-28, `VandeheySmith.lean`, sorry-free).**  `MobiusCFN a b c d`
  is the per-matrix statement; it is closed under matrix product (`MobiusCFN.comp`, whose only
  CF input is that a CF-normal number is irrational — `not_isCFNormal_of_not_irrational`, proved
  by the Euclidean descent of the Gauss orbit on rationals).  An elementary Hermite descent on
  `|det|` (`exists_column_kill`, `mobiusCFN_of_leaves`) writes every nonsingular integer matrix
  as `M'' · diag(p,1) · V` with `V ∈ GL₂(ℤ)`.  And `vandeheyUniformFreq_of_matrix_action` shows
  the crux is *equivalent* to Theorem 1.1 (the limit is `γ(I_v)`).
- **Serret leaf DISCHARGED (2026-09-28, `VandeheySerret.lean`, sorry-free).**
  `mobiusCFNGL2_holds : MobiusCFNGL2` — `PGL₂(ℤ) = ⟨x ↦ x+n, x ↦ 1/x⟩` by a Euclidean descent
  on the bottom-left entry; each generator shifts the CF digit sequence boundedly, which
  `CFTailFreq.tendsto_occStart_of_shift` / `isCFNormal_of_digit_shift` absorbs.  The one real
  computation is `t ↦ 1 − t`: `T²(1−t) = T t` for `t < 1/2`, `T(1−t) = T² t` for `t > 1/2`.
- **The single open leaf:** `MobiusCFNScale` — `x ↦ p·x` preserves CF-normality for prime `p`.
  `vandeheyUniformFreq_of_scale` reduces the whole theorem to it.  Composite determinants, the
  diagonal factor, division and all of `GL₂(ℤ)` are gone.
- **Available for that leaf:** `VandeheyTwo.tendsto_jointCount_classStep`
  (`VandeheyClassEquidist.lean`) — Vandehey's §3 made unconditional, without the refuted
  Moshchevitin-Shkredov criterion: joint (digit window, `ℙ¹(ℤ/p)` class) frequencies converge to
  an `x`-independent limit.  What is missing is Vandehey §2 (Raney normal forms) + §5–§6
  (trigger counting), plus the fibre step (state = class × mergeable fibre).
- **Retired 2026-09-28:** `exists_jointFreq_limit` is gone.  Its `Synchronizing` hypothesis is
  unsatisfiable for the needed transducer, and that is now a theorem:
  `VandeheyAut.not_synchronizing_of_injective_quotient` (axiom-free).  Maze:
  `hall_vandehey_synchronizing_transducer`.
- **Read:** `archive/handoff/HANDOFF-2026-09-28-vandehey-bridge-CLOSED.md` (its NEXT list),
  `papers/vandehey-2017-open-problem-attack-map.md`.

### Moshchevitin-Shkredov refutation (PROVED 2026-09-28)
- `moshchevitinShkredov_cf_false` (`MoshchevitinShkredovRefuted.lean`, in the root import,
  axiom-clean): uniformly bounded upper block frequencies do NOT imply CF-normality.
- Witness `x = [0;1,2,3,…]`, built as the limit of the nested cylinders `[1,…,s+1]`
  (`exists_irrational_cfDigit_succ`, reusable).  Strictly increasing digits ⇒ every genuine
  block occurs at most once ⇒ every frequency is `O(1/p)`, so the hypothesis holds vacuously at
  `σ = 0`, while CF-normality would force `γ(I_1) = log₂(4/3) > 0`.
- Maze: `hall_moshchevitin_shkredov_cf_false`.  Any route through Vandehey 2017 Lemma 3.3 is dead.

### C3/MRT: `ConjC3` (richness of `∑ ω(n)/bⁿ`) as a conditional theorem
- **Live headline:** `conjC3_of_geom_input_band'` (`C3MrtBlockDefect.lean`), sorry-free and
  axiom-clean.  It is `conjC3_of_geom_input_band` with `UniformResonantMass` DISCHARGED
  (2026-09-28), so it takes three inputs, not four:
  1. `KPointNoExcAtWith …`: the Tao-Teräväinen K-point correlation input, faithful to arXiv
     2512.01739 Thm 3.1.  Out of reach today, and TT say so themselves.
  2. ~~`UniformResonantMass`~~: discharged by `uniformResonantMass_holds`
     (`C3MrtUniformMass.lean`).  No longer a hypothesis anywhere on the archimedean side.
  3. `CharPrimeSumLogQ D` with `2D < 125`: standard in strength, but needs Dirichlet
     L-function theory that mathlib lacks.  The `t = 0` slice is reduced to
     `CharTailCancellation` (`C3MrtCharSumZero.lean`).
  4. `WideBlockSavingBand`: a bespoke per-block saving, not a literature statement.
- **Retired 2026-09-28:** `highResonantMass_le_narrow` (`C3MrtURMLowHigh.lean`) was the one
  open obligation on a second, redundant route to `UniformResonantMass`.  With the theorem
  already in the kernel it had no consumer, so it and its two dependents are removed; the
  file's sorry-free lemmas stay.  Maze: `hall_urm_low_high_split`.
- **Vacuous, do not retry:** `conjC3_of_geom_input_blocks`, `_blockPartial`, `_pairing` (lap 115).
- **Read:** `archive/findings/ROUTE-ESCALATION-2026-09-25-c3mrt.md`,
  `archive/handoff/HANDOFF-2026-09-25-6-urm-lowhigh.md`.

### Elliott: two-point logarithmic Elliott for the Lambert twist (one hypothesis left)
- **Proved:** `ElliottLedger.twoPointElliottLog_of_zetaExponent` gives `TwoPointElliottLog` from
  a single input, `ZetaLogDerivExponent θ` with `θ < 1`: `‖ζ'/ζ‖ ≪ (log |t|)^θ` on `Re s ≥ 1`.
  `ledger_nonvacuous` guards it, and the chain has no sorries.
- **Gap:** Vinogradov-Korobov gives `θ = 2/3`.  The repo owns `θ ≥ 9`, and the gap is recorded
  as `zetaLogDerivExponent_gap`.
- **Relation to the rest:** it feeds the log-average, whereas the normality route consumes the
  natural-average `CastingOut.TwoPointElliott`, a Chowla-strength step away.  It shares with
  C3/MRT only the type of debt (archimedean non-pretentiousness), not a `Prop`.
- **Read:** `archive/handoff/HANDOFF-elliott-2026-09-25-lap121.md`,
  `archive/findings/ON-LINE-FINDINGS-2026-09-26-tao-2016-log-elliott.md`.

### Casting-out programme: the designated-open crux leaves
These are the ratified conjecture nodes.  They are open by design, and none is scaffolding.
- **C1:**
  - `SwingC1.hAutoCorrAll`, which supersedes `hDepthAll`.
  - `SwingC1Log.castLawLog_one`, the first rung.
  - `SwingC1Log.conjC1Log`.
  - `TwoPointBet.twoPointWeightedAvg_all`, a research bet.
- **C2:** `SwingC2.shiftedDivisorIncidence_holds` is the one open obligation on the headline
  path (Brun-Titchmarsh plus a Linnik lower bound).
- **C3:**
  - `SwingC3Leaf.weylLambertTwist_holds`, the crux that C3/MRT attacks.
  - `SwingC3Rotation.tailLargeDecouple_holds`.
- **Pair decoupling:** `PairDecoupleProve.multiElliott_all` and its refutation twin
  `PairDecoupleRefute.not_pairDecouple_all`.
- **Other open nodes:**
  - `PrimeLambertOscillation.phaseOscillation`, which gates `irrational_primeLambert`.
  - `MahlerDriftOne.exists_prime_nonresidue`, which is Linnik-strength and probe-true below 6000.
- **Likely stale (triage):** `SwingC2.tauMomentPrimesShiftStruct_of_primeDensity`, which takes the
  old vacuous `PrimeDensityAP`, and `SwingC2.survivorLeaf_of_struct`.
  `SwingC2.constructionInputs_even` is off the headline path.

## Closed campaigns (headline, Lean name)
- **Track A.**  Wall's criterion `isNormal_iff_equidistributed_orbit`, the ln 2 reduction, and
  Stoneham's constant `isNormal_two_stoneham23`.
- **Wall rational (2026-09-27).**  `WallRational.isNormal_rat_mul_add`: normality in base `b` is
  preserved by `x ↦ qx + r` for rational `q ≠ 0` and `r`.
- **Philipp ψ-mixing (2026-09-27).**  `philipp_psi_mixing_holds`: Gauss-measure cylinders ψ-mix
  at a geometric rate.
- **B5′ Khinchin.**  `xstar` is absolutely normal and CF-normal (Becher-Yuhjtman).  B6 affine
  images: `exists_cfNormal_and_affine_cfNormal`.  Leftover stretch: `ae_tail_average_tendsto`.
- **G4 disjunctivity.**  `G4.isDisjunctive_base` for every `b ≥ 3`, with corollaries
  `irrational_primeSum` and `every_word_occurs_base_late`.
- **Entropy expedition (2026-09-15).**  `IsNormal 2 fullRealW`.  The mechanism's normality wall is
  itself a theorem.
- **Campaign B (2026-09-20).**  Master additive weight, polylog-`c` weights.
- **Pair A multicutoff, Theorem C′ (2026-09-23).**
  `FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero`, unconditional.
- **Master conjectures (2026-10-02, 1 lap).**  `BorelConjecture`, `BaileyCrandallHypA` (Tier P
  Props).  Planted: `hypA_lnTwo`, `hypA_pi_base16`, `borel_sqrt_two`.  Engine
  `hypA_isNormal_of_kicked` (B–C Thm 2.10 for every base: `not_irrational_of_hasFiniteAttractor_base`;
  two-sided tail `equidistributed_of_fract_perturb_abs`); base descent `isNormal_of_isNormal_pow`.
  Consequences: π normal in base 2 (`hypA_pi_base2_uncond`), ln 2 in base 3 (`hypA_lnTwo_base3`),
  π² in bases 16/2 given `Irrational (π²)` (`hypA_piSq_base2`), Borel ⇒ disjunctive.  Maze test:
  `MasterMaze.lean` (`mazeTestImplied`/`mazeTestNotImplied`; `equidistributed_lnTwoOrbit_iff`,
  `run_sublinear_of_isNormal`).
- **10.37 profile (2026-10-03, audit + 1 lap): UNCONDITIONAL.**  `CantorLiouvilleAll.exists_computable_liouville_mem_cantorSet_normalProfile`: same Liouville Cantor point, IsNormal b ↔ 3 ∤ b for all b ≥ 2 (vs Cassels a.e.: all b not a power of 3; `not_isNormal_six`).  Family derandomizer `SchedFamily`.
- **Bugeaud 10.31 Hertling (2026-10-03): audited, ~12%, not run.**  `Hertling.bugeaud_10_31` reduced to the single sorry `blockForcing` (needs uniform ×r×s Schmidt-type lemma); guards + corners proved.
- **Bugeaud 10.36 (2026-10-03, sweep c + audit + 1 lap): UNCONDITIONAL.**  `UniformBad.bugeaud_10_36`: ξ with ‖bⁿξ‖ > b^{-24} ∀ b ≥ 2, n ≥ 0 (book best: b^{-1100 b log 3b}).  Generic nested-interval engine `exists_avoid_of_stagePotential` (reusable for 10.31).  Lower limit c > log₂3 proved.  Note `docs/notes/bugeaud-10-36-uniform-bad.md`.
- **Odd bases + fast base-2 discrepancy (2026-10-03, audit + 2 laps).**  `LevinSparse.exists_levinRate_oddNormal`: x normal in all odd bases and powers of 2, base-2 D*_N = O(log²N/N), cond. `Levin1999` (95%) + `BLDLemma5` (93%).  Computable odd-normal translate `exists_computable_bld_odd_add`.  Open target `exists_absNormal_base2_fast` (ABSS barrier, 20%).  Note `docs/notes/odd-bases-fast-base-2-discrepancy.md`.
- **Bugeaud 10.37 (2026-10-03, audit + 2 laps): UNCONDITIONAL.**  `CantorLiouville.exists_computable_liouville_mem_cantorSet_isNormal_two`: computable x in Mathlib's `cantorSet`, `Liouville`, normal to base 2.  Cassels second moment with forced zero-runs (`secondMoment_le`), slow-schedule derandomizer `SchedDerandomize`.  Note `docs/notes/bugeaud-10-37-cantor-liouville.md`.
- **Computable normal in BAD + Rivoal reciprocal (2026-10-03, sweep b + 1 lap).**  `BadNormal.exists_computable_absNormal_bad`: computable abs. normal x with all CF partial quotients in {1,2} (Montgomery; Bugeaud §7.7 / Queffélec 'none exhibited'), cond. `SahlstenStevensBernoulli12` (refereed 93%; JS + BB Thm 1.2 cross-routes).  `ReciprocalNormal.exists_computable_absNormal_recip_not_normal` (Bugeaud 10.18, BB refereed) and `..._not_simplyNormal` (10.17 all b, `BakerBanajiSparse` refereed 93%).  Folklore risk: Becher–Heiber–Slaman 2015 method.  Note `docs/notes/explicit-normal-bad-and-reciprocal.md`.
- **Manai 2606.08325 §1.1, P(x) normal / Q(x) not (2026-10-03, audit + 2 laps).**  `ExplicitPQ.exists_computable_PQ`: ∀ nonconstant Q ∈ ℤ[X], computable x with Q(x) not normal and P(x) abs. normal ⟺ ¬AffineIn P Q, cond. `BakerBanajiUniformQuarterCantor`.  Per-P exponent derandomizer `FamilyDerandomizeVar`.  Refuted frozen leaf: `not_approxGPfamClaim` (Q = X + 512(X−1)⁹).  Single-pair a.e. mechanism already in Manai 2609.24665 Thm 1.3 proof.  Note: `docs/notes/computable-normal-square-not-normal.md` §3.
- **Bergelson–Downarowicz 2506.12929 §8.6 questions 2 and 4 (2026-10-03, sweep + 1 lap): both No.**  `Deterministic.not_productQuestion` / `not_ratioQuestion` / `not_recipProductQuestion` UNCONDITIONAL (`dimH` of products/ratios/reciprocal products of deterministic numbers is 0; packing-type cover `deterministic_subexp_cover`; Liouville control `not_dimH_prod_zero_of_dimH_zero`).  `not_reciprocalQuestion` cond. B-D Cor 4.11(2) `DetSub` + Cor 8.15 `DetSqNotDet` (refereed 93%/88%).  Open: `quadraticLogWitness_of_cor14` (Manai route, 90%, not on the headline path).  Note `docs/notes/deterministic-numbers.md`.
- **Manai's `Ω_k` (2026-10-02, audit + 2 laps).**  `ExplicitOmegaK.exists_computable_mem_Omega_two`: computable
  `e` with `√(cantorReal e)` ABSOLUTELY normal and in `Ω₂` (answers Manai's x² question as posed), cond. on
  `BakerBanajiQuarterCantor`.  `ExplicitOmegaK.Omega_nonempty` / `ae_mem_Omega`: `Ω_k ≠ ∅` for every `k ≥ 2`
  (Manai: "not even known"), cond. on `BakerBanajiAnalyticQuarterCantor` (BB v2 Cor 2.10, refereed 92%).
  `ExplicitOmegaK.dimH_Omega_eq_one`: `dim_H Ω_k = 1` ∀k≥2, cond. `BakerBanajiAnalytic` (general self-similar BB Cor 2.10, refereed 92%), via missing-digit measures `DigitCantor`.  `ExplicitOmegaK.exists_computable_mem_Omega`: computable point of `Ω_k` for EVERY `k ≥ 2`, cond. `BakerBanajiUniformQuarterCantor` (refereed 93%), via the cylinder cut `pushFourier_le_of_deriv2_lower` + family derandomizer `FamilyDerandomize`, 2026-10-03.  `ExplicitOmegaK.lean` is sorry-free.
  Note: `docs/notes/computable-normal-square-not-normal.md`.
- **Computable normal `x` with `x²` not normal (2026-10-02, audit + 2 laps).**
  `ExplicitSquare.exists_computable_normal_sq_not_normal`: `x = √y`, `y = cantorReal e` (binary digits 0 at
  every odd place, so no `11` and `y` is not normal, `not_isNormal_cantorReal`), `e : ℕ → Bool` `Computable`,
  `x` normal in base 2.  Conditional only on the cited `BakerBanajiQuarterCantor` (BB 2401.01241 Cor 1.5,
  refereed implied 93%, decay probe with affine control).  Base-2 version of Manai 2506.15422 §1 / 2508.09319 (his "normal" is ABSOLUTE; all-bases upgrade in
  progress, `ExplicitOmegaK`), computable sense; existence was Manai 2609.24665 `thm:2`.  Engines: `DecayAeNormal`, `Derandomize`,
  `ComputableNormal`.  Row 5 (deterministic `y`, `1/y` normal) parked: no mechanism, barriers stated.
- **Erdős #257 for EVERY infinite set of primes (2026-10-02, audit + 2 laps).**
  `Erdos257.erdos257_allPrimes_of_literature` (`Erdos257Headline.lean`): `Σ_{p∈S} 1/(2ᵖ−1)` is irrational for
  every infinite prime set `S`, conditional only on `Literature.Erdos1968CoprimeSummable` (convergent `Σ1/p`)
  and `CastingOut.TTEquidistributedReal` (literal TT Thm 3.1(i)).  Divergent case: base-2 disjunctivity with
  no rate, `isDisjunctive_subsetLambert_two_of_divergent(_literature)` (S-restricted moment cap + far tail,
  `G4SchedBE2`, `G4FarTailS`).  The counted form is now a theorem, `ttEquidistributedDyadic_of_real`
  (`TTDyadicBridge.lean`).  Outward note: `docs/notes/erdos-257.md`.
- **Erdős #257 at base 2 for prime subsets (2026-10-02, ~6 laps).**  `Erdos257.isDisjunctive_subsetLambert_two`:
  `Σ_{p∈S} 1/(2ᵖ−1)` is disjunctive in base 2 for every prime set `S` with a Mertens rate (new even
  for all primes); `erdos257_primeSubset`, `erdos257_residueClass`: Erdős #257 for `A = S`.  Conditional
  on the cited `CastingOut.TTEquidistributedDyadic` (Tao–Teräväinen Thm 3.1(i), dyadic form, derived
  85%; the first transcription was vacuous, `ttEquidistributedCorrelation_trivially_true`).
- **Joint Lambert + Campbell (merged 2026-10-02).**  `JointLambert.jointWords_quantitative`; with `S = {2}`,
  `Literature.Campbell.campbellEQuestion_holds` re-proves (no hypotheses; first answered on paper by CaptainSude, `CaptainSude2026EDisjunctive`) Campbell arXiv:2605.24160 §4 (every binary string
  occurs infinitely often in binary `E`).  Priority citation `Campbell2026AbelianThm1` (decimal
  abelian-normal, not normal) for our binary `exists_abelianNormal_not_normal`.
- **Erdős #257 for `A = k·S` (2026-10-02, 1 lap).**  `Erdos257.erdos257_kMul`: `Σ_{n∈k·S} 1/(2ⁿ−1)` is
  irrational for every `k ≥ 2` and every prime set `S` with a Mertens rate (all primes:
  `erdos257_kMul_primes`; residue classes: `erdos257_kMul_residueClass`); `erdos257_twoMul_normal`: normal
  in base 2 at `k = 2` for C′ sets.  Unconditional.  Via `subsetLambert S (2ᵏ)` = the #257 sum.
- **Growing-prime localized logarithm (2026-10-02, 2 laps).**  `GrowingLocalizedLog.zetaY_isNormal`:
  `ζ_Y = Σ_{P⁺(m) ≤ Y(m)} 1/(m·2ᵐ)` is normal in base 2 for monotone `Y ≥ 3` with
  `π(Y n) ≤ (1−ε) log₂ log n`; `exists_unbounded_zetaY` gives an admissible `Y → ∞`.  Conditional on
  the cited `Literature.VandeheyDiff.VandeheyThm51` (Vandehey 2016 Thm 5.1, numerically tripwired).
  Engine: `isNormal_xS` (any retained set keeping `3ᴷ`, `2·3ᴷ`).
- **Quantitative C′ (2026-10-02, 2 laps).**  `Quant.cPrimeQuant_holds`: bounded square-root fresh
  mass `ρ ≤ ρ₀` + divergent reciprocal sum ⇒ base-4 orbit discrepancy `≤ Cρ log³(1/ρ)`.
  `Quant.cPrimeResidueRich_holds`: every fixed-length base-4 word has positive lower frequency in
  `∑_{p≡a (q)} 1/(4ᵖ−1)` for all large `q`.  Unconditional.
- **C4 (2026-09-25).**  `Abelian.c4_realizable`, plus the odd and finite-complement variants.
- **Elliott, Tao 2016 Thm 1.3.**  Two-point log-Elliott, in both the CM and multiplicative forms.

## Axiom ledger (the fidelity spine)

Math-axiom count excludes the trust base (`propext`, `Classical.choice`, `Quot.sound`).
This repo holds **no `axiom` declarations**: literature inputs are named hypothesis `Prop`s
(standing rule 3), so debt shows up as a hypothesis on the theorem, not in `#print axioms`.
`sorryAx` on a headline means a disclosed open crux, and is listed as such.

| headline theorem | paper claim | `#print axioms` shows | status |
| --- | --- | --- | --- |
| `Literature.vandehey_matrix_action_holds` (`VandeheyCapstone.lean`) | unconditional (Vandehey 2017 Thm 1.1) | trust base | 🟢 **CLEAN, DISCHARGED 2026-09-29** (`6d7a8ad`).  Route: Serret + Smith reduce to `x ↦ D·x` (`D` prime); the concrete Raney `L/R` transducer supplies a monotone RUN clock with an `x`-independent positive rate (`tendsto_runClock_div`, Lemma 6.1) and an `x`-independent Cesàro limit for the image's CF-occurrence count sampled along it (`exists_tendsto_cfCount_runClock`).  Assembled by `mobiusUniformFreq_of_runClock`.  NB the theorem lives downstream of `LiteratureVandehey.lean` (import cycle); the frozen statements stay there. |
| `VandeheyS7.affineCFN_of_runClock` (`VandeheyS7Clock.lean`) | — (reduction for the OPEN §7 Problem 1) | trust base | 🟡 clean **as a reduction**, and since lap 88 the PRIMARY route: `0 < q` + `RunClock ℓ rate` + `SampledUniformCount q r₀ ℓ` ⊢ `AffineCFN q r₀`, for every real `q, r₀`, with **no cited ergodic input**.  `SampledUniformCount` is the live frontier; next prerequisite = `RefCesaro` (a CF-normality consequence via S7-EQ), and then the crux `BlockForget` |
| `VandeheyS7.MapState.exists_uniform_slotCountFreq` (`VandeheyS7BlockForget.lean`) | — (route-A architecture, lap 88) | trust base | 🟡 clean as a reduction: `BlockForget w` + `RefCesaro w` + an affordable width floor ⊢ one constant `L` that every CF-normal input's crux frequency converges to.  `BlockForget` is the crux and is `x`-free; `RefCesaro` is a CF-normality consequence (next prerequisite) |
| `VandeheyS7.tendsto_blockCount_Ioo` (`VandeheyS7IntervalFreq.lean`) | — (the analysis route A runs on) | trust base | ✅ proved lap 88, axiom-clean: a CF-normal orbit's frequency of an arbitrary interval is exactly its Gauss measure.  Two-sided cylinder squeeze; no AC, no ergodic theorem |
| `VandeheyS7.vandeheyS7_mul_phi_of_orbitWordBound` (`VandeheyS7Chain.lean`) | — (the LIVE reduction for the OPEN §7 Problem 1) | trust base | 🟡 clean **as a reduction**, three hypotheses wide: `GaussACRigidity (C/log 2)` (cited, standard ergodic theory) + `ImageTight` on the image + `OrbitWordBound φ 0 C` (the crux).  Same for `vandeheyS7_add_phi_of_orbitWordBound`.  DEMOTED lap 88 (fact (ε)): the cover instrument cannot give a `w`-uniform `C`, so this route needs `ClassFreqBound` + an AC input.  Kept as the alternative; next prerequisite there = `ClassFreqBound`: the front is now `AffineImageIrrational + BlockAverageBound` alone (`orbitWordBound_of_runBlockAverage_all`, `VandeheyS7Interp`), and fact (δ) (`runState_entries_abs_le`) makes the predictor's range precompact |
| `VandeheyS7.MobState.blockPullback_sum_le` (`VandeheyS7Pull.lean`) | — (measure side of the crux) | trust base | ✅ proved lap 74, axiom-clean: a state of width `≥ η`, distortion `≤ K`, pulls a whole emitted block of length `L` back to Gauss mass `≤ (2K/η)·L·γ(I_w)`.  The tower `G^{-j}I_w` is free, by Gauss invariance |
| `VandeheyS7.MobState.volume_preimage_le` (`VandeheyS7Pull.lean`) | — (instrument) | trust base | ✅ proved lap 74, axiom-clean; the pullback bound for an ARBITRARY target set, no measurability |
| `VandeheyS7.MapState.runState_entries_abs_le` (`VandeheyS7Box.lean`) | — (directive fact (δ)) | trust base | ✅ proved lap 77, axiom-clean: every run state of width `≥ η` has all four entries in `[−M,M]`, `M = √(6·\|det Φ\|/η)`.  Unconditional — no hypothesis on `x`, `Φ` or normality.  This is the precompactness of the predictor's range |
| `VandeheyS7.MapState.orbitWordBound_of_runBlockAverage_all` (`VandeheyS7Interp.lean`) | — (the live §7 front) | trust base | 🟡 clean as a reduction, now TWO hypotheses: `AffineImageIrrational` (a theorem for both instances) + `BlockAverageBound` for `mapBlockSet (runState Φ x n) w j`.  `hΦ` discharged by `exists_mob_eq` |
| `VandeheyS7.anchoredPullback_of_stateClock` (`VandeheyS7Clock2.lean`) | — (second obligation) | trust base | 🟡 clean as a reduction, but PARKED: its `StateClock` hypothesis demands a UNIFORM width floor, which fact (β) makes impossible for the true transducer states.  Next prerequisite = the frequency form `S7-WF` |
| `VandeheyS7.affineImageIrrational_goldenRatio` (`VandeheyS7Golden.lean`) | — (leg 1) | trust base | ✅ proved lap 30, axiom-clean; same for `affineImageIrrational_add_goldenRatio` |
| `VandeheyS7.cellCover_inv_log_two` (`VandeheyS7Cell.lean`) | — (geometric leg) | trust base | ✅ proved lap 29, axiom-clean |
| `VandeheyS7.sampledUniformCount_of_approxScheme` (`VandeheyS7Approx.lean`) | — (engine, fallback route) | trust base | 🟢 clean; the crux from a uniform ε-approximation scheme, with no existence hypothesis |
| `VandeheyS7.MobState.no_window_function` (`VandeheyS7Memory.lean`) | refutation | trust base | 🟢 clean; the window-function frame is dead |
| `Literature.vandeheyUniformFreq_of_scale` | — (reduction) | trust base | 🟢 clean; reduces Thm 1.1 to `MobiusCFNScale` |
| `Literature.mobiusCFNGL2_holds` | unconditional (Serret) | trust base | 🟢 clean, discharged |
| `Literature.philipp_psi_mixing_holds` | unconditional (Philipp) | trust base | 🟢 clean, discharged |
| `moshchevitinShkredov_cf_false` | refutation (Airey–Mance) | trust base | 🟢 clean |
| `JointLambert.jointLambertDisjunctivity_unconditional` | **none** | installed prime distribution + CRT + tail | Proved at `f6fbf87`; quantitative strengthening remains paper work. |
| `JointLambert.primeIntervalSupply_holds` | **none** | `Erdos446.eventually_dyadicPrimes_card_bounds` → real PNT | ✅ proved, axiom-clean |
| `CastingOut.conjC3_of_geom_input_band'` | conditional (C3, open conjecture) | trust base | 🔴 by design: `KPointNoExcAtWith` is Tao–Teräväinen-hard, `CharPrimeSumLogQ` needs Dirichlet L-theory, `WideBlockSavingBand` is bespoke.  C3 is itself a conjecture, so a conditional headline is the honest form |
| `ElliottLedger.twoPointElliottLog_of_zetaExponent` | conditional on `ZetaLogDerivExponent θ`, `θ < 1` | trust base | 🟡 Vinogradov–Korobov gives `θ = 2/3`; repo owns `θ ≥ 9`; gap recorded as `zetaLogDerivExponent_gap` |

**Done** would be: every headline's base is the trust base alone, with 🔴 only where the paper
is itself conditional.  Today the 🟡 with a live attack is the Vandehey §7 crux, since lap 88 in its universality form
(`SampledUniformCount`, reached through `BlockForget` + `RefCesaro`; `OrbitWordBound` /
`OrbitCellBound` / `OrbitACBound` are the demoted route-B shapes); `AGP` and `ZetaLogDerivExponent` are
the other two, both parked.

## Pointers

`ROADMAP.md` (frozen plan) · `DIRECTION.md` **CURRENT DIRECTIVE** (binding, altitude-owned) ·
newest baton `HANDOFF.md` / `archive/handoff/HANDOFF-2026-09-28-*` · `PENDING_WORK.md` (queue) ·
`JUDGE.md` (statement freezing) · `src/NormalNumbers/Maze.lean` (refuted routes, as Lean data).

## Map of the repo
- `src/NormalNumbers.lean`: the root import.  `lake build` covers every module except the
  Elliott chain.
- `src/NormalNumbers/Maze.lean`: every refuted route, as Lean data.
- `papers/`: per-paper notes (PDFs live in `~/personal/papers`, symlinked in, not committed), plus
  `literature-review.md`, which has one route-synthesis chapter per campaign.
- `archive/`: pre-merge handoffs, kickoffs, probes, findings and the old DIRECTION/STATUS/
  PENDING_WORK.  Lean docstrings still cite some of these by bare filename, so use
  `find archive -name <file>`.
- `OVERVIEW.md`/`.html`: the reader's project map, refreshed 2026-09-28.  Rebuild it with
  `make -f docs/overview.mk`.
