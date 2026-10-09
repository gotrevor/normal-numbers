# DIRECTION — normal-numbers 🧭

## Branch directive (2026-10-06, `proof/uniformbad-threshold`): locate the optimal 10.36 exponent `c⋆` 🎯

**This is the directive for branch `proof/uniformbad-threshold`.**  The `proof/cantor-bad-normal` section below
belongs to that branch (its route is parked at the middle-digit obstruction); do not work it here.

**Objective:** prove the two frozen headlines in `src/NormalNumbers/UniformBadThreshold.lean`:
`twelve_fifths_le_cStar` (`12/5 ≤ c⋆`, 85%) and `cStar_le_four` (`c⋆ ≤ 4`, 55%), where
`c⋆ = inf {c : ∃ ξ, ∀ b ≥ 2, ∀ n, ‖bⁿξ‖ > b^{−c}}` (Bugeaud 2012, Problem 10.36; the repo proved `c⋆ ≤ 24`).
Never restate or weaken them.  The stretch node `CStarLeThree` and any sharper located value are bonuses.
- **Mandated next move:** probe first (`scripts/uniformbad_cstar_probe.py` is the host's floating-point probe;
  make an exact-rational version).  (a) For the lower bound, generate an exact finite certificate at `c = 12/5`
  (a cover of `[0, 1]` by rational intervals, each inside one forbidden window of some `(b, n)`, `b ≤ 16`, with
  rational `δ_b ≤ b^{−12/5}`) and check it in Lean by `decide`/`norm_num`/`native_decide` (all fine at this tier).
  (b) For the upper bound, design the construction: small bases `b ≤ B₀` tracked explicitly inside the nested
  windows of `UniformBad.exists_avoid_of_stagePotential` (or a variant engine), large bases by its stage
  potential.  State the construction's key lemmas as named nodes with confidences before proving them.
- **Push the frontier:** once a headline is green, locate `c⋆` more tightly (higher certified lower bound with
  more bases; `CStarLeThree`).  Record every located bound as a Lean theorem, every failed mechanism as a Maze row.
- **Operator note (Ren, 2026-10-07 02:45):** the `c⋆ ≤ 4` crux now rests on `SmallBaseTreeCore` (15%) and
  `TreeEngineSuffices` (50%).  Keep it, but bank the reachable upper bounds in parallel: lap 1 measured the pure
  potential engine stalling near `c ≈ 7`, so prove the best engine-only bound as a theorem (`cStar_le_eight` or
  better, then as close to the stall as the constants allow), using the free perfect-power bases.  Each lower
  located upper bound is an advance; so is a higher certified lower bound (bases beyond 10 in the cover).
- **Forbidden drift:** normality or disjunctiveness of the 10.36 points (impossible, `not_isNormal_of_uniformBad`);
  re-proving `c⋆ ≤ 24`; literature hunting beyond what a lap needs (the 2026-10-03 freshness audit stands).
- **Why:** the host probe (`UniformBadThreshold` docstring) puts `c⋆` in about `[2.44, 3]`: bases 2, 3 alone give
  `log₂ 5` (survivors `1/5`, `3/10`, rational), and bases up to 16 push it to `≈ 2.44`.  Locating an optimal
  constant in an open Bugeaud problem is new mathematics with a definite, checkable endpoint.

- **Review lap 2026-10-07 (c⋆ lap 3) — direction revised, binding for this branch:**
  New mechanism: **Rosenfeld counting** (count alive dyadic cells `N_k`; charge each kill to an alive ancestor at
  a fixed lag, so `N_{k+1} ≥ 2N_k − Σ m_i N_{k+1−i}` and induct `N_{k+1} ≥ ΛN_k`).  It is exact for base-2 runs
  (charged at lag 6 with multiplicity ≤ 2) and needs no Frostman constant.  Probe (`scripts/cstar_models/ros*.py`):
  per-level version closes at `c = 6` (`Λ = 5/3`, all bases, slack ≈ 0.04 after rigorous tails), fails at
  `c = 5`; with perfect level-averaging it reaches only `c ≈ 4.6`; at `c = 4` binary-exact counting fails even
  idealized (averaged slack −0.105), so **base 3 must be exact jointly with base 2** (confirms lap 2 by an
  independent mechanism).  Simulation (`joint.js`): the true joint `{2,3}` tree at `c = 4` grows 1.808/level and a
  base-3 event costs 2.4% ≈ the Lebesgue share `2/81`, so the crux is a worst-case-vs-typical gap.
  **Mandated next moves, in order:** (1) formalize the counting engine and `cStar_le_six` (new file
  `UniformBadCount.lean`; the engine is the `b ≥ 5` half of the eventual `c ≤ 4` proof, so it is on-path);
  (2) crux probe: a finite-state abstraction of the joint `{2,3}` skew product (binary run state, ternary run
  state, position in ternary units, phase of `k log₃ 2`) with a computed sub-eigenvector — does it certify
  `Λ ≥ 1.75`, and with how many states?  State the result as a Lean node (`JointCoreCount`-type) with confidence.
  **Forbidden drift:** more α-power potential-engine tuning; Frostman-constant cores (`SmallBaseTreeCore` at
  `C ≤ 3/2` is doubtful); thickness theorems (Falconer–Yavicoli constants are hopeless here).

- **CURRENT DIRECTIVE for this branch (review lap 2026-10-07, c⋆ lap 7) — supersedes the lap-3 orders above.**
  *Objective* unchanged: the frozen headlines (`twelve_fifths_le_cStar` proved; `cStar_le_four` open).
  *Finding:* the Newhouse crux has no adaptive escape.  Any `τ`-thick `B ⊆ ⋂_{b≥3} E_b(c)` puts every
  pair of `τ`-close windows inside its hull into one gap (`Newhouse.windows_merge_forced`, proved), so
  `ThickCore` is exactly locality of the canonical merge closure, i.e. control of cross-base window
  clusters at every depth (Maze row "adaptive split cores for the Newhouse thick core").  Both known
  `c ≤ 4` mechanisms are now walls: Newhouse (cluster locality) and counting (a weight-regular exact
  `{2,3}` core with growth `≥ 1.78`, Maze row "counted medium bases").
  *Mandated next moves, in order:* (1) **decisive `c = 4` counting probe**: the exact joint `{2,3}`
  system (true positions, no box abstraction) with threshold pruning of cells mostly inside a base-3
  window; report growth, weight spread, and the worst per-ancestor weight-aware charge of `b ≥ 5`.
  Record the verdict as a Lean node or Maze row the same lap.  (2) **bank `c⋆ ≤ 5`**
  (`UniformBadFive.cStar_le_five`, frozen node): counting engine, base 2 exact (runs, multiplicity 1,
  lag 5), each window `(b, n)` killed at `lv` (≤ 4 cells) or `lv − 1` when it spans ≥ 3 cells (≤ 3 cells),
  lag `⌊log₂(¾(b⁵−2))⌋`, perfect powers dropped, growth `181/100` off and `329/200` on the base-3 kill
  levels, products bounded by `L₃(n+2) ≥ L₃(n)+3`.  Probe (`scripts/cstar_models/lvl5c.js`,
  `pess.js`): pessimistic slack `0.019` (uniform growth fails, `−0.023`); control `c = 6` slack `0.21`.
  *Forbidden drift:* building thick cores (adaptive splits, flipped pairings, cluster discarding)
  without a cross-base locality mechanism; re-proving `c⋆ ≤ 6`; Falconer–Yavicoli.
  *Why:* `c⋆ ≤ 5` moves the located interval to `[12/5, 5]` with machinery (level-dependent growth,
  per-window resolution) that any counting route to `c ≤ 4` reuses; the probe decides whether that
  route is alive before more `c = 4` formalization is spent.

- **Operator answer to the c⋆ lap-9 STUCK (Ren, 2026-10-07 06:50): rescope accepted.**  Banked: `5/2 ≤ c⋆`
  (`five_halves_le_cStar`) and `c⋆ ≤ 6` (`cStar_le_six`), both axiom-clean.  `cStar_le_four` stays frozen and
  unweakened, recorded as a research wall (the Maze rows above).  **The run's gate is now
  `sorry-free:src/NormalNumbers/UniformBadFive.lean`**: prove `cStar_le_five`.  After it: (a) the lowest upper bound
  the counting engine reaches with base 2 exact (lap 8: charges live at c = 4.25), banked as its own theorem;
  (b) a higher certified lower bound (more bases in the cover).  Do not reopen `cStar_le_four` without a new
  mechanism for an exact {2,3,5} core.

- **Operator gate 2 (Ren, 2026-10-07 07:05):** `cStar_le_five` landed (lap 10).  The run gate is now
  `sorry-free:src/NormalNumbers/UniformBadNineHalves.lean`: prove the frozen `cStar_le_nine_halves` (`c⋆ ≤ 9/2`, 40%).
  The `cStar_le_five` engine has slack 0.013, so this needs a new ingredient: base 3 exact alongside base 2 (lap-8
  joint recursion lives at c = 4.25).  Probe the joint {2,3} growth at c = 9/2 first.  If it cannot be made uniform,
  bank the lowest exponent the current engine certifies (any c < 5) as its own theorem, record the wall in the Maze,
  and stop.  A higher certified lower bound (above 5/2) is a parallel bonus.

- **CURRENT DIRECTIVE for this branch (review lap 13, 2026-10-07) — supersedes lap 7's orders; operator gate 2 still binds.**
  *Objective* unchanged: the frozen gate `cStar_le_nine_halves`.
  *Finding:* the statement is almost surely true (finite systems put `c⋆` near `5/2`,
  `CStarLeThirteenFifths`), but every local per-window engine stalls near `c ≈ 4.55`: proved for the
  per-stage engine even with only bases 2, 3 (`not_perStageCert`); Lebesgue and Parry-measure precharges
  and box abstractions fail numerically (Maze row "local per-window engines at c = 9/2").  The base-3
  charge must fall by about 30%, which needs where base-3 windows sit in the alive set (non-local).
  *Mandated next move:* operator gate 2's fallback is complete (`cStar_le_124_25` banked, walls in the
  Maze, lower bound now `93/37`), so the run calls `box stuck` with this evidence.  If reopened: either
  (a) bank a formal per-stage engine (≈ `4.6–4.7`, multi-rate products over alignment classes), or
  (b) a non-local input for the exact `{2,3}` core (where `k/3ⁿ` falls among pattern-alive binary cells).
  *Forbidden drift:* retuning local engines at 9/2 (two-rate, per-stage, precharge) without a 30% cut
  in the base-3 charge; touching-kill box abstractions of the joint position; re-probing the two-rate engine.
  *Why:* three independent local mechanisms meet at the same threshold, so the loss is the worst-case
  placement of base-3 windows, not the bookkeeping.

Directive history:
- 2026-10-07 (c⋆ lap 13, review): local engines walled at 9/2 (`not_perStageCert`); lower bound 93/37; stuck evidence.
- 2026-10-07 07:05 (operator): gate moved to `cStar_le_nine_halves` after `cStar_le_five`.
- 2026-10-07 06:50 (operator): rescoped the run gate to `cStar_le_five` after the c⋆ ≤ 4 wall.
- 2026-10-07 (c⋆ lap 7, review): Newhouse thick core closed by forced merging; probe c=4 counting core, bank c⋆ ≤ 5.
- 2026-10-07 (c⋆ lap 3, review): counting engine + `c⋆ ≤ 6` banked first; crux = exact joint {2,3} core certificate.
- 2026-10-06 evening: threshold lane opened (Trevor: "go for it").

## CURRENT DIRECTIVE (2026-10-09, branch `proof/cantor-repetition`, review lap 13): P1 is the last leaf 🎯

**Objective:** prove `repPairArith_of_sparse` (CantorRepetition), the Baker-free shadow dichotomy.
It is the ONLY open obligation under the frozen headline `liouvilleCantorFullProfile` and the scope
target (`CantorRepetition.lean` sorry-free): P3 is DONE (`PadicTwoLogs.laurentZeroLemma` proved
elementarily, so `padicTwoLogs` is a theorem and `repPairArith_of_three_dvd` is wired to it).
**Mandated next moves, in order** (design detail: PENDING_WORK "P1 ASSEMBLY DESIGN"):
1. **Decisive probe first:** state `repPairPos_shadow` (the `repPairPos_copy` analogue whose
   shadow-class terms are the min-option bound with NO Baker input) and the per-pair lemma
   "min(repBound none, repBound (some k)) ≤ θ_k + 1[orbit point c·tᵐ cyclically sparse]" for
   classes 2/4.  Prove the per-pair lemma on the real `repBound` (it reuses
   `cycSparse_of_copy_free` + `cycSparse_of_three_pow_mul`).  If the separated sub-case (class 2:
   top of ξ leaves the fresh stretch) does not reduce to `c = h'`, record that as a refutation
   (Lean `¬` or counterexample) + Maze row and fall back (below).
2. Refined classification (`pair_classify_rep` returning the run `k` for classes 2/4).
3. Totals of shape `N·N_k·φ_k`, summable along `sched` (`sched_tail1`, `summable_shadow_sched`).
4. Assembly `repPairArith_of_sparse` (sign/3-part reduction as `repPairPower_of_pos`).
**Fallback (only if step 1 refutes the per-pair dichotomy):** prove
`CantorExactExponentProfile.Literature.BakerLogDiscrepancy` (archimedean two logs, fixed heights
`t, 3`, any polylog rate) by an interpolation determinant on the model of `PadicTwoLogs.lean`.
**Forbidden drift:** re-opening P3 (done); Matveev / Baker–Wüstholz formalization; sorry'd theorems
whose statement is a cited Prop; edits to frozen statements (`LiouvilleCantorFullProfile`,
`RepPairArith`, `repPairArith_of_three_dvd`'s statement, `repPairArith_of_sparse`'s statement);
other lanes.
**Why:** the review lap found the zero lemma elementary (a support determinant whose top
coefficient is a generalized Vandermonde), which closed P3 in one lap; the remaining uncertainty
of the whole route is concentrated in P1's per-pair dichotomy (carry normalization with repeated
exponents; the separated sub-case), so that is the decisive probe.

Directive history (repetition branch):
- 2026-10-09 review lap 13: zero lemma PROVED (elementary), P3 done; P1 `repPairArith_of_sparse` is the last leaf, per-pair dichotomy first.
- 2026-10-08 review lap 10: sparse-pair route complete; next = one 3-adic two-log input (3-adic chain proved), Baker-free shadow (P1), then prove the input (P3).
- 2026-10-07 review lap 7: sparse-pair route (cluster lemma + Matveev) replaces the walls.
- 2026-10-07 review lap: assembly first; walls stay named nodes.


## Branch directive (2026-10-06, `proof/cantor-bad-normal`, cantorbad lap 6): `K ∩ BAD ∩ normal` via the local route 🎯

Branch `proof/cantor-bad-normal`.  Target `CantorBadNormal.exists_mem_cantorSet_bad_isNormal_coprime_three`,
never restated.  The headline now runs `exists_of_law_ae resLaw ← ae_isNormal_resLaw_of_localDeadBias`, whose
open leaves are the two standard leaves `ae_cesaro_condDiff` (martingale part) and `cesaro_contChar_small`
(Weyl + `∫ Π cos² = 2^{−C}`), and the crux `localDeadBias_resLaw`.
- **Mandated next move:** prove the two standard leaves (martingale part first), then attack the crux scale by
  scale: a second martingale split at a coarser prefix leaves the phases `e(hbⁿ p/q)` of the obstacle rationals
  in a coarse cylinder; state that equidistribution as the next node.
- **Forbidden drift:** `midStages`, `StageSaving` and every per-stage μ_K-tail bound (a rate there needs
  Baker-type equidistribution of `n log₃ b`); any-rule arguments (they reduce to `DeadRateDecay`, believed
  false); restating the headline or the law.
- **Why:** the probe `scripts/cantorbad_localbias.py` finds no coherent dead bias for `resLaw` (bases 2, 5, 7;
  inflation 1.00 ± 0.01) while the dyadic control shows coherence 0.96, and the local route needs only
  irrationality of `log₃ b`.
- **Operator answer to the lap-9 STUCK note (2026-10-06 13:50, Ren):** rescope accepted.  The scope is the
  **headline path**: done means `#print axioms` of the headline is free of `sorryAx`, and the multi-lap research
  crux `aliveOffMix_resLaw` is the accepted work, so an unreachable `sorry-free:` file gate is **not** a reason
  to call `box stuck`.  Mandated mechanical move (first thing the next lap does, one commit): move the two
  off-path open nodes `midStages` and `fourierPairRate_descent_of_deadRateDecay`, with the declarations only
  they use, verbatim into a new sibling file `src/NormalNumbers/CantorBadNormalRetired.lean` (imports
  `CantorBadNormal`; statements, docstrings and confidences unchanged; BarrierAudit waivers/links repointed).
  That makes the host gate `sorry-free:CantorBadNormal.lean` mean exactly "headline proved".  Then back to
  `AliveOffMix`: the large sieve is closed (PENDING lap 9); the live mechanism is the arithmetic of `bᵐ mod q`
  over obstacle denominators, tested against the working dyadic control (`R = .977`).

- **Run directive (2026-10-06 evening, Ren; Trevor authorized): probe-gated numerator-averaging run.**
  Lap 10 showed that, through the preperiodic families (3-free denominator | 3^ℓ±1), averaging over m needs the
  middle ternary digits of hbᵐ (Korobov at length ≍ log modulus; open).  The one live route averages over the
  obstacle NUMERATORS instead.  Order of work:
  1. The mechanical move above (`CantorBadNormalRetired.lean`), one commit.
  2. **Probe first** (`scripts/cantorbad_numdisp.py`): for the preperiodic obstacle families at depth L, measure the
     resLaw/μ_K-weighted numerator dispersion that the averaging argument needs, i.e. whether
     `Σ_p w(p) e(a·p/3^k-part)` over the obstacle numerators in a coarse cylinder shows √-cancellation in `a`, and
     whether the resulting bound on the AliveOffMix pair sums decays in L.  Known-answer controls in the same
     pipeline: b = 3 and dyadic centres must NOT cancel; b = 2, 5, 7 are the test.  Report only what separates them.
  3. **If the probe separates:** state the dispersion statement as a Lean node, prove its wiring into
     `AliveOffMix` (or the preperiodic part of it), then attack it.
  4. **If it does not:** record the route as closed in `Maze.lean` (a row citing the probe-backed node, believed
     false, plus `pow_phase_recur` and the middle-digit obstruction), update BarrierAudit, and call `box done`.
     A clean refutation is a successful run.

Directive history:
- 2026-10-06 evening: probe-gated numerator-averaging run (Trevor: "of course you should!").
- 2026-10-06 13:50: operator rescope to the headline path; off-path sorries move to `CantorBadNormalRetired.lean`.
- 2026-10-06 (cantorbad lap 6): local route adopted; `midStages` off-path.
- 2026-10-02: normality's master conjectures (below, superseded on this branch).

## Branch directive (2026-10-06, `proof/cantorexp-stretch`, DONE): land the stretch node

**Objective:** prove `ev_expTest_mass_all` (`CantorExactExponentStretch.lean`), which closes the
frozen node `ae_not_liouvilleWith_all` and the stretch headline (both already wired).
**Mandated next move:** the crux leaf `hit_mass_padic` first (with `padic_sep`,
`card_image_mod_HS_le`), then `farey_sep` / `hit_mass_farey`, then the case split.
**Forbidden drift:** no more pricing of Kloosterman / inverse-sum / BFR routes for this node
(the 3-adic Farey separation supersedes them); no edits to frozen signatures.
**Why:** the review lap found the crux elementary (count `≲ (|r|q)^{log₃2}`); what remains is
formalization of six elementary leaves.

## Directive history
- 2026-10-06: stretch lane → prove the six Farey-separation leaves (supersedes the 2026-10-02
  directive on this branch only).

## PREVIOUS DIRECTIVE (2026-10-02): normality's master conjectures 🎯

Follow `KICKOFF-2026-10-02-master-conjectures.md`: prove the three planted consequences of
`BorelConjecture` / `BaileyCrandallHypA` (`src/NormalNumbers/MasterConjectures.lean`), grow the
consequence graph, then run the Maze test.  Frozen statements stay byte-identical.  The run is done
only when all three phases are, not when the file is sorry-free.

🅿️ **Parked node, not a directive (2026-10-05):** `LiteratureDigitsOfPowers.SmoothDigitOmission`, the
integer-digit crux under Erdős #406, zeroless `2ⁿ`, and persistence ≤ 11 (Numberphile sweep).  Open
question for the consequence graph: does any repo master conjecture imply it?  No link is claimed.
  2026-10-06 `/create`: Erdős #406 now hangs off a sharper, decidable-per-instance node,
  `ErdosTriples.GapTwoTriples` (`C(1, 4ᵃ, 4ᵃ⁺ᵇ) = {0}` for `a, b ≥ 2`), wired by the proved
  `erdos406_of_gapTriplesEventually`; it would also give `E(ℤ₃) = {0}`.  Detail and data:
  `docs/ERDOS-TRIPLES-2026-10-06.md`.  Parked, not a directive.

## Completed runs 🏁

**Joint Lambert, unconditional + quantitative (closed 2026-09-30, merged 2026-10-02).**  Simultaneous
Lambert disjunctivity for any finite set of distinct bases, with `≥ N^(1−ε)` common-position
occurrences (`jointWords_quantitative`, `JointLambertQuantitative.lean`).  Gives a hypothesis-free
proof of Campbell arXiv:2605.24160's question (every binary string occurs infinitely often in `E`),
first answered on paper by CaptainSude (`Literature.Campbell.CaptainSude2026EDisjunctive`).

**Growing-prime localized logarithm (2 laps, closed 2026-10-02).**  `zetaY_isNormal` +
`exists_unbounded_zetaY` (`src/NormalNumbers/GrowingLocalizedLog.lean`), conditional on the cited
`VandeheyThm51` only.  Route: `KICKOFF-2026-10-02-growing-localized-log.md`, audit repairs applied
(cutoff `N·exp(−(log log N)³)`, per-segment depth).

**Quantitative C′ (2 laps, closed 2026-10-02).**  `cPrimeQuant_holds` and
`cPrimeResidueRich_holds` (`src/NormalNumbers/CPrimeQuant.lean`), unconditional; route as in
`KICKOFF-2026-09-30-cprime-quantitative.md` (Fejér Erdős–Turán, fixed-`u` schedule, Mertens in
APs ≤ 9/φ(q)).  The quadratic sharpening `CPrimeResidueQuad` stays walled (Maze "site
factorization via log-power BV").

**Vandehey §7 Problem 1 (laps 27–91, closed 2026-09-29).**  Not solved.  The deliverable is the
machine-checked map of closed routes: **`docs/VANDEHEY-S7-FALSE-STARTS.md`**, with every verdict
aliased in `src/NormalNumbers/Maze.lean` and the surviving machinery listed there.  The three
findings a future lap must not re-derive:

1. the crux (`BlockForget` → `BlockForgetGen` → `BlockForgetRun` → `BlockForgetAll`) is the headline
   PLUS locality — the SIGNED form is equivalent to the goal in both directions (S7-NR) and
   `abs_gap_witness` shows the absolute values are not free (S7-CK);
2. the scalar debts (`WidthAfford`, `MeanSlack`, `ClockLinear`) were artefacts of a transducer
   throttled to one digit per read: the throttle's queue makes the wide times have density zero, so
   the hypothesis is false and the width-filtered crux is vacuous on the same run (S7-WQ); the
   greedy transducer (S7-GR) does not have this defect and keeps `freq(width < η) ≍ √η`;
3. the wall is joint equidistribution of `(state, input point)`; in its sharpest form, a
   no-concentration statement about the image orbit near cylinder boundaries (S7-GS).

The frozen targets `vandeheyS7_mul_phi` / `vandeheyS7_add_phi` stay in the build, never weakened.
`GaussACRigidity` remains cited and unused by the surviving architecture.


## Standing rules (bind every lap)

1. **Guard rule.**  A lap may not hand the chain a new `Prop` unless the same lap also lands, in
   the kernel:
   - a *content locator*: the trivial or extremal instance, which shows where the content is not;
   - a *degenerate-case verdict* for the empty, singleton, truncated/boundary and
     constant-function configurations.
   A reduction without both is not an advance.  This rule was installed at C3/MRT lap 115, after
   laps 112-114 "reduced" the debt to statements that were false: a stronger statement looks
   cleaner and dies on a singleton block.
2. **Refutations are progress, and are recorded as Lean data.**  Every walked dead end gets a row
   in `src/NormalNumbers/Maze.lean`, aliased onto the refuting theorem.  Read the Maze before
   proposing a route.
3. **Literature inputs are named hypothesis `Prop`s**: cited, faithful or weaker, never `axiom`.
   **New math comes first.**  A literature input stays assumed until a new result needs it
   discharged; then proving it is a side quest (Philipp and Wall were proved this way).
4. **Frozen statements stay byte-identical.**  A campaign's ratified headline and its frozen
   modules are pinned by commit in that campaign's kickoff.  Statement freezing is JUDGE-owned
   (`JUDGE.md`).
5. **A false contract is recorded as an obstruction, never silently weakened.**
6. **Every new module goes in the root import** (`src/NormalNumbers.lean`), so `lake build`
   covers it.

## Standing charter (destination)

The project harvests the digit-reading dynamics of real numbers: normality, disjunctivity,
continued-fraction normality, and the richness of arithmetic constants such as `∑ ω(n)/bⁿ`.
Moonshot lane: aim at the open conjectures (C1-C3 of the casting-out programme, Vandehey's
open problem), and treat a conditional theorem on an honestly labelled literature input as a
real advance.
