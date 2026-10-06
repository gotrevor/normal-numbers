# DIRECTION — normal-numbers 🧭

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

Directive history:
- 2026-10-06 (cantorbad lap 6): local route adopted; `midStages` off-path.
- 2026-10-02: normality's master conjectures (below, superseded on this branch).

## CURRENT DIRECTIVE (2026-10-06, branch `proof/cantorexp-stretch`): land the stretch node 🎯

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
