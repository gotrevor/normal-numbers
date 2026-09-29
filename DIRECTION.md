# DIRECTION — normal-numbers 🧭

## CURRENT DIRECTIVE (altitude laps only write here; it OUTRANKS the HANDOFF) 🧭

**Set 2026-09-29 (review lap 88).**  Supersedes lap 77's directive.  Same destination.  The
ROUTE changes: off the absolute density bound (route B), onto **universality** (route A), because
the repo already owns route A's endgame and route B's instrument has a proved-out ceiling.

* **Objective.**  `AffineUniformFreq Real.goldenRatio 0` — *the image's word frequencies converge
  to a limit that does not depend on which CF-normal `x` is fed in.*  Nothing else counts.
  It already implies the headline, axiom-clean and with NO cited input
  (`affineCFN_of_uniformFreq`), and it is already factored:
  `affineUniformFreq_of_runClock : RunClock ℓ rate → SampledUniformCount q r₀ ℓ → AffineUniformFreq`
  (`VandeheyS7Clock`).  So the target is `SampledUniformCount` (plus the clock rate).

* **Why route B is demoted (fact (ε), this lap's finding).**  Route B wants
  `limsup freq ≤ C·γ(I_w)` with `C` uniform in `w`, then cites `GaussACRigidity`.  Its only
  surviving instrument is a cover of the state-dependent target by a FIXED finite family
  (S7-WD/WD′/CV/FT).  That cover cannot be afforded:
  1. **state-blind is impossible** — over the whole width-`≥η` state box the targets' union is all
     of `(0,1)`, so a cover valid for every state has mass `1`, not `C·γ(I_w)`;
  2. **net-indexed is quantitatively dead** — resolving a target of length `≍γ(I_w)` needs net
     precision `ρ ≲ γ(I_w)`, so the box carries `≍ρ^{-4}` cells and the unweighted cover mass is
     `≍γ(I_w)^{-3}`: `C` blows up as `|w|` grows.  The ℤ[φ]-separation of the reachable states
     (`|α|·|α^σ| ≥ 1` for `0 ≠ α ∈ ℤ[φ]`) says this is not an artefact of the net.
  So route B's residual is irreducibly the WEIGHTED joint statement `ClassFreqBound`, which needs
  the state's empirical law AND an absolute-continuity input.  Route A needs neither.

* **Route A's decomposition — the mandated program (`BlockForget`).**  With `f = slotObs w` and the
  skew product `pairStep` (S7-SK), the sliding-block identity turns the run's Cesàro average into
  the Cesàro average over `m` of `blockAvg (s_m) T w (G^m x)`.  Name
  > **`BlockForget`**: `∀ ε>0, ∃ T, ∀ states s s′, ∀ z ∈ (0,1),`
  > `|blockAvg s T w z − blockAvg s′ T w z| ≤ ε`
  — the block time-average forgets the initial state, uniformly in the input segment.  Then
  replacing `s_m` by ONE reference state `s*` makes the integrand a FIXED function of `z` alone,
  and CF-normality of `x` evaluates its Cesàro average (S7-WN + the interval/cylinder squeeze).
  Hence **`BlockForget` + CF-normality ⟹ `SampledUniformCount` ⟹ the headline.**
  `BlockForget` mentions no `x` and no normality: it is a statement about the skew product alone;
  it is what BOTH 2026-08-24/25 probes measured GREEN (the state law is KS-indistinguishable
  across four initial states from ~60 steps on); and pathwise non-merging (S7-CN: reading is
  inert) does not contradict it — time-averaging, not trajectory equality, is the right test
  (probe trap #2).

* **Mandated next move**, in this order:
  (a) `VandeheyS7BlockForget` — `blockAvg`, the sliding-block Cesàro identity, the statement
      `BlockForget`, and the architecture theorem down to the one named input;
  (b) the reference-state observable: `blockAvg s* T w ·` is an interval-step function of `z`
      (finite after a digit truncation) — the bridge to S7-WN/S7-CV;
  (c) then `BlockForget` itself: Birkhoff–Hopf / Hilbert-metric contraction on the fibre, with
      `disc` (S7-CN) as the comparison instrument and `distortion_runWord_le_two` as the
      contraction already in hand.
  Keep the scalar width debt (`MeanSlack`, `ClockLinear`): route A needs it for the CLOCK
  (`RunClock`'s rate), so that work is not wasted.

* **LAP-90 AMENDMENT (the crux's name has changed).**  `BlockForget` is REFUTED in the kernel
  (`not_blockForget`, S7-BX) and so is lap 89's CF-normal repair `BlockForgetGen`
  (`not_blockForgetGen`, S7-BY): the quantifier order `∃T, ∀z` fixes the block length before the
  input, and `blockAvg` at a fixed `T` is a finite-prefix functional, while CF-normality is a tail
  property.  S7-RR explains why no repair of that shape could work — the reference run IS the
  Gauss shift, so the `s' = refState` instance of the crux is the headline itself.  **The live
  crux is `BlockForgetRun`** (S7-BR): the same comparison, but only in CESÀRO average over the
  times the run actually visits, at the good (width-`≥η`) times.  That is the exact hypothesis the
  architecture consumes, it is strictly weaker (`blockForgetRun_of_gen`), and the refutations —
  single `(state, point)` pairs — do not touch it.  Everything else in this directive stands.

* **LAP-91 AMENDMENT (the width debt leaves the critical path; the crux is `BlockForgetAll`).**
  The lap-91 probe (`experiments/PROBE-2026-09-29-lap91-stall-and-width-walk.md`; exact `ℤ[φ]`
  arithmetic, output verified against the true CF of `x/φ`) reads the run as follows: the clock
  deficit STOPS (7 stalls in 18000 reads, so `runClock p/p → 1` — the crux at `[]` is measured
  green), while `log(1/width)` is a null-recurrent `√n` random walk — **for the rational map
  `(z+1)/3` as well**, where the theorem is known.  So `WidthAfford` and `MeanSlack` are false in
  SHAPE, not open; the single mechanism is the queue of known-but-unemitted output digits, whose
  returns to zero are the stalls.  Three consequences, all in the kernel:
  1. **S7-WQ** (`VandeheyS7WidthDensity`): sparse wide times make `BlockForgetRun` VACUOUS and
     `WidthAfford` FALSE — non-vacuity of the crux and satisfiability of the width debt are the
     same requirement.
  2. **S7-AW** (`VandeheyS7ArchWidthFree`): the architecture re-derived with the width filter
     deleted.  `BlockForgetAll` — the same comparison summed over ALL times — alone gives
     `isCFNormal_image_of_blockForgetAll`.  **`BlockForgetAll` is the crux from now on**; no
     `RefCesaro`, no clock hypothesis, no width affordability.  The scalar debts (`MeanSlack`,
     `ClockLinear`, `WidthAfford`) are OFF the critical path — do not spend laps on them.
  3. **S7-NR** (`VandeheyS7NoReduction`): the crux with the absolute values REMOVED is exactly the
     headline (`signedForget_iff_slotCountFreq`).  So the whole surplus of route A's front over its
     own conclusion is the absolute values, i.e. LOCALITY: the run's window statistics must track
     the input's window by window.  An attack that averages first is attacking the headline
     directly; the only thing route A adds is the local comparison.
  Also landed: **S7-LG** (`VandeheyS7LevelGen`) carries S7-RC's level constants to an arbitrary
  state and reduces the crux's FIXED-state coordinate to an arithmetic statement about finite sums
  of relative Gauss masses (`abs_blockAvgCesaro_sub_gauss_le_of_levelSum`).

* **LAP-91 AMENDMENT 2 (the width walk is an artifact of the THROTTLE — the instrument was
  broken, not the route).**  The repo's `step` emits at most ONE digit per read
  (`runWord_length_le_one`); Vandehey's transducer emits a variable-length word.  Re-running the
  same exact simulation with MAXIMAL emission (emit while emittable, then read) keeps
  `slack = log(1/width)` **bounded**: `[0, 12]` over 8000 reads for `z ↦ z/φ`, `[0, 3.4]` for the
  rational `z ↦ (z+1)/3`, against `25 … 590` and rising for the throttled run.  Emissions track
  reads to within 1%.  So the queue, the `√n` width walk, and the failure of
  `WidthAfford`/`MeanSlack` are all consequences of the throttle.  **The next program is the
  GREEDY transducer**: (1) `stepMax` with termination from the burst bound (`k` emissions force
  `width ≲ 1/fib(k)²`); (2) the greedy state is reduced after each read, with the step identity;
  (3) the width floor for reachable reduced states — which the probe says is TRUE and which is
  exactly what the scalar debts wanted; (4) re-wire `slotCount` and the sliding-block identity to
  the greedy run, recovering S7-BF/S7-RV with a SATISFIABLE width hypothesis and a non-vacuous
  crux.  S7-AW (width-free) remains valid as the fallback.

* **Forbidden drift.**  (i) New unweighted-cover machinery for route B (S7-WD/WD′/CV/FT are
  finished; do not extend them).  (ii) `ClassFreqBound`/`CellMemory` as the front — they are route
  B's residual, and `CellMemory` is a restatement (lap 80).  (iii) The window-function frame,
  bounded-error decompositions, Serret/commensurator, soft self-joining rigidity.  (iv) Finishing
  `GaussACRigidity` — route A does not use it; it stays cited.  (v) `StateClock` in the
  uniform-`η` form.

* **What the crux IS now.**  `BlockForget`: two states, the same input segment, one time-average.
  Facts (α)(β)(γ)(δ) all survive and none obstructs it — (α)'s counterexample families are not
  orbits of an autonomous map (S7-SK), (γ)'s rigidity is about pathwise identity, and (δ)'s box is
  where the two states live.  A lap that does not either build (a)/(b) or attack `BlockForget` is
  off-directive.

Directive history:
- 2026-09-29 (lap 91): width debt refuted in shape by the probe and removed from the architecture
  (S7-AW); crux renamed `BlockForgetAll`; S7-NR shows the signed crux is the headline, so the
  crux's only content is locality.
- 2026-09-29 (lap 88, review): ROUTE CHANGE — universality (`AffineUniformFreq`, which already
  reduces the headline with NO cited input) replaces the absolute density bound; fact (ε) kills the
  unweighted cover, and the new crux is `BlockForget` (block time-averages forget the initial
  state), which is `x`-free and probe-verified.
- 2026-09-29 (lap 27, review): window-function frame REFUTED; ε-scheme replaces the bounded-error
  engine; the ERGODIC route (`OrbitACBound` + `GaussACRigidity`) becomes primary, the
  state-indexed decomposition the fallback.
- 2026-09-29 (lap 30, review): leg 1 DISCHARGED (`VandeheyS7Golden`), so the crux is the whole
  chain; crux pinned as the predictable-set/`Γ\SL₂(ℝ)`-translate problem, with facts (α)(β)(γ).
- 2026-09-29 (lap 74, review): crux-neglect corrected; `StateClock`'s uniform width floor
  identified as the wrong shape by fact (β); the MEASURE side of the crux closed by S7-PB.
- 2026-09-29 (lap 77, review): fact (δ) — the reduced state set of width `≥ η` is a COMPACT BOX
  (box lemma + `denRatio` trapped by the read/emit recursion), so fact (α)'s "finiteness of the
  predictor's range" is available; the crux becomes `ClassFreqBound`, class equidistribution over
  a compact class space.

## OPERATOR OBJECTIVE 2026-09-29: Vandehey §7 Problem 1 🌙

**Target (open, Vandehey Compositio 2017 §7 Problem 1):** if `x` is CF-normal, is `φx` CF-normal?
Is `x + φ`?  Moonshot lane: the objective is a conjecture graph, not "prove X".  There is no
stop condition beyond the lap cap; a refutation of a route is an advance, and a lap succeeds by
advancing the crux, not by sorry count.

**Read first:** `papers/vandehey-2017-open-problem-attack-map.md` (§1 diagnosis, §2 dead ends,
§3 Route A with the three 2026-08-24 corrections), `experiments/PROBE-ROUTE-A.md`,
`archive/probe/PROBE-2026-08-25-1235-route-a-transducer.md`, and the Maze.  Serret/commensurator
and soft rigidity (self-joinings of geodesic flow) are dead; do not relitigate them.

**Graph to build:**
1. **Frozen targets.**  A new module `VandeheyS7.lean` (in the root import) stating
   `vandeheyS7_mul_phi : ∀ x, IsCFNormal (Int.fract x) → IsCFNormal (Int.fract (goldenRatio * x))`
   and `vandeheyS7_add_phi` (for `x + φ`), plus the general quadratic-irrational form as a Prop.
   These are open statements: `sorry`-free is not expected, and they are never weakened.
   Record the frozen names and commit in `HANDOFF.md`.
2. **The obstruction, as Lean.**  The Thm 1.1 pipeline (Raney normal form → transducer → class
   equidistribution → run clock, `VandeheyCapstone.lean`) needs a finite state set.  State as
   Props, with probes, where it breaks over `ℤ[φ]`: unit drift makes the reachable state set
   infinite; pathwise merging is impossible (`M⁻¹VM` integral forces `V` diagonal for
   `M = diag(φ,1)`); Lemma 2.2's bounded burst fails (`burst ≤ C + log(1+a)/Lévy` instead).
   Prove what is provable (infinitude of the state set, the non-merging fact) and add Maze rows.
3. **Route A: replace finiteness.**  The dynamics read only the real place.  Candidate nodes:
   a bounded-distortion window lemma for reduced post-emission states (the compact analogue of
   `entries ≤ D`; the integer descent does NOT port), a distributional merging statement
   (Birkhoff–Hopf cone contraction, not coupling), trigger windows with `ρ(∂U) = 0` in place of
   trigger strings, and the endgame either-or trick (verbatim for any `M`, so the problem reduces
   to "every string has a limiting frequency in `φx`, independent of the CF-normal `x`").  Wire
   each node to the frozen target by a theorem, even a conditional one.
4. **Reuse before rebuild.**  Factor the Thm 1.1 pipeline so its finite-state step is a named
   hypothesis; the new work supplies a compact-fiber substitute for that hypothesis.

Guard rule applies to every new Prop (content locator + degenerate cases).  A Prop that turns
out false goes in the Maze with its refutation, never silently weakened.

**Lap 1 side items (cheap, do first):** SwingC2 triage and the OVERVIEW refresh (Vandehey 1.1
proved, joint Lambert rests on AGP alone) from `PENDING_WORK.md`; prune them from the queue when
done.

---

Open fronts: `STATUS.md`.  Queue: `PENDING_WORK.md`.

Completed runs (the directive text is in git history, the outcome in `STATUS.md`):
- 2026-09-28 (a): Moshchevitin–Shkredov refuted; C3 headline without `hURM`; Vandehey automaton
  hypothesis refuted.
- 2026-09-28 (b)+(c): **Vandehey 2017 Thm 1.1 proved** (`vandehey_matrix_action_holds`, `6d7a8ad`).
- 2026-09-28 (joint Lambert inputs): `PrimeIntervalSupply` proved (`3ddc0b6`); AGP gap mapped
  (`docs/JOINT-LAMBERT-AGP-GAP.md`).

The pre-merge directive history is in `archive/DIRECTION-to-2026-09-27.md`.

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
