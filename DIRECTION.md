# DIRECTION — normal-numbers 🧭

## Current Lambert status, 29 September 2026

The bounded qualitative Lambert objective is complete: `f6fbf87` proves the original
common-position theorem unconditionally.  [Completed proof](docs/JOINT-LAMBERT-RESCALED-PROOF.md).
The [next quantitative target](docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md) has a paper derivation
of `N exp(-C (log log N)^2 log log log N)` occurrences for every sufficiently large N.
No new treadmill is launched by this documentation update.  The older AGP-only status
below is historical; proving AGP is not the next Lambert obligation.  Vandehey work is
separate, in the main checkout.


## CURRENT DIRECTIVE (altitude-owned; outranks HANDOFF) — set lap 4, 2026-09-28

**Objective.** `vandeheyUniformFreq_holds` (`LiteratureVandehey.lean`).  The output side
(§4–§6) is DONE (laps 2–3).  What is left is the **input/supply** side: the six named
hypotheses of `VandeheyOut.mobiusUniformFreq_of_transducer` for the concrete L/R machine.
`hK`, `hkK`, `hout` are closed.  The crux is now `hjs : JointStateFreq lrDelta s₀ ν`.

**⚠ ROUTE FINDING (lap 4, numeric + structural) — the planned supply route is BLOCKED as
stated, and the repair is identified.**  `classEquidistribution_of_common_reach` needs a
common target reachable from EVERY state by a genuine word of ONE fixed length.  The Raney
automaton `lrDelta` can NEVER satisfy that: `det (M · B_j) = −det M`, so the sign of the
determinant is a **deterministic period-2 phase** on the state set, and states of opposite
phase are never simultaneously occupied.  Probe `scratch/raney_reach.py`: for `D = 2,3,5,7,11,13`
common targets exist but NO uniform length does.  The transfer-operator pin
(`stateHorizonIntegral_pin_of_reach`) is therefore FALSE for `lrDelta` — a periodic chain's
`n`-step kernel does not converge.

**The repair (verified numerically, lap 4).**  `ι M := J · M` (swap the rows) satisfies
`ι ∘ lrDelta = lrDelta ∘ ι`, `det (ι M) = −det M`, and `lrOut (ι M) j = (lrOut M j).map not`.
So on `RPlus D := {M // IsRD D M ∧ M.det = D}` the **phase-corrected** automaton
`δ̄ P a := ι (lrDelta P a)` is a genuine finite automaton with `stateAt lrDelta … i = ι^i (stateAt δ̄ … i)`,
and it is APERIODIC: probe `scratch/raney_plus.py` shows every `P ∈ RPlus D` reaches
`z = diag(1, D)` in EXACTLY 2 steps, for every prime `D` tested (2…13), with digits `≤ D`.

**⚠ SECOND ROUTE FINDING (lap 4, numeric) — the capstone's hypothesis SHAPE is wrong.**
`mobiusUniformFreq_of_transducer` assumes `JointStateFreq`, i.e. the joint (window, state)
frequency FACTORIZES as `ν t · γ(I_q)` with one `ν`.  `probes/raney_joint_product.py` refutes
that for the concrete machine: at `D = 3`, four of the fourteen Raney states have
`ρ(q,t)/γ(I_q)` varying by up to **20 %** across short `q` (≈15σ over 2.1M Gauss CF digits),
while at `D = 2` it does factorize — because there the stationary law is uniform, and a uniform
law is invariant under each individual digit's action.  The Raney digit steps are not injective,
so the state at `i` stays correlated with the digits abutting the window at `i`.

**Mandated next move — four steps, in this order, in `src/`.**
1. Finish `VandeheyRaneyReach.lean`: `RPlus D` as a `Fintype`, `rplusDelta`, and
   `rplus_common_reach` — every `P ∈ RPlus D` reaches `diag(1,D)` in EXACTLY 2 genuine digits.
   The four ingredients are already in the kernel (lap 4); this is assembly.
2. **De-factorize the output side.**  Replace `JointStateFreq δ s₀ ν` by a general
   `ρ : List ℕ → S → ℝ` and port `VandeheyOutputFreq.lean`.  The factorization was adopted only
   to control the infinite alphabet's escape mass, and that is recovered for free from
   `ρ(w,t) ≤ γ(I_w)` (`jointCount ≤ winCard`) plus the already-proved
   `exists_boundedWords_sum_gt`.  Then restate `mobiusUniformFreq_of_transducer` against `ρ`.
3. `hjs` = `ClassEquidistribution (rplusDelta hD) t q` for each `q`, from step 1 via
   `classEquidistribution_of_common_reach`, PLUS the **parity split**: `jointCount lrDelta` lives
   on one parity of `i`, so it is `½(jointCount rplusDelta ± Σ_i (−1)^i …)`, and the signed half
   is FREE from the existing two-point machinery (`abs_integral_devFun_mul_le` bounds an
   ABSOLUTE value, so inserting `(−1)^k` changes nothing in `integral_devAvg_sq_le`).
4. `hlen`, `hgen`, `htail`.

**Forbidden drift.**  Do NOT attack `hlen` by the cone-perturbation route of the lap-3 handoff:
lap 4 found Vandehey's own §6 proof makes `ℓ(n)` a Birkhoff sum of a BOUNDED window/state
function (augment the state with the last emitted letter), so `hlen` is a COROLLARY of `hjs`
plus the `wCount`/`wLimit` machinery already in `VandeheyOutputFreq.lean`, not an analytic leaf.
Do NOT open `PrimeIntervalSupply` until `hjs` has a stated theorem in the kernel.
  ↳ **PREREQUISITE SATISFIED, lap 6** (`VandeheyTransport.jointStateFreq_lrDelta`,
  `VandeheyTransportB.jointStateFreq_lrB`), and the gate is DISCHARGED: see the
  2026-09-28 (c) operator objective below, under which `PrimeIntervalSupply` became a
  theorem at `3ddc0b6`.

**Why.** Hardest-first.  `hjs` is the only remaining obligation whose feasibility was in doubt,
and lap 4 showed BOTH the published route to it and the hypothesis shape it was aimed at are
wrong; the phase quotient and the de-factorized `ρ` are the repairs, and until they are in the
kernel every other leaf is building on sand.

Directive history:
- 2026-09-28 lap 1 (review): crux switched from the automaton supply side (HANDOFF NEXT 1–3) to
  the §5–§6 output-frequency engine; factorized joint limit adopted as the hypothesis shape.
- 2026-09-28 lap 4 (review): output side done; crux switched to `hjs`.  Recorded (a) the period-2
  determinant obstruction that kills the uniform-length common reach, with the `ι = J·−` phase
  quotient that repairs it, and (b) the numeric REFUTATION of the factorized `JointStateFreq`
  shape, with the `ρ(w,t) ≤ γ(I_w)` escape that makes de-factorizing free.  `hlen` demoted from
  "analytic leaf" to corollary of `hjs`.

---

## OPERATOR OBJECTIVE 2026-09-28 (c): joint-Lambert prime inputs + AGP gap map — ✅ COMPLETE

**Scope: bounded, at most TWO laps, and NOT a Vandehey assembly campaign.**  Trevor's
authorization, 2026-09-28: "Go for it! It's an interesting claim".  This section is scoped to the
joint-Lambert analytic inputs only; the Vandehey objective (b) above and the `PENDING_WORK.md`
queue are **untouched and still live**, and no Vandehey implementation is modified under it.

The lap-4 gate above ("do not open `PrimeIntervalSupply` until `hjs` is a theorem") is satisfied:
lap 6 proved `hjs` twice over.  So this objective supersedes that gate for the interval-supply
item only.

**Deliverables (all met, lap 7, `3ddc0b6` + this commit).**
1. `src/NormalNumbers/JointLambertPrimeInputs.lean`, namespace `NormalNumbers.JointLambert`:
   * `primeIntervalSupply_holds : PrimeIntervalSupply`
   * `jointLambertDisjunctivity_of_agp (hagp : AGP) : JointLambertDisjunctivity`
   * `jointWords_two_four_of_agp (hagp : AGP) : JointWords {2,4}`
   Exact frozen headline types, no extra hypotheses, `#print axioms`-clean.  Every
   pre-existing `JointLambert*.lean` byte-identical to `7b17c44`.
2. `docs/JOINT-LAMBERT-AGP-GAP.md` — the AGP gap map against the **installed** dependency
   versions: what is proved, what is only stated, which gaps are adapters, and the one
   substantial missing analytic theorem (a log-free zero-density estimate).  Names
   `AGPExpRange` as the single concrete next target.

**Recorded finding.** Interval supply is an *ordinary* PNT consequence, not PNT-in-AP; the
`STATUS.md` row that called both hypotheses "PNT-in-AP strength" was wrong and is corrected.
`AGP` is the only analytic hypothesis the joint headline still rests on, and §4 of the gap doc
shows no averaged absolute-error bound (including Bombieri–Vinogradov) can supply it — the
obstruction is structural, not a constant.

---

## OPERATOR OBJECTIVE 2026-09-28 (c): finish (b) (bounded, at most 4 laps)

Objective (b) below still stands.  Its analytic inputs are proved (`HANDOFF.md`, lap 6).  What
remains, in order:
1. Restate `mobiusUniformFreq_of_transducer` on the run clock.
2. Close `hgen`, `htail` and `hcof`.
3. Assemble `vandeheyUniformFreq_holds`.
If a lap is left over, do (b)'s `PrimeIntervalSupply` side item.  **Stop when
`vandeheyUniformFreq_holds` is proved, or at the lap cap.**

## OPERATOR OBJECTIVE 2026-09-28 (b): the Vandehey crux, plus `PrimeIntervalSupply` (bounded, at most 8 laps)

**Main target:** prove `vandeheyUniformFreq_holds : VandeheyUniformFreq`
(`LiteratureVandehey.lean`), which completes Vandehey 2017 Thm 1.1: Möbius images of CF-normal
numbers are CF-normal.
- Start from `archive/handoff/HANDOFF-2026-09-28-0935.md` (the "next crux" section) and
  `archive/handoff/HANDOFF-2026-09-28-vandehey-bridge-CLOSED.md`.  The open input is
  `VandeheyCocycle.ClassEquidistribution` wherever the class automaton does not already supply it.
- **Lap 1 evaluates the Smith-normal-form shortcut first.**  Every nonsingular integer matrix is
  `U · diag(d₁,d₂) · V` with `U, V ∈ GL₂(ℤ)`.  For the `GL₂(ℤ)` factors, CF tails agree
  (Serret), and `x ↦ Dx` for prime `D` is covered by `tendsto_jointCount_classStep`.  So record
  whether composite `D` and the diagonal reduce to the prime case.  If the shortcut fails,
  record the precise obstruction in the Maze and follow the bridge-CLOSED handoff's NEXT list.
- `VandeheyUniformFreq` stays byte-identical.  The guard rule applies to every new `Prop`.

**Side item (one lap at most):** prove `PrimeIntervalSupply` (`JointLambertPrimeSelection.lean`,
which stays frozen) in a new module, as `primeIntervalSupply_holds`.  The Erdős 446 dyadic prime
bound in the lean-proofs dependency
(`ErdosProblems/Erdos446/PrimeDyadic.lean`, `eventually_primeCounting_tenth_bounds`) is likely
stronger than the statement.  Then add the corollary: `jointLambertDisjunctivity` from `AGP` alone.

Keep `lake build` green at every commit and update `STATUS.md` and the `PENDING_WORK.md` queue.
**Stop when `vandeheyUniformFreq_holds` is proved, or at the lap cap.**  A precise recorded
obstruction counts as an advance.

---

**No active objective.**  The last run (2026-09-28, queue items 1-3) completed; its record is
`archive/handoff/HANDOFF-2026-09-28-0935.md`.  Every campaign branch was merged on 2026-09-27 (`f5034b6`).  The next
run gets its objective from the operator: a kickoff file, plus a dated section added at the top of
this file that names the target theorem and the stop condition.  To choose one, read the open
fronts in `STATUS.md` and the queue in `PENDING_WORK.md`.

The full directive history up to the merge is in `archive/DIRECTION-to-2026-09-27.md`.  Read it
for provenance only.  It has no authority over a new run.

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
   Proving one is a side quest in its own right (Philipp and Wall were proved this way).
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
