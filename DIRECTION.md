# DIRECTION — normal-numbers 🧭

## CURRENT DIRECTIVE (altitude-owned; outranks HANDOFF) — set lap 1, 2026-09-28

**Objective.** `vandeheyUniformFreq_holds` (`LiteratureVandehey.lean`), via the single leaf
`MobiusCFNScale`.  The Smith shortcut of the operator objective is **already discharged**
(`VandeheySmith.lean`, sorry-free): composite `D`, the diagonal factor, division and all of
`GL₂(ℤ)` are gone.  So that instruction is spent; what remains is the leaf.

**Mandated next move — the §5–§6 output-frequency engine, ABSTRACT, in `src/`.**
Three laps have built the *input* side (Raney §2, the bijectivity-free pin, Doeblin at a common
target).  The *output* side (Vandehey Lemma 4.3 + §5 triggers + §6 assembly) has never been
touched, and it is the route-decisive piece: if output-word frequencies cannot be read off the
joint (window, state) frequencies, the whole automaton build is worthless.  Build
`VandeheyOutputFreq.lean` on the hypothesis our machinery actually delivers — the **factorized**
joint limit `ρ(q,t) = ν(t)·γ(I_q)` that `tendsto_jointCount_of_classEquidistribution` already
produces (strictly stronger than Vandehey's `ρ ≪≫ μ̃`, and it makes countable additivity free):
1. `gaussMeasure (allWordsEvent m) = 1`, and finite subfamilies of `allWords m` of measure `> 1−ε`.
2. **The upper-bound engine**: for a weighted family supported on `allWords m`,
   `limsup (1/n)·Σ_{i<n} a(wᵢ)·1[tᵢ=t] ≤ ν t · Σ_w a(w) γ(I_w)`.  The finite-subfamily
   escape is what replaces the tightness patch the published §3 needs.
3. The assembly: bucket the trigger family by word length, finite truncation below `m`,
   `K·1_{U_m}` above, `τ_m = Σ_t ν t·γ(⋂-limit) → 0` as the one honest hypothesis.

**Forbidden drift.** Do NOT spend this run on `raneyNorm`/`RaneyState`/the common-target reach
(HANDOFF's NEXT 1–3).  They are derisked numerically and are supply, not crux.  Do NOT open the
`PrimeIntervalSupply` side item until the output engine has a stated theorem in the kernel.

**Why.** Hardest-first.  The output side is the only piece whose feasibility is in real doubt,
and its shape dictates what the automaton must supply — building the automaton first risks
supplying the wrong thing.

Directive history:
- 2026-09-28 lap 1 (review): crux switched from the automaton supply side (HANDOFF NEXT 1–3) to
  the §5–§6 output-frequency engine; factorized joint limit adopted as the hypothesis shape.

---

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
