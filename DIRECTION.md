# DIRECTION — normal-numbers 🧭

## OPERATOR OBJECTIVE 2026-09-28: `PENDING_WORK.md` queue items 1-3 — **COMPLETE 2026-09-28**

1. Prove `moshchevitinShkredov_cf_false` in `MoshchevitinShkredovRefuted.lean` (witness
   `[0;1,2,3,…]`), wire the file into `src/NormalNumbers.lean`, and add a Maze row marked
   "false as stated".  `moshchevitinShkredov_cf` stays byte-identical.
2. Add a C3 headline that consumes `uniformResonantMass_holds` in place of the `hURM` hypothesis
   of `conjC3_of_geom_input_band`.  Then retire `highResonantMass_le_narrow` /
   `C3MrtURMLowHigh.lean` as a redundant second route, with a Maze row and no sorry left on it.
3. Retire `VandeheyAutomaton.exists_jointFreq_limit`, whose `Synchronizing` hypothesis cannot
   hold (`archive/probe/PROBE-2026-09-27-transducer-not-synchronizing.md`), with a Maze row.

Keep `lake build` green at every commit.  Update `STATUS.md` and remove each finished item from
the `PENDING_WORK.md` queue.  **Stop when all three are done.**  Nothing else is in scope.

**All three landed 2026-09-28** — see the dated lap note in `PENDING_WORK.md`.  Items 1 and 3
each landed as a *theorem*, not just a Maze row: `moshchevitinShkredov_cf_false`, and
`not_synchronizing_of_injective_quotient` (which turns the transducer probe into a kernel
obstruction).  Item 2's headline is `conjC3_of_geom_input_band'`.  The queue is renumbered;
its new item 1 is the Vandehey crux `ClassEquidistribution` / `vandeheyUniformFreq_holds`.

---

**No active objective beyond the one above.**  Every campaign branch was merged on 2026-09-27 (`f5034b6`).  The next
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
