# Kickoff: G4 disjunctivity — formalization campaign, lap 1

*Staged by Ren for Trevor, 2026-09-13 23:10 EDT.  Branch `wip/g4-disjunctivity` in the main
worktree `~/src/normal-numbers`, from `master` @ `e3d7303`.*

## The specification

The full brief is
`~/personal/claude/knowledge/core/projects/normal-numbers-g4-disjunctivity-fable-handoff-2026-09-14.md`
(read-only in the box).  **Read it before editing.**  This file only records the staging decisions
and what lap 1 owes; it does not restate the mathematics.

Target: the candidate proof that

  G4 = ∑_{p prime} 1/(4^p − 1) = ∑_{n≥1} ω(n)/4^n

is disjunctive in base 4, and hence in base 2.  This is a **candidate**, not an established theorem.
Lean is being asked to test the argument, not decorate a known conclusion.

## Staging decisions already made (do not redo)

- **Worktree**: the main tree `~/src/normal-numbers` on `wip/g4-disjunctivity`.  Two sibling
  worktrees are live on other campaigns — `~/src/nn-fable` (`wip/adder-tower-c9`, hitting sets) and
  `~/src/normal-numbers-cfsched` (`wip/cfschedulea-prop-nodes`).  Do not touch either, and do not
  touch `Adder*`, `CF*`, `Mahler*`, or `LnTwo*` files.
- **Deps**: `lake-base status 4.33.1` is fully built and this tree's `.lake` is a CoW clone of it.
  Never start a fresh unshared dependency download.
- **Commits**: the pre-commit hook refuses `master`; that is why the branch exists.  Commit green
  integrated work as you go with `git-safe`.

## Frozen endpoint — pin this before decomposing anything

New declarations (proposed names; these do **not** exist yet):

1. `primeLambertFour : ℝ` — a *new* base-four constant.  ⚠️ `PrimeLambertDefs.primeLambert` is the
   **base-two** series `∑' n, omegaR n / 2^n`.  Do not redefine it, do not generalize it in place in
   a way that changes what existing theorems mean.  A `primeLambertAtBase` with `primeLambertFour`
   as the `b = 4` instance is fine.
2. Summability of `fun n => omegaR n / 4^n`, and **equality of the two displayed series** —
   `∑_{p prime} 1/(4^p − 1) = primeLambertFour`.  This identity is not yet proved anywhere.
3. `NormalNumbers.IsDisjunctive 4 primeLambertFour`.
4. `NormalNumbers.IsDisjunctive 2 primeLambertFour` — via the **existing**
   `Disjunctive.isDisjunctive_pow_iff` at `b = 2`, `k = 2`.  Do not spend a lap re-proving it.
   `isDisjunctive_iff_forall_occursAt` supplies the finite-word reading.

## Lap 1 checkpoint (this is the whole objective for lap 1)

1. Pin the endpoint statements above in a new file (`PrimeLambertFour.lean` or similar), with
   whatever is not yet proved stated as explicit named `Prop`s.
2. Write the **dependency graph** as named, inspectable propositions, one per handoff §4 half:
   - **A** grid / tensor cancellation / exact affine Lambert transport (§4A)
   - **B** zonotope volume + spectral `log det(I + AAᵀ) = O(r√K)` (§4B)
   - **C** uniform joint small-prime Fourier control on the whole box ‖q‖∞ ≤ D (§4C)
   - **D** three-range remainders: p ≤ R, R < p ≤ Y, p > Y, plus the infinite far tail (§4D)
   - **E** Jackson smoothing and the finite contradiction (§4E)
   - **P** the §5 parameter schedule, in its own module.
3. **Prove the finite separating-test contradiction** (E), conditional on A–D as hypotheses, with
   explicit error budgets.  A conditional wiring theorem is the lap-1 deliverable; it is a
   checkpoint, **never** reportable as the unconditional endpoint.
4. Then take one load-bearing lemma far enough to prove it or expose an exact missing premise.
   Prefer **B** — the geometry is the crux and the least likely to survive contact.

## Hard constraints

- ⚠️ **Bounding the zonotope by a coordinatewise box loses the estimate that closes the proof.**
  Use the average coordinate torus distance, not the product sup metric.
- ⚠️ The pointwise very-large-prime argument **does not handle all primes above R**.  Keep the
  three ranges separate and preserve the signed cancellation in the medium range.
- ⚠️ Do not freeze K and then send X → ∞.  One simultaneous limit, per §5.
- **Never** introduce a trusted axiom for a candidate mathematical lemma, and never present a
  hypothesis carrying the hard result as though it were proved.
- Do not inherit the G2 two-point correlation theorem, and do not chase the multiplicity, entropy,
  ordinary-normality, or historical-novelty questions this campaign.
- `PrimeLambertOscillation.lean` is the old irrationality endpoint with unfinished holes.  It is
  neither a prerequisite nor a shortcut.  Don't route through it.

## Reporting

Report **what mathematics was proved, refuted, or isolated**, with declaration names and an updated
dependency map.  Do not report sorry counts, or their direction, as progress — decomposing one fat
`sorry` into named leaves is an advance.  A refutation that closes an invalid route is a successful
outcome: record the exact original statement, a concrete counterexample (formalized if you can),
which downstream implication fails, and the weakest repair actually justified.

Leave a durable handoff at `HANDOFF-<timestamp>-g4.md` so the next lap resumes from the real
frontier.  Do not publish, contact anyone, or open public discussion.
