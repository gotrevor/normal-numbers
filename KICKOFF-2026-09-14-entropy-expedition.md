# Kickoff: G4 entropy expedition — lap 1

*Staged by Ren (Claude) for Trevor, 2026-09-14 11:00 EDT.  Branch `wip/g4-entropy` in the main
worktree `~/src/normal-numbers`, from `wip/g4-disjunctivity` @ `bad77d8`.*

## The specification

`BRIEF-entropy-expedition-2026-09-14.md` (repo copy; the KB original is
`~/personal/claude/knowledge/core/projects/normal-numbers-entropy-expedition-fable-2026-09-14.md`).
**Read it before editing.**  This file records staging decisions and what lap 1 owes; it does not
restate the mathematics.  The DIRECTION override at the top of `DIRECTION.md` is the active
objective and outranks the G5 CURRENT DIRECTIVE beneath it.

## Staging decisions already made (do not redo)

- **Engine/model**: claude engine, grind laps on **Opus** (Trevor, 2026-09-14: low on Fable
  tokens, prefer Opus treadmills).  The brief's "Fable as lead" is overridden for this run.  Review
  laps are Opus/xhigh (treadmill default).  No Astra, no escalation to it.
- **Worktree/branch**: main tree, `wip/g4-entropy`.  Sibling worktrees `~/src/nn-fable` and
  `~/src/normal-numbers-cfsched` are other campaigns - do not touch.  Do not touch `Adder*`,
  `CF*`, `Mahler*`, `LnTwo*`, `Stoneham*`, `PrimeLambertOscillation`.
- **Existing G4/G5 source is read-only** except where the brief §3A/§3C says to *expose* an
  existing internal identity or generalize a statement: do that by **adding** a lemma and
  recovering the old theorem as an instance, never by changing an old endpoint.  One writer per
  file.
- **Footprint**: new modules `G4Entropy*.lean` (suggested split: `G4EntropySample` for §2,
  `G4EntropyInfo` for the finite-probability lemmas, `G4EntropyCover` for §3B, `G4EntropyCapture`
  for §3C, `G4EntropyBudget` for §4, `G4EntropyFrequency` for §5, `G4EntropyTransfer` for §6),
  dated `HANDOFF-2026-09-14-entropy-lapN.md`, `PENDING_WORK.md`, `STATUS.md`.
- **Deps**: this tree's `.lake` is a CoW clone of `~/.lake-base/4.33.1` and was built green at
  `bad77d8` (8938 jobs).  Never start a fresh unshared dependency download.
- **Commits**: the pre-commit hook refuses `master`; commit green integrated work as you go with
  `git-safe`.  🚨 **Commit a compiling skeleton with named `sorry` leaves EARLY in the lap** - a
  lap that dies (output-token cap, window exhaustion) with nothing committed loses the hour.
- **Preserved declarations** (host-checked every lap via `--require-decls`):
  `G4ScheduleAssembly.lean : isDisjunctive_four, isDisjunctive_two`.  Also keep
  `isDisjunctive_base`, `primeSumAtBase_eq_primeLambertAtBase` and the definitions named in the
  override.
- **Completion**: there is no `--done-when`; the expedition ends by self-stop when the brief §8
  outcome is reached (E0/E1 settled AND T_E proved or refuted with a witness meeting its exact
  premise), or at the host duration cap.  Do not stop because unrelated `sorry`s exist elsewhere
  in the repo (Mahler/oscillation holes are not this campaign's).

## Lap 1 checkpoint (this is the whole objective for lap 1)

Brief §2 and §3C, in order:

1. **Freeze the sample** (`G4EntropySample.lean`): `k_{K,α}(n)`, the exact identity
   `n = t + d·k` on `P_K` from `GridParams.exists_mult_mul`, `m_K = K/4` (⚠️ not `Sched.m K`),
   `u^x_{K,α}(n) = fract(4^k x)`, `Z^x_{K,α}(n) = ⌊2^{m_K} u⌋`, the law of the **joint** vector as the
   pushforward of one uniform `n ∈ P_K`, and the dictionary `Z` = the `m_K`-bit binary block at
   zero-based position `2k`, proved against `digitOf`/`OccursAt`.  Record `P_K ≠ ∅`, coordinate
   ranges, and `H₂(Z) ≤ min(m_K H_K, log₂|P_K|)`.
2. **Finite Shannon entropy** with the explicit zero-mass convention (`G4EntropyInfo.lean`):
   reuse mathlib where it fits (search `Mathlib/Analysis/SpecialFunctions/BinaryEntropy`,
   `negMulLog`), otherwise a small self-contained definition.  Prove the **information-set
   lemma** (Markov on `−log₂ mass`: `Pr[Z ∈ B] ≥ δ/(2−δ)`, `|B| ≤ 2^{(1−δ/2) m H}`) - this is
   pure finite probability and is the first load-bearing piece.
3. **State (C) and (G)** as named `Prop`s with all side conditions explicit, wire the
   entropy contradiction `E0` conditional on them, and then take **(C)** as far as it goes:
   extract the bounded-Lipschitz bump argument from `G4Jackson`/`G4SeparatingTest` as a new
   lemma with the old `Frame.test` statement recovered as an instance.

A checkpoint containing only declarations with unproved hypotheses is preparation, not the
result (brief §2).  Lap 1 must end with at least one of: a proved information-set lemma, a proved
sample dictionary, or a proved load-bearing component of (C).

## Lap 2+ (do not start early)

§3A exact transported sample · §3B joint-box cover · §4 budget against `G4ScheduleParams` with
the proposed `D_K = (16K²2^{m_K})²` (an obligation, not a given) · §5 sampled-frequency
statement (S) · §6 T_E prove-or-refute, with the counterexample worker starting the
support/collision computation for `w_{K,ℓ}` as soon as §2 is frozen.

## Handoff discipline (brief §7)

At each lap record only: (1) which statement was proved / refuted / narrowed, with the
declaration or witness; (2) which bottleneck moved, incl. new assumptions or changed
quantifiers; (3) the next bounded test.  Two laps stalled on one assertion → the next review
lap decomposes it, isolates the missing premise, or records the refutation.  Sorry counts,
declaration totals and warnings are not progress metrics.
