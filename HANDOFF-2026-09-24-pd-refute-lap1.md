# Handoff — pd-refute, lap 1: the boundary checklist is discharged, no counterexample

**Branch** `wip/pd-refute` · tree clean, NOT pushed · **Build**: full `lake build` green
**Objective**: `KICKOFF-2026-09-24-pd-refute.md` (supersedes `DIRECTION.md`; the CURRENT
DIRECTIVE has been re-set to match it).

## The crux and the confidence

**Crux**: `PairDecouple b p q t` (`SwingC1Decouple.lean`), the sole open input of
`conjC1_of_delange_katai_decouple`.  This worktree's target is its negation,
`not_pairDecouple_all` — still an open ratified `sorry`, and that is the honest state.

**Confidence that `PairDecouple` is TRUE: 92%** (Ren's prior: 85%).  Raised because (a) every
boundary case in the kickoff's checklist is now a *theorem* saying it cannot produce a bias, and
(b) the band decomposition shows the class deviation is produced by CRT counting error plus a
*cancellation* across prime bands — the intermediate truncations are worse than the full object,
which is the opposite of a conspiracy.

## What landed

Two new sorry-free modules (`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| file | content |
|---|---|
| `PairDecoupleLower.lean` | the twist identity; the test-function certificate (lower bounds on `pairDefect`); the finitary two-sided pin `‖fullMean f (QR)‖ ≤ 2·pairDefect + ‖∏ pairLocalFactor‖`; `not_pairDecouple_of_pairCorr_ge`; the degenerate cases (`P<2`, `p ≡ q mod r`, `primorialLe P ∣ p−q`, `P=2` odd) |
| `PairDecoupleAttacks.lean` | `classDeviation` (arithmetic-free `pairDefect`); all six kickoff attacks closed as theorems |
| `PairDecoupleBand.lean` | **the CRT half of `PairDecouple`, PROVED**: the crux decomposition `pairRemainder b P = band(P,y] + pairRemainder b y`, and `classDeviation(band) ≤ 4(R mod M)/R` with `M = bandModulus P y` coprime to `Q` — exactly `0` when `M ∣ R`.  Generic engine: `const_of_coprime_periods`, `sum_class_period_const`, `classDeviation_le_of_periodic_coprime` |

`probes/pair_defect.py` (stdlib only — the box has no numpy and no egress) with five
hand-computed controls, and three data files (`data-2026-09-24-pair-defect*.txt`).

## Read next, in order

1. `FINDINGS-2026-09-24-pd-refute.md` — the full account: what `PairDecouple` says after the
   twist, the checklist table, the degenerate family, the numbers, and the confidence argument.
2. `PENDING_WORK.md` top section — open items and the three things refuted this lap.
3. `DIRECTION.md` → CURRENT DIRECTIVE — the binding orders.

## THE next move

**The only regime no CRT argument reaches is the primes `r ≍ N`** — and that is now a THEOREM,
not a heuristic: `classDeviation_bandPairTail_le` kills every bounded band, so a counterexample
must live in the tail beyond every fixed `y`.  Probe: split `n < QR` by `P⁺(pn+1)` above/below `√N` and compute each part's class
deviation separately.  Work the degenerate family `primorialLe P ∣ p − q` (`(5,11)` at `P = 3`,
`(7,37)` at `P = 5`, `(11,431)` at `P = 7`) — there the proved model half is exactly `1`, so any
bias found is a counterexample to `PairDecorr` itself.

## Standing constraints (unchanged)

* Never delete, rename or weaken `not_pairDecouple_all`.
* Do not edit `SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other
  KICKOFFs.  New helpers in `src/NormalNumbers/PairDecouple*.lean` only.
* Never use `axiom`; named hypotheses are the sanctioned device.
* `hDepthAll` (l. 920) and `hAutoCorrAll` (l. 2201) stay as `sorry`s in `SwingC1.lean`.
* Probes in `probes/`, with a hand-computed known-answer control.  `uv run` does NOT work on this
  box (no egress to PyPI); write stdlib-only Python.
