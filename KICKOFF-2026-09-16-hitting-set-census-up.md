# KICKOFF 2026-09-16 (02:50 EDT) — push the `S(g,k)` census UP with the carry-consistency reduction 🧵📈

*Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine Opus/low.  Branch
`wip/adder-tower-c9`.  Hard stop: the host kills laps at 05:25 EDT (≈ 2.5 h from launch) - land
things in this order and commit each as it goes green.  Scope: THIS kickoff only.  `box done --green`
when the list is exhausted or the clock is close.*

Context: `HANDOFF-2026-09-16-*` (the upper-halves lap): the reduction in `HittingSetReduced.lean`
shrinks single-track automata to tens-to-hundreds of states (`(2,4)`: `4.6·10¹⁵ → 520` runs), so
"larger `k` at base 2 becomes reachable for the first time".  `docs/hitting-set-invariant-2026-09-13.md`
§Data has `(8,1),(9,1),(10,1) > 8/8/9` and `(2,k)` only to `k = 4`, all search-capped.

## Objectives, in order

1. **Port the reduction to the search instrument.**  `experiments/hitting_set_search.py` runs the
   product automaton; write `experiments/hitting_set_search_reduced.py` that enumerates the
   reduced state space (the same `stateOfK` / run-compression idea as the Lean file, in Python
   with exact integers), verify it reproduces the known rows `(2,4) = 9` (`{1,3,…,17}`),
   `(3,2) = 6`, `(6,1) = 7`, `(7,1) = 7`, `(5,1) = 5` **exactly** (same minimal sets) before
   trusting it on anything new.  Commit with a `--selftest` flag that runs those controls.
2. **New rows**: `S(2,5)` (candidates: odd numbers first, cap ≤ 80), `S(3,3)` (cap ≤ 40),
   `S(8,1)` (cap ≤ 40).  Record every result in `docs/hitting-set-invariant-2026-09-13.md` §Data
   with the cap, exactly in the existing row format; a ">" is a search cap, never a theorem.
3. **Upper halves as theorems** for whatever item 2 finds, on the reduction, in the pattern of
   `HittingSetBase2Len4.lean` (run compression, kernel chunks ≤ ~10 000 checks each, one kernel
   probe at a time, peak RSS ≤ 9 GB - another box may be building).  Files
   `HittingSetBase2Len5.lean`, `HittingSetBase3Len3.lean`, `HittingSetBase8.lean`; trust triple
   preferred, `native_decide` acceptable (formalize tier) if a certificate resists chunking - say so.
4. Only if time remains: re-prove `(7,1)` on the reduction (~30 states) so the chapter's build time
   drops from 24 min; keep the old theorem name, delete nothing.

## Not in scope
Lower bounds (searches are data, not theorems), N5, the run+jump / Mahler campaign, PENDING_WORK
archaeology.  If item 1's self-test disagrees with a known row, STOP item 2, record the discrepancy
in the doc and the handoff, and fall back to item 4.
