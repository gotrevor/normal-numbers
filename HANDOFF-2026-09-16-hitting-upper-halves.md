# HANDOFF 2026-09-16 — the three upper halves are theorems, via the carry-consistency reduction 🧵

*Lap: overnight Opus run on `KICKOFF-2026-09-16-hitting-set-upper-bounds.md` (U5/U6/U7).
Branch `wip/adder-tower-c9`.  HEAD at handoff: see `git log -1`.*

## Done — all three kickoff targets

| theorem | file | set | ambient | reduced | `#print axioms` |
|---|---|---|---|---|---|
| `hitting_6_1_seven` | `HittingSetBase6.lean` | `{1,8,11,14,16,20,23}` | 9 067 520 | **76** | **trust triple only** |
| `hitting_3_2_six` | `HittingSetBase3Len2.lean` | `{1,2,4,5,7,8}` | 1 632 960 | **54** | **trust triple only** |
| `hitting_2_4_nine` | `HittingSetBase2Len4.lean` | `{1,3,…,17}` | 4 625 065 731 686 400 | **520** | **trust triple only** |

## The lap's real content: `src/NormalNumbers/HittingSetReduced.lean`

The kickoff's route (mirror `HittingSetBase7.lean`, chunked kernel decide over the
ambient) is **infeasible** for all three: the ambient is the product `∏ᵢ mᵢ·g^(ℓ−1)`.
U6 was first landed the brute way (nine `native_decide`s over 1 632 960 states with
sorted-array tables, 14-minute module — commit `c9c7a3d`), which showed the wall.

The reduction removes the product.  All channels read the same `X`, so with
`u = X·gᵐ`, `F = ⌊u⌋`, `t = fract u`:

* `carryTG g a 0 X 0 m = ⌊a·t⌋`  (`carryTG_single`);
* `gdigit g (a·X) (m+j) = ⌊a·g^(j+1)·t⌋ − g·⌊a·g^j·t⌋`  (`gdigit_window`) — the
  `F` terms cancel, because `a·g^(j+1) = g·(a·g^j)`.  **The window needs no extra
  parameter**; the first draft of the reduction wrongly carried a `r = F mod g`
  (an off-by-one in the digit index) and the Python cross-check caught it.

So the joint state is a one-parameter curve, and with `N = lcm{a·g^j : j ≤ ℓ−1}`
it is `stateOfKW g N ℓ ms ⌊N·t⌋` (`gfamState_window`, proved for all `ℓ`).
`signed_engine_g_single_reduced` is `signed_engine_g_single` on the relabelled
state space `[0,S')`, its only extra hypothesis being that the index map is a
section over the reachable states — one sweep over `k < N`.

Emitters: `experiments/adder_reduced_emit.py` (ℓ = 1) and
`experiments/adder_reduced_emit_ell.py` (any ℓ).  The latter carries a
**state/`gfamPred` intertwining self-test** (`pred(⌊g t⌋, state(fract(g t))) = state(t)`
on every breakpoint sample), which is what validates the Lean state formula
against the automaton before any Lean is written.  Reachable sets are enumerated
exactly, by walking the breakpoints of `t` with `Fraction`s.

## Next moves, in order

1. **DONE — all three are axiom-clean** (`[propext, Classical.choice, Quot.sound]`),
   no `native_decide` anywhere in the chapter.  `(6,1)` uses `allOn_of_chunks`
   (fourteen kernel chunks of `10 120`); `(2,4)`'s `6 126 120`-index sweep uses
   **run compression** — `stateOfKW` reads `k` only through the monotone quotients
   `(b·k)/N`, so it is constant on each of the `520` runs between breakpoints
   (`stateOfKW_congr`, `quot_const_of_run`, `runsCover_spec`), and the whole sweep
   is `520` kernel checks.  Module build times: `(3,2)` 19 s, `(2,4)` ~16 min,
   `(6,1)` ~17 min.
2. **The lower halves** `S(6,1) ≥ 7`, `S(3,2) ≥ 6`, `S(2,4) ≥ 9` are untouched and
   are the real remaining content of the invariant (only searches, no theorems).
   `N5` (`S(2,k) = 2^(k−1)`) is refuted at `k = 4` but `8` is not excluded.
3. **The reduction is reusable**: any single-track family is now cheap, so the
   `(7,1)` file could be re-proved on ~30 states, and larger `k` at base 2 becomes
   reachable for the first time.

## Not touched
`DIRECTION.md`'s run+jump / Mahler campaign (a different chapter — this kickoff
outranked it for this run only).
