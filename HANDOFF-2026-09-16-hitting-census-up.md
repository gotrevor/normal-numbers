# HANDOFF 2026-09-16 — the census goes up, and the upper halves are now EMITTED 🧵📈

*Lap: overnight Opus run on `KICKOFF-2026-09-16-hitting-set-census-up.md` (the
02:50 EDT attended override).  Branch `wip/adder-tower-c9`.*

## Done

| # | kickoff item | state |
|---|---|---|
| 1 | port the reduction to the search instrument | **done**, `97cec2d` |
| 2 | new rows `S(2,5)`, `S(3,3)`, `S(8,1)` | **done**, `e1df04e` |
| 3 | upper halves as theorems | `S(8,1) ≤ 11` **done** (`d041ae0`); `(2,5)` and `(3,3)` emitted and Python-verified, NOT yet kernel-checked |
| 4 | re-prove `(7,1)` on the reduction | **done**, `fbf099f` — 8 s instead of 24 min |

### 1. `experiments/hitting_set_search_reduced.py`

The hitting test on the carry-consistent states instead of the ambient product.
The carry vector into the current digit position is `(⌊m·t⌋)ₘ` for the unread
tail `t`, so a **forward BFS from the zero carry is exactly the reachable
space**: `t ↦ (d+t)/g` generates the `g`-adic rationals, dense in every interval
between the breakpoints `p/m`, so BFS reachability *is* realizability, with no
analytic argument.  Restricting to reachable states is sound for the hitting
question — an escaping `α` is an infinite path read upward from the deep
positions and never leaves that set.

`--selftest` is three layers of control and all three pass: (a) block-by-block
agreement with the ambient automaton on twelve families including `(6,1)`,
`(3,2)`, `(2,3)`; (b) every published row reproduced exactly; (c) minimality —
every proper subset of each published minimal set fails.

### 2. New rows (`docs/hitting-set-invariant-2026-09-13.md`)

* `S(8,1) ≤ 11`, `{2,4,7,11,13,14,17,20,22,28,38}` — **theorem**
  `hitting_8_1_eleven`, axiom-clean, 128 reduced states of 892 268 016 640
  ambient, 25 s build.
* `S(2,5) ≤ 20`, `{1,3,…,37,41}`.  The odd prefix `{1,3,…,2n−1}` first hits at
  **`n = 21`**, not `16`: the refuted `S(2,k) = 2^(k−1)` shape fails in the
  OTHER direction at `k = 5`.
* `S(3,3) ≤ 28` (pool `3∤m ≤ 60`).  The kickoff's cap `≤ 40` is **too small** —
  the entire pool below 40 fails at `000`.
* Refuted en route: "`0^k` is the last block standing, so hitting `0^k` is the
  whole invariant".  `{5,7}` at base 3 hits digits `0` and `2` and **misses `1`**;
  45 of 57 random hitting-`0` 5-sets at base 5 miss some other digit.  `0^k` is
  the hardest block generically, not universally.

### 3. `experiments/emit_hitting_lean.py` — the real lever

Emits a whole upper-half module from `(g, ell, ms)`: state list, run endpoints,
the run-compressed reachability sweep, one verified `checkCertA` per word, and
the `IsHittingSet` assembly (any word length).  It **refuses to emit** unless
every certificate's C1/C1'/C3' conditions check in Python first.  What
`HittingSetBase2Len4` / `Base6` carried by hand is now one command.

`--split DIR MODULEBASE N` writes `…Core` + `N` cert modules + the assembly:
the monolithic `(2,5)` file (5328 states × 32 words, 1.4 MB) is **OOM-killed**
on this 19 GB box (`Lean exited with code 137`), and worse, two concurrent
`lean` processes on it guarantee the kill — run ONE build at a time here.

## Where `(2,5)` actually stands — read this before restarting it

`S(2,5) ≤ 20` is **emitted and Python-verified** (all 32 certificates pass
C1/C1'/C3'), but it is **not a theorem yet**: the kernel has not seen it.  What
was measured this lap, on the 19 GB box:

* the `(2,5)` reduction is `5328` states and `5328` runs — 10× `(2,4)`'s `520`,
  with state labels of 47 digits instead of 16;
* as ONE module it is OOM-killed (`Lean exited with code 137`);
* split into `…Core` (defs + the 29 run-sweep chunks of 200 + `_section`) plus
  16 certificate modules, the Core module ran **70 minutes without finishing**,
  peak RSS cycling between 4 and 14 GB.  It was killed to protect the lap, not
  because it errored.  The certificate modules were never reached.

So the run sweep must be **split across `lean` processes**, not just across
declarations — memory is released between chunks but the wall-clock is not.
`emit_hitting_lean.py --split` now does exactly that: it writes `…Base` (defs +
a LOCAL `runsCover_append` lemma, so no rebuild of the rest of the chapter),
`…Runs{i}` (a couple of `decide +kernel` chunks each), `…Core` (the append
chain + `_section`), `…Cert{i}`, and the assembly.  That layout is emitted and
untested; testing it is move 1 below.  Build the modules ONE AT A TIME
(`lake build -j1`); two concurrent `lean` processes on a module this size is an
instant OOM.

Reproduce (seconds each):

```
RUNCHUNK=200 python3 experiments/emit_hitting_lean.py h25 2 5 \
  1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,41 hitting_2_5_twenty \
  --split src/NormalNumbers HittingSetBase2Len5 16
RUNCHUNK=200 python3 experiments/emit_hitting_lean.py h33 3 3 \
  1,5,7,8,10,11,13,16,17,19,23,25,26,28,29,31,35,37,41,43,47,49,50,52,53,56 \
  hitting_3_3_twentysix --split src/NormalNumbers HittingSetBase3Len3 27
```

## Next moves

1. **`(2,5)` on the per-process split** — build `…Base`, then each `…Runs{i}`,
   then `…Core`, then the certs, `-j1`, one at a time.  If a single `Runs`
   module is still minutes-long, lower `RUNCHUNK` and raise the group count:
   the knob is now free.
2. `S(3,3) ≤ 26` (the hunt improved 28 → 26 during the lap) is 5094 states × 27
   words — the same shape, one more word length.  Shrink the set further first;
   every set here is greedy-minimal-BY-INCLUSION, not minimum.
3. The **lower halves** are still the real content of the invariant: every `≥`
   in the table is a search cap, not a theorem, and no finite automaton decides
   them.

## Not touched
`DIRECTION.md`'s run+jump / Mahler campaign (a different chapter; this kickoff
outranks it for this run only).
