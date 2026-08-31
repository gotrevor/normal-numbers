# HANDOFF: C9 tower node — recovery + chunk4 split (4b in flight) 🗼

Branch `wip/adder-tower-c9`, HEAD `2a9b6a5`.  Build NOT yet green
(chunk4b still compiling at handoff).  Continuation of the dead-container
recovery lap.

## State at handoff
- HEAD `2a9b6a5` "WIP: split C9 chunk4 into 4a/4b to fix OOM".
- Working tree clean (all split edits committed).
- **`AdderTowerC9Chunk4b` decide+kernel STILL RUNNING** as a background
  `lake build` (log: scratchpad `c9c4b.log`).  At handoff ~35 min wall,
  CPU ~32 min at ~99%, RSS ~10–12 GB, healthy — a genuinely long decide
  (the highest omega numerals are ~700 digits; GMP mul is superlinear).
  It had survived swap-full (32/32) spikes with av≥1 the whole way.

## What this lap did
1. **Banked** the dead-container C9 tree onto `wip/adder-tower-c9`
   (commit `0afc8a4`): AdderTowerC9{,KData,Chunk0..4}.lean,
   experiments/emit_cert_lean.py, adder_cert_secondset.json, +7 imports
   in NormalNumbers.lean, adder_signed_emit.py.
2. **Sequential chunk builds** (solo, `taskset -c 0-5`, 8M heartbeat):
   Chunk0 [0,6144) GREEN, Chunk1 GREEN, Chunk2 GREEN, Chunk3 [18432,24576)
   GREEN.  Chunk3 took ~7 min CPU; peaks ~24 GB.
3. **Chunk4 [24576,30720) OOM-KILLED (exit 137)** at its tail on BOTH the
   first run and a fresh retry: it survived the early ~24 GB peak, ran ~27
   min at ~11 GB, then a final proof-term spike exceeded RAM+swap.  The
   retry filled swap during the sustained phase just like the first run, so
   the fresh-swap advantage did not save it → refuted that approach.
4. **Fix: split chunk4 into 4a/4b** (commit `2a9b6a5`), 3072 states each.
   - `AdderTowerC9Chunk4a` [24576,27648): **GREEN** (verified, "Build
     completed successfully").  Rode swap up to ~28/32 but survived.
   - `AdderTowerC9Chunk4b` [27648,30720): building at handoff.
   - C9.lean `c9_edges_ok`: last rcases branch split at 27648 into two
     branches using `c9_chunk4a`/`c9_chunk4b`.  NormalNumbers.lean imports
     updated.  Old `AdderTowerC9Chunk4.lean` deleted.

## NEXT STEPS (resume here)
1. **Check chunk4b**: `grep -E "completed successfully|error|137"
   .../scratchpad/c9c4b.log` (or re-run `lake build
   NormalNumbers.AdderTowerC9Chunk4b`; if the container died it's cache-cold
   again).  Build sub-chunks SOLO (memory), never in parallel.
2. **If 4b OOMs too** (unlikely — it survived the tail region at handoff):
   split it once more into 4b1 [27648,29184)/4b2 [29184,30720) (1536 states
   each) exactly like 4a/4b; update C9.lean rcases + imports.  The recipe is
   mechanical; the numeral-heavy states are all in the top ~768 states.
3. **Once 4a AND 4b green**: run full `lake build`, then `#print axioms
   NormalNumbers.Adder.adder_c9_disjunction` (+ `_universal`) — expect
   `[propext, Classical.choice, Quot.sound]` only (kernel decide is
   axiom-clean; signed_engine is the wiring).  Fix anything, commit green.
4. **Merge to master** if green + axiom-clean.  Then C9 tower node done.

## C9 headline content
Second channel set (docs/adder-family-2026-08-29.md): ln2,ln3,ln6,ln12,
ln24,ln72; words 00,001,11,00,00,010; ambient 30720, 28 live — cheapest
family in the tower.  Headlines: `adder_c9_disjunction` (ln-instance),
`adder_c9_disjunction_universal` (any X,Y not both rational), via
`signed_engine` data-swap, kernel tier.

## Gotchas learned this lap
- **These C9 kernel-chunk decides are LONG** (7–35 min each) and
  memory-peaky (~24 GB), NOT the ~11 s the frozen-table reference suggests —
  the ~700-digit omega numerals dominate.  Budget accordingly.
- **Per-chunk peak is dominated by the AMBIENT automaton** (all 30720
  states' tables), so splitting the state RANGE barely lowers the sustained
  peak — BUT it halves the TAIL proof-term spike, which is what OOM'd.  That
  is why 3072-state sub-chunks fit where 6144 did not.
- Retry-after-OOM with "fresh swap" does NOT help: the sustained working set
  refills swap before the tail.  Split, don't retry.
- OFF-LIMITS (unchanged): both CFScheduleA.lean sorries, Comparator/
  Challenge.lean holes.
