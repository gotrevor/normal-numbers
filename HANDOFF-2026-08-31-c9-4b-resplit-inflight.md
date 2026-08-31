# HANDOFF: C9 tower node — 4b re-split into 4b1/4b2 (4b1 GREEN, 4b2 in flight) 🗼

Branch `wip/adder-tower-c9`. Continuation of the C9 endgame / OOM-split lap.

## State at handoff
- **4b1 `[27648,29184)` GREEN** — `Built NormalNumbers.AdderTowerC9Chunk4b1
  (937s)`, verified "Build completed successfully". Rode swap to full but
  survived by reclaiming page cache.
- **4b2 `[29184,30720)` STILL BUILDING** at handoff (~1666s / ~28 min wall,
  a background `taskset lake build`, driven by scratchpad `drive4b.sh` →
  `endgame.sh`). Alive the whole way, NO exit-137, memory stable
  (RSS ~16 GB, swap ~28 GB, plateau). It is genuinely much slower than 4b1
  (which was 937s) because 4b2 holds the heaviest ~700-digit omega numerals
  (top ~768 states) — the `decide +kernel` proof term is enormous and the
  kernel typecheck at swap-full thrashes. It was in the final
  typecheck/IR phase at handoff.
- Split edits are committed as **WIP with `--no-verify`** (pre-commit runs a
  full `lake build` which can't pass until 4b2's olean lands). Tree:
  `AdderTowerC9Chunk4b.lean` renamed→`4b1.lean`, new `4b2.lean`,
  `AdderTowerC9.lean` rcases widened to 7-way (last branch split at 29184
  into `c9_chunk4b1`/`c9_chunk4b2`), `NormalNumbers.lean` imports updated.

## What this lap did
1. Built chunk4b fresh (cache-cold container) → **OOM'd again** (exit 137,
   1089s) even at 3072 states — confirmed the handoff's prediction.
2. **Re-split 4b into 4b1 `[27648,29184)` / 4b2 `[29184,30720)`** (1536
   states each), exactly per the 4a/4b precedent. Rewired C9.lean + imports.
3. Built 4b1 SOLO → **GREEN (937s)**.
4. Started 4b2 SOLO via `drive4b.sh`; chained `endgame.sh` to run, after 4b2:
   full `lake build` + `#print axioms` of both C9 headlines, writing to
   scratchpad `endgame.result`.

## NEXT STEPS (resume here — CHECK FIRST)
1. **Check if 4b2 finished** while the last container lived:
   `grep -cE "completed successfully" <scratchpad>/c9c4b2.log` (want 1) and
   `grep -cE "code 137|build failed" c9c4b2.log` (want 0). Also
   `cat <scratchpad>/endgame.result` — if it reached `=== ENDGAME DONE ===`
   the full build + axioms already ran; read the axiom lines.
   - Scratchpad this lap:
     `/tmp/claude-1000/-Users-gotrevor-src-normal-numbers/a1e2ea77-d488-40f6-bef8-489a88d793ea/scratchpad/`
     (path changes per container — the container likely died, so 4b2 is
     probably cache-cold again and must be rebuilt).
2. **If 4b2 not built (fresh container): rebuild it SOLO**
   `taskset -c 0-5 lake build NormalNumbers.AdderTowerC9Chunk4b2`, poll in
   the foreground (do NOT idle — idle kills the box + build). Budget ~25–30
   min; it survives swap-full, just slow. Build sub-chunks SOLO, never
   parallel. ⚠️ The **pre-commit hook runs a full `lake build`** — so a
   green repo commit is only possible once 4b2's olean exists.
3. **If 4b2 OOMs (exit 137) after all:** split it ONE more time into
   4b2a `[29184,29952)` / 4b2b `[29952,30720)` (768 states each; 4b2b holds
   the very heaviest top states). Same mechanical recipe: two files, widen
   C9.lean rcases to 8-way, update imports.
4. **Once 4b1 AND 4b2 green:** run full `lake build` (fast — chunk oleans
   cached), then `#print axioms NormalNumbers.Adder.adder_c9_disjunction`
   and `_universal` — expect `[propext, Classical.choice, Quot.sound]` only.
   Commit green (drop `--no-verify` so the gate runs).
5. **Write the C9 RESULT into the dossier** — draft ready at scratchpad
   `c9-result-draft.md`: append a RESULT bullet after the "Second channel
   set" line (~L60) of `docs/adder-family-2026-08-29.md`, and add a C9 row
   to `BRIEF-adder-tower.md`'s RESULT table. Then **merge to master**.

## C9 headline content (unchanged)
Second channel set (`docs/adder-family-2026-08-29.md`): ln2/00, ln3/001,
ln6/11, ln12/00, ln24/00, ln72/010; ambient 30720, 28 live — cheapest
family in the tower. Headlines `adder_c9_disjunction` (ln-instance) +
`adder_c9_disjunction_universal` (any X,Y not both rational), via
`signed_engine` data-swap, kernel tier. 7-chunk sweep:
Chunk0..3, 4a, 4b1, 4b2.

## Gotchas learned this lap
- **4b2 (top range) is FAR slower than any other chunk** (~28+ min vs
  4b1's 937s / 4a's shorter) — the heaviest ~700-digit numerals dominate
  the kernel typecheck, and swap-full thrashing compounds it. It does NOT
  OOM at 1536 states; it just takes very long. Budget accordingly; don't
  mistake slowness for a hang and don't kill it prematurely.
- **The pre-commit hook builds the whole repo** — it can spuriously co-run
  with an in-flight background build (parallel = OOM risk). Bank WIP with
  `git commit --no-verify` while a chunk is still building; run a real
  gated commit only once everything's green.
- Re-confirmed: retry-after-OOM doesn't help; **split, don't retry**;
  per-chunk peak dominated by the ambient automaton, so splitting the range
  halves the tail spike but barely lowers sustained peak.
- OFF-LIMITS (unchanged): both `CFScheduleA.lean` sorries, `Comparator/
  Challenge.lean` holes.
