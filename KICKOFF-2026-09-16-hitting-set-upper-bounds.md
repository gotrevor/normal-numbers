# KICKOFF 2026-09-16 — hitting-set upper halves as theorems: U5 `(6,1) ≤ 7`, U6 `(3,2) ≤ 6`, U7 `(2,4) ≤ 9` 🧵

*Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine Opus/low.  Branch
`wip/adder-tower-c9`.  Hard stop: the host kills laps at 05:25 EDT - commit a compiling skeleton with
named `sorry` leaves before each certificate.  Scope: THIS kickoff only; `DIRECTION.md`'s run+jump
directive is a different campaign and is not touched.  Finish with `box done --green`.*

Context: `docs/hitting-set-invariant-2026-09-13.md` §Data - three rows have an exact value found by
the automaton search but no theorem.  `KICKOFF-2026-09-13-hitting-set-bounds.md` (U1–U4, landed in
`HittingSetBounds.lean`) and `KICKOFF-2026-09-13-hitting-7-1.md` (landed in `HittingSetBase7.lean`,
chunked kernel decide, `HANDOFF-2026-09-14-0300.md` has the memory lessons) are the templates.

## Objective - three theorems, in this order (each its own file, each committed as soon as green)

```lean
/-- `S(6,1) ≤ 7`: `{1, 8, 11, 14, 16, 20, 23}` hits every base-6 digit (search 2026-09-13). -/
theorem hitting_6_1_seven : Literature.IsHittingSet 6 1 {1, 8, 11, 14, 16, 20, 23}
/-- `S(3,2) ≤ 6`: `{1, 2, 4, 5, 7, 8}` hits every base-3 word of length 2. -/
theorem hitting_3_2_six : Literature.IsHittingSet 3 2 {1, 2, 4, 5, 7, 8}
/-- `S(2,4) ≤ 9`: the first nine odd numbers hit every binary word of length 4. -/
theorem hitting_2_4_nine : Literature.IsHittingSet 2 4 {1, 3, 5, 7, 9, 11, 13, 15, 17}
```

Files: `src/NormalNumbers/HittingSetBase6.lean`, `HittingSetBase3Len2.lean`, `HittingSetBase2Len4.lean`,
each imported from `src/NormalNumbers.lean`.

## Route

1. **Certificates.**  Add FAMILIES entries `h61`, `h32`, `h24` to `experiments/adder_baseg_emit.py`
   (mirror `h71` / `h23`) and emit `experiments/certs/adder_cert_h61_d{0..5}.json`,
   `adder_cert_h32_w{00..22}.json`, `adder_cert_h24_w{0000..1111}.json`; verify each with the
   emitter's Python checker before touching Lean.  Commit the JSONs.
2. **Lean.**  Generate the `checkEdgesOnA` / `checkForcedA` / `checkCertA` blocks the way
   `HittingSetBase7.lean` does (sparse `List.lookup` tables), glued by
   `HittingSetBounds.checkEdgesOnA_of_chunks` / `checkCertA_of_edgesOn`.  **Kernel `decide +kernel`
   in chunks of ≤ 1600 ambient states, ONE kernel probe at a time** (the 2026-09-14 lesson: two
   concurrent probes swap the box to death; seven whole-certificate probes in one file hit
   `avail < 1 GB`).  ⚠️ Another box is building on the host tonight - keep peak RSS ≤ 9 GB.
   **`native_decide` is allowed** where the ambient count makes kernel chunks impractical
   (expected for `(2,4)`: 16 words); this repo is at the formalize tier, so say so in the docstring
   and move on - do not spend a lap optimizing a certificate that `native_decide` closes in seconds.
3. `#print axioms` on each headline in the handoff (trust triple, or trust triple + the named
   `native_decide` certificates).
4. If a search set turns out NOT to certify (the emitter's checker fails), record it in
   `docs/hitting-set-invariant-2026-09-13.md` §Data as a withdrawn row and move to the next theorem;
   do not search for a replacement set.

## Not in scope
Lower bounds (N2, N4′), the run+jump chain, any Mahler work, `PENDING_WORK.md` archaeology.
