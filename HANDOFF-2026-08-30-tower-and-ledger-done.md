# HANDOFF: tower C1–C8 done, literature ledger live, k=2 floor recorded 🗼📚🧯

Branch `wip/adder-disjunction`, HEAD `905c945`, tree clean, build green
(8833 jobs).  Continuation of `HANDOFF-2026-08-30-tower-complete.md`
(same session, later laps).

## Session summary (this autonomous run)

1. **Tower brief CLOSED** — all eight claims C1–C8 kernel-tier,
   axiom-clean; RESULT table at top of `BRIEF-adder-tower.md`.  New
   infrastructure: `AdderBaseG.lean` (base-g signed stack,
   `signed_engine_g` + `signed_engine_g_single`),
   `experiments/adder_baseg_emit.py` (validated against hand-built C1
   certs).  New theorems: `c1_ternary_digit` (B–B 1994 cited),
   `c2_product_block` (+ transversal; novelty under check),
   `c3_ternary_digit_five`, `c4_disjunction(_universal)`,
   `c5_disjunction(_universal)`, `c6_disjunction_universal`.
2. **Literature ledger CLOSED (first pass)** — `Literature.lean`, 11
   statements with provenance tiers; RESULT table in
   `BRIEF-literature-statements.md`.  Three wired edges, including an
   outright PROOF of the Adamczewski–Rampersad boundary
   (`adamczewskiRampersad_boundary_holds`).
3. **Standing-mandate probe (negative, recorded)** —
   `probes/PROBE-2026-08-30-word-level-product-blocks.md`: length-2
   (k = 2) word product blocks are a method floor at small scale (all
   pairs/triples/5-sets fail; harness sanity-checked).  Instrument:
   `experiments/mahler_k2_triple_scan.py`.

## Next steps (fresh session)

1. **C9** (optional per dossier, authorized): 7 distance-1 flagship
   neighbors + second base-2 channel set, data in
   `docs/adder-family-2026-08-29.md`; existing base-2 pipeline +
   `adder_signed_emit.py`; expect 8M-heartbeat chunked kernel builds
   (sequential-build recipe below).  Low marginal value — judge against
   remaining budget.
2. **Ledger deepening**: Philipp 1967 ψ-mixing (Scheerer Thm 2.1) and
   B–M strong hot spot (Thms 3.4/3.5) need σ-algebra / sequence-space
   defs — statement-only formalization counts as progress per DIRECTION.
3. **C10** ruled out for kernel decide (~46k states × 25 alphabet ≈ 1.15M
   pred evals); would need ~100+ chunks.  Leave unless chunk-automation
   lands.
4. If a new collapse MECHANISM idea appears (beyond simple cycles), the
   k = 2 probe doc lists what it must beat.

## Gotchas (standing)

- 8M-heartbeat kernel chunk jobs fail NONDETERMINISTICALLY under parallel
  `lake build` (memory pressure): build chunks solo
  (`for i in …; do lake build NormalNumbers.<Chunk$i>; done`), then the
  full build is cache-hot.
- `signed_engine_g_single` needs no `b = 0` hypothesis (`b·0 = 0`).
- Emitter cert data is hints only; the binding check is Lean's own
  `decide` against `gfamPred` — a convention mismatch fails closed.
