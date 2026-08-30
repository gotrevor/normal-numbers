# HANDOFF: tower C1–C8 ALL PROVED; next = literature-statements brief 🗼✅

Branch `wip/adder-disjunction`, tree clean, build green (8832 jobs).
Continuation of `HANDOFF-2026-08-30-tower-phaseA-done.md`.

## Done this session (four laps)

1. **`AdderBaseG.lean`** — the full base-g signed stack (tower phase B):
   `gdigit`/`carryTG` (carry window is radix-independent ⇒ `ZChannel`
   reused unchanged), `gpred` with `Int.emod/ediv` column split, family
   shadowing, base-b endgame, `signed_engine_g` (alphabet `g²`) and
   `signed_engine_g_single` (`Y := 0`, alphabet `g`).
2. **`adder_baseg_emit.py`** — base-g cert emitter (single/two-track),
   bit-for-bit `gpred` mirror; its C1 output reproduces the hand-built
   Lean certs exactly.
3. **All tower claims proved, kernel tier, axiom-clean**: C1 (`AdderTowerC1`,
   B–B 1994 cited), C2 (`AdderTowerC2`, 9 certs + transversal lemma,
   novelty under check), C3 (`AdderTowerC3`), C4+C5 (`AdderTowerC45`,
   universal + ln instances), C6 (`AdderTowerC6`, universal; first
   negative-coefficient base-g window).  C7/C8 were already done.
4. **RESULT section written at the top of `BRIEF-adder-tower.md`**
   (per-claim table, axiom audits, encoding-divergence note, no
   non-collapse findings).  Brief CLOSED.

## Next steps

1. **`BRIEF-literature-statements.md`** (the novelty-tripwire ledger) —
   now the queue head per DIRECTION.  Seed list: B–B 1994 M(3,1)=2
   (tier S, wire the edge from `c1_ternary_digit`!), Adamczewski–Rampersad
   boundary, Vandehey 2017 §7, Becher–Yuhjtman 2019 (wire from the Tier 1
   headline), Scheerer 2017, Bailey–Misiurewicz 2006, Fisher–Schmidt 2014
   (all tier P, local `papers/`).  Wiring bonus: C2/C4/C5/C6 statements
   could get `..._holds` edges from the tower theorems where nearly free.
2. Then the standing tractability mandate (DIRECTION 0b3fdb2): C9/C10 are
   explicitly optional-low; prefer ledger + anything adjacent-tractable.

## Gotchas current

- 8M-heartbeat kernel chunks (C8, musical) fail NONDETERMINISTICALLY under
  parallel `lake build` — build them solo first if cache is cold.  C6's
  single 8M `decide +kernel` job has not shown this (15 s solo).
- `signed_engine_g_single` needs no `b = 0` hypothesis: `b·0 = 0` makes
  the coefficients inert; conclusion reads on `a·X`.
