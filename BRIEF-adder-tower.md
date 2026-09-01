# BRIEF follow-on 3: the tower claims (C1–C8) 🗼

## RESULT (2026-08-30, autonomous session; brief CLOSED) ✅

**All eight claims proved, kernel tier, no non-collapse findings.**  Every
theorem below audits exactly `[propext, Classical.choice, Quot.sound]`
(real `#print axioms` output, session scratchpad `axall.lean`).  Engine
infrastructure landed on the way: `AdderEngineCoreG` (alphabet-generalized
descent), `AdderBaseG` (base-g signed stack: `gdigit`/`carryTG`/`gpred`
on the reused radix-independent `ZChannel`, base-b endgame,
`signed_engine_g` over `σ = x + g·y < g²`, and the single-track
`signed_engine_g_single` with `Y := 0`, alphabet `g`).

### C10 ADDENDUM (2026-09-01, autonomous run) ✅ — REDUCTION FINDING

**C10 proved, kernel tier, axiom-clean — and it is NOT a large-certificate
theorem.**  `c10_disjunction_universal` (`AdderTowerC10.lean`; the dossier's
exact nine-disjunct shape: 3 in Y · 4 in 2Y · 2 in 3Y · 0 in 4Y · 2 in X+Y ·
3 in X+4Y · 2 in 2X+2Y · 2 in 3X+3Y · 2 in 4X+4Y, base 5) audits exactly
`[propext, Classical.choice, Quot.sound]` (real `#print axioms`); the two
certificates `c10y_cert`/`c10z_cert` audit `[propext]`.

- **Audit disposition (same pattern as C5): the family SPLITS.**  If `Y` is
  irrational, the four `Y`-only channels `(0,1)/3 · (0,2)/4 · (0,3)/2 ·
  (0,4)/0` collapse alone as a single-track family (24 ambient, 5 live,
  `c10_y_branch`).  Otherwise `Y = q ∈ ℚ`, `X` irrational, `Z := X+q`
  irrational, and the diagonal channels `(1,1)/2 · (2,2)/2 · (3,3)/2 ·
  (4,4)/2` are `Z, 2Z, 3Z, 4Z` all avoiding digit 2 — a single-track family
  that also collapses (24 ambient, 6 live, `c10_z_branch`).  The mixed
  channel `(1,4)/3` (`X+4Y`) is **unused**.  So the dossier's 540 396-state
  certificate certifies a statement two 24-state single-track `M(5,1)`-type
  claims already imply; do NOT present C10 as an independent nine-channel
  discovery.  (Its `docs/tower-novelty-audit-2026-08-29.md` "credible new
  candidate" rating should be downgraded to the C5 disposition.)
- **Collapse verdict agrees** with the dossier: the full two-track automaton
  in our encoding (46080 ambient, 18 live, four 2-cycles,
  `adder_baseg_emit.py c10`, 1.2 s) also collapses; kernel proof went via
  the reduction instead.  Emitter entries `c10`, `c10y`, `c10z` added.
- The two single-track sub-claims are themselves base-5 analogues of
  B–B's `M(3,1)=2` (multipliers `{1,2,3,4}`); novelty of those against
  Berend–Boshernitzan 1994's general-`g` results is UNCHECKED (paper not
  held) — lane-2 treatment until the operator's sweep says otherwise.

### C9 ADDENDUM (2026-08-31, overnight autonomous run) ✅

**C9 proved, kernel tier, axiom-clean.**  `adder_c9_disjunction` (ln
2/3/6/12/24/72 — clauses `00`/`001`/`11`/`00`/`00`/`010`) and its universal
form `adder_c9_disjunction_universal` both audit exactly `[propext,
Classical.choice, Quot.sound]` (real `#print axioms`, no `sorryAx`), as does
the certificate `c9_cert_ok`.  Module `AdderTowerC9` over `AdderTowerC9KData`.

- **30720 ambient states** — largest tower node so far.  The `checkEdgesP`
  witness could not be kernel-reduced in one `decide +kernel` (OOM), so the
  edge check is split into 7 contiguous chunks over `[0,30720)`:
  Chunk0..3 (6144 each), 4a `[24576,27648)`, 4b1 `[27648,29184)`,
  4b2 `[29184,30720)`; each `c9_chunkN` is a `checkEdgesOnP` cert, reassembled
  in `c9_edges_ok` by a 7-way `rcases`/omega interval split.
- **4b2 is the heavy tail** (~2053s solo build; holds the ~700-digit omega
  numerals for the top range) — required two rounds of splitting to fit under
  the container memory ceiling (4→4a/4b, then 4b→4b1/4b2).
- `c9_forced_ok` is a single `decide +kernel` at 8M heartbeats.
- Full `lake build` green (8842 jobs); merged to master at `aaa58ac`.

| claim | theorem(s) | module | states (ours) | tier |
|---|---|---|---|---|
| C1 | `c1_ternary_digit` | `AdderTowerC1` | 2 ambient, 2 live ×3 certs | kernel `decide` — **B–B 1994 M(3,1)=2, lane-2 CITED, not new** |
| C2 | `c2_product_block` (+ `c2_clause`, transversal inline) | `AdderTowerC2` | 22 ambient, 5–10 live ×9 certs | kernel `decide`; **novelty under check** (operator sweep pending) |
| C3 | `c3_ternary_digit_five` | `AdderTowerC3` | 5 ambient, 2–4 live ×3 certs | kernel `decide` — lane-2, B–B orbit |
| C4 | `c4_disjunction_universal` / `c4_disjunction` (ln 3/27/24/6) | `AdderTowerC45` | 24 ambient, 6 live | kernel `decide` |
| C5 | `c5_disjunction_universal` / `c5_disjunction` (ln 3/9/162/4/16) | `AdderTowerC45` | 80 ambient, 6 live | kernel `decide`; y = x instance subsumed by C1 (noted, not restated) |
| C6 | `c6_disjunction_universal` (no named instances in dossier) | `AdderTowerC6` | 480 ambient, 19 live | kernel `decide +kernel`, 8M heartbeats; first signed base-g carry window (channel `(2,−1)`) |
| C7 | `adder_musical_disjunction(_universal)` | `AdderMusical` | 15360 ambient, 15 live | kernel — proved BEFORE this brief landed; RESULT recorded in `BRIEF-adder-signed-engine.md` |
| C8 | `adder_c8_disjunction(_universal)` | `AdderTowerC8*` | 75 live, 8 cycles | kernel, 8-chunk split — phase A, certified independently (not via complement involution) |

- **Live-state counts differ from the dossier's figures throughout**
  (e.g. C1: ours 2 vs dossier 6; C4: 6 vs 72; C6: 19 vs 676) — expected
  encoding divergence per this brief's coordination note.  **Collapse
  VERDICTS agree on all certified instances** (two-instrument agreement:
  `experiments/adder_baseg_emit.py` ↔ the dossier's
  `mahler_minimal_sets.py`/`base3_*`/`base_g_digit_hunt.py`, and the
  emitter's C1 output reproduces the hand-built Lean certificates
  field-for-field).
- §1.4 transpose note: resolved in `AdderEngineCoreG`'s docstring — the
  whole Lean pipeline is the backward-deterministic deep→shallow `fstep`
  orientation, so certified graph = shadowed walk by construction.
- Python mirror: `adder_baseg_emit.py` (single- and two-track, any g),
  refusing on C1/C1'/C3' failure, cross-checked against the Lean kernel on
  every claim (the binding check is the Lean `decide` itself).  The
  brief's mpmath digit-anchor selftest extension was NOT done (no new
  named-constant carry conventions were introduced beyond what the kernel
  re-derives; flag if C-instance anchors are wanted).
- Out of scope untouched (as of 2026-08-30): C9, C10, floors/negatives, novelty sweep.  C9 landed 2026-08-31, C10 landed 2026-09-01 (addenda above); floors/negatives and the novelty sweep remain operator-owned.

**Operator-authorized 2026-08-29 (Trevor, attended session).**  Execute AFTER
`BRIEF-adder-signed-engine.md`.  The complete evidence package is
`EVIDENCE-2026-08-29-tower-formalization.md` (committed here) — read it in full
before starting; this brief is routing, the dossier is substance.

## Coordination (from the operator, verbatim intent)

The dossier is **additive cargo** — it does not touch the frozen
`BRIEF-adder-disjunction-formalization.md` statements or any RESULT already
recorded.  🚨 **If any of your automata fails to collapse, that is a FINDING to
report back, not something to patch quietly.**  Record the divergence in this
file's RESULT section (claim id, your encoding, what failed), leave that claim
unproved, and move on.  Divergence in live-state COUNTS from the dossier's
figures is expected and fine; divergence in a collapse VERDICT is the finding.

## Independence rule

Your Lean automaton definition must come from the dossier's §1.2–1.3 rules (a
function `decide` computes), NOT from importing the provided transition tables.
`experiments/certs/tower-2026-08-29.json` (20 per-channel tables, format in
`emit_tower_certs.py`'s docstring) is expected-output TEST DATA for
cross-checking and debugging only — then the kernel check remains an independent
derivation and a collapse becomes two-instrument agreement.

⚠️ Before anything else, settle the dossier's §1.4 transpose note against our
pipeline: our `HStep`/`famPred` is already the deep→shallow backward-deterministic
form, so confirm which graph direction your certificate conditions sweep and note
the transpose-invariance argument explicitly in the Lean docstring.  This is the
likeliest silent-mismatch point.

## Phases (engineering-cost order, not the dossier's)

The dossier's priority list assumes the base-g engine already exists; ours
doesn't yet, so:

### Phase A — C8 data-swap (no refactor) 🥇
**C8 complemented flagship** is base 2 with nonnegative coefficients
`(1,0)/11 · (0,1)/110 · (1,1)/00 · (1,2)/110 · (2,1)/101 · (1,3)/111` — a pure
data swap on the EXISTING engine, same shape as the main family.  Certify
directly (the dossier recommends this over the complement-involution derivation,
for independence).  Universal form + ln-instance corollary.  `decide +kernel`
if it fits, `native_decide` disclosed otherwise (two-lanes).

### Phase B — base-g engine generalization
Generalize digits/carries/automaton to base g ≥ 2 per §1.2: recursion
`a·x_n + b·y_n + T(n) = g·T(n−1) + z_n`, joint input alphabet `{0..g−1}²`,
word-tracking via factor-automaton states (single digits: trivial — state dies
iff the emitted digit equals the avoided one; multi-digit words only reappear in
base 2, already handled).  Carry window per §1.2 general (signed) range —
build on `AdderSigned`'s offset encoding.

**Single-track claims come free**: a channel `m·x` is `(m, 0)` with `Y := 0`;
then "not both rational" reduces to `Irrational X`.  State the single-track
corollaries in the dossier's exact form ("for every irrational x …, base g
explicit") — don't invent a parallel one-real engine.

### Phase C — claims, dossier order
1. **C1** ternary {1,2}, three certificates (~6 states each).  ⚠️ **KNOWN RESULT
   (reclassified 2026-08-29, master `c645528`): C1 is Berend–Boshernitzan 1994's
   own M(3,1) = 2.**  Formalize it as a lane-2 *cited* result — docstring
   "Berend–Boshernitzan 1994, M(3,1)=2", never headlined as new — and spend the
   minimum: certificates only, SKIP the hand-proof lemma (it presumably
   re-derives theirs).  C3 and the {1,5} landscape are at most a variant delta
   over the same paper — same lane-2 treatment.  The {2,11} product block (C2)
   is a different statement SHAPE with novelty UNKNOWN pending the subsumption
   check — keep its priority but say "novelty under check" in its docstring.
2. **C2** ternary product block {2,11}: NINE certificates (≤36 states) + the
   **transversal lemma** exactly as stated in the dossier (finite contrapositive,
   no compactness).
3. **C3** {1,5} variants (~12 states).
4. **C4** base-3 four-channel single-digit family (72 live, fixed points).
5. **C5** escape from Cantor (261 live).  Formalize the two-real form; the
   y = x instance is subsumed by C1 — note that in the docstring, no extra
   theorem.
6. **C6** base-4 positioned-binary family (676 live).

## Python mirror discipline

Extend `experiments/adder_certificate_emit.py` (or a sibling) to base-g and
single-track with the SAME encoding bit-for-bit as the Lean definition; emitter
re-verifies C1/C1'/C3' and refuses on failure, as now.  Extend
`adder_cert_selftest.py` with mpmath anchors against the true base-3/base-4
digits of the named instance constants, including at least one exercised-carry
anchor per new base.  The dossier's own scripts (`mahler_minimal_sets.py` etc.,
copied here) are the OTHER instrument — use for cross-checks, don't fork them.

## Statement conventions

As in the prior briefs: i.o. spelled `∀ N, ∃ n, N ≤ n ∧ …`; hypothesis welded
inside each statement (`¬(∃ p : ℚ, (p:ℝ) = X) ∧ …` two-track / `Irrational x`
single-track); base explicit; named constants as instance corollaries only.
RESULT section at the top of this file when done (or when budget walls):
per-claim status, real `#print axioms` output, evidence tier named per claim,
any non-collapse findings.

## Out of scope ⛔

C9 (distance-1 neighbors), floors and negative search outcomes (§2 "NOT for
formalization" — method-relative, not theorems), the novelty sweep
(operator-owned), any outward artifact.
