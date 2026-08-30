# BRIEF follow-on 3: the tower claims (C1–C8) 🗼

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
