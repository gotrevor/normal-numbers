# BRIEF follow-on 4: the literature statement layer 📚🪞

## RESULT (2026-08-30, autonomous session; first pass landed) ✅

`src/NormalNumbers/Literature.lean` is live, builds green, and future
briefs are pointed at it (module docstring).  Statements landed:

| statement | tier | status |
|---|---|---|
| `mahler_theoremM` (Mahler 1973, m ≤ g^(2k+1)) | S (`docs/disjunctive-vs-normal.md` §1.1 via Waldschmidt) | unproved def |
| `berendBoshernitzan_bound` (m ≤ 2g^(k+1)) | S (same + `docs/adder-family-2026-08-29.md`) | unproved def |
| `berendBoshernitzan_M31` (M(3,1)=2 upper half) | S (`docs/mahler-sets-…` via master `c645528`) | **WIRED**: `…_holds` from tower C1 `c1_ternary_digit` ✅ |
| `adamczewskiRampersad_boundary` (0/1/01/10 i.o. in every irrational) | S (`docs/disjunctive-vs-normal.md`, PAMS 136) | **WIRED**: `…_holds` proved here (forbidden-switch → eventual constancy → endgame) ✅ |
| `waldschmidt_conjecture_1_1` (digit occurrence for algebraics; OPEN) | S (arXiv:0908.4034 §1 quoted) | unproved def (conjecture) |
| `furstenberg_dense_orbit` (×2×3 dense orbits) | S (`docs/disjunctive-vs-normal.md` §1.2) | unproved def |
| `becherYuhjtman_existence` (Thm 1 minus efficiency) | P (`papers/becher-yuhjtman-…`) | **WIRED**: `…_holds` := `exists_absolutely_normal_cf_normal` ✅ |
| `baileyMisiurewicz_weak_hot_spot` (Thm 1.1 full iff, limsup form) | P (`papers/bailey-misiurewicz-…`, complete AMS text) | unproved def (repo holds the b-adic corollary of one direction) |
| `vandehey_matrix_action` (Thm 1.1, det ≠ 0) | P (`papers/vandehey-2017-…`) | unproved def |
| `vandehey_quadratic_problem` (§7 OP 1; OPEN) + `IsQuadraticIrrational` | P (same) | unproved def |
| `mendesFrance_simple_normality_problem` (§7 OP 2; OPEN) | P (same) | unproved def |

All three `…_holds` edges audit `[propext, Classical.choice, Quot.sound]`.

**Gaps (never-fabricate rule):** B–B's `g^k − 1` lower bound (quantifier
structure not pinned by our secondary sources); Scheerer 2017 Thm 2.1
(Philipp ψ-mixing — needs σ-algebra-level defs, deferred, PDF held);
Fisher–Schmidt 2014 (skew-product ergodicity — heavy geometric defs,
deferred, PDF held); B–M strong hot spot (Thms 3.4/3.5 sequence-space
form, deferred, PDF held).

**Papers worth fetching (operator-owned):** Mahler 1973 (Bull. Austral.
Math. Soc. 8) and Berend–Boshernitzan 1994 (Acta Arith. 66) — both only
tier S here; Adamczewski–Rampersad PAMS 136 (2008); Waldschmidt
arXiv:0908.4034 (survey, pins Conjecture 1.1 and the Mahler chain).

**Operator-authorized 2026-08-29 (Trevor, attended session).**  Execute after
(or interleaved with) `BRIEF-adder-tower.md` — statement-layer work is cheap and
makes good budget-tail filler.  Motivation, in the operator's framing: *had we
formalized Berend–Boshernitzan, we wouldn't have re-invented C1 tonight.*  The
repo needs a machine-readable novelty ledger.

## The deliverable

`src/NormalNumbers/Literature.lean` (split by paper if it grows): the STATEMENTS
of the known results adjacent to this repo's work, formalized precisely,
**not proved**.

- **Form**: `def berendBoshernitzan_M31 : Prop := …` — plain `Prop`-valued
  defs in a `NormalNumbers.Literature` namespace.  No `sorry`, no `axiom`, no
  `proof_wanted` — defs elaborate and build green while polluting nothing.
- **Docstring per statement**: full citation (authors, year, venue, theorem
  number when the source gives it), the local source file it was transcribed
  from, and a provenance tier (see below).
- **Wiring bonus** (when nearly free): if a theorem we've already proved
  discharges a literature statement, add the edge —
  `theorem berendBoshernitzan_M31_holds : berendBoshernitzan_M31 := …`
  from the C1 certificates, say.  That upgrades "we cite it" to "we
  independently verified it," which is exactly the known-answer-test value.
  Don't grind for these; take the ones that fall out.

## Provenance tiers — 🚨 never fabricate a statement

- **Tier P (primary)**: transcribed from a paper we hold locally in
  `papers/` (PDF + companion `.md`).  Read the local files; do NOT attempt to
  download anything — you will wall on a permission.
- **Tier S (secondary)**: the precise statement appears only in our own
  docs/dossier quoting the paper (e.g. B–B 1994 M(3,1)=2 via
  `docs/mahler-sets-2026-08-29.md` — we do not hold the PDF).  Formalize what
  the secondary source states, tag the docstring `provenance: secondary
  (docs/…)`, and add a line to the RESULT listing papers worth fetching —
  fetching is operator-owned.
- **Missing**: if no local source pins the exact statement, record the gap in
  the RESULT (paper, what's needed) and move on.  An invented quantifier is
  worse than an empty ledger.

## Seed list (grow it as you read; sources are all local)

1. **Berend–Boshernitzan 1994** — M(3,1) = 2 (= C1) and whatever of their
   M(b, ·) framework the secondary sources pin down (tier S).
2. **Adamczewski–Rampersad boundary** — base-2 words 0, 1, 01, 10 recur for
   every irrational; the openness frontier already cited in the dossier §3
   and the brief docstrings (check `docs/` for the exact source; tier per
   what you find).
3. **Vandehey 2017** (tier P — `papers/vandehey-2017-*.md` + the attack map):
   the §7 affine-images statement and the open problems the attack map names.
4. **Becher–Yuhjtman 2019** (tier P): the abs-normal ∧ CF-normal existence
   statement — we PROVED this (Tier 1 headline); wire the edge.
5. **Scheerer 2017**, **Bailey–Misiurewicz 2006 hot spot**,
   **Fisher–Schmidt 2014** (tier P, local): statements at whatever precision
   the papers give; hot-spot is directly adjacent to the normality machinery.
6. Anything `papers/literature-review.md` flags as adjacent to a claim we've
   proved or queued — that file is the map.

## Discipline

- Statement precision beats coverage: five exactly-transcribed statements
  outrank twenty paraphrases.  Where the paper's statement needs definitions we
  lack (e.g. their M(b, s) notation), define them faithfully in the
  `Literature` namespace with the paper's own names in docstrings.
- The ledger is lane 2 by construction — never report it as novel progress;
  its value is the tripwire.  Future briefs should check candidate theorems
  against this file before claiming novelty (say so in the module docstring).
- RESULT section at the top when done or walled: statements landed (with
  tiers), edges wired, papers-to-fetch list, gaps.

## Out of scope ⛔

Proving literature statements not already discharged by our theorems; fetching
papers (operator-owned); the novelty sweep itself; any outward artifact.
