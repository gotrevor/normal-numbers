# EVIDENCE dossier: the 2026-08-29 tower claims, for formalization 🗼→🔬

Audience: the formalization session (worktree, currently grinding
`BRIEF-adder-disjunction-formalization.md`).  This file is the complete evidence
package for the night's NEW claims: exact statements, the shared proof architecture,
per-claim certificate data, and regeneration commands.  Nothing here disturbs the
frozen brief; treat these as additional cargo for the same family-agnostic pipeline.

**Evidence tier of everything below**: exact integer-graph certificate, ONE Python
implementation (`experiments/`), self-tested; the base-3/4/5 and single-track code
paths are fresh (written 2026-08-29).  ⚠️ **Your Lean development is intended as the
independent reimplementation**: derive the automata from the construction rules in
§1 - do NOT import our transition tables - so a kernel-checked collapse becomes
two-instrument agreement.  If your automaton for any claim does NOT collapse, that
is a finding; report it back rather than patching.

---

## §1. Shared proof architecture (all claims instantiate this)

### 1.1 Setup and conventions

Base g ≥ 2.  Digit of a real t at position n ≥ 1: `dig_g(t, n) = floor(g^n t) mod g`
(floor convention: terminating expansions get all-0 tails; no two-representation
issues arise because everything below is an algebraic identity in floor/frac).
"Word w occurs i.o. in t (base g)" := ∀N ∃n > N such that the digits of t at
positions n, n+1, ..., n+|w|−1 spell w.  For single digits, |w| = 1.

### 1.2 The carry identity (Lemma A - the heart)

Channel = pair (a, b) ∈ ℤ², (a,b) ≠ (0,0), tracking z = aX + bY.
Define u_n = frac(g^n X), v_n = frac(g^n Y), w_n = frac(g^n z), and the
**true carry** T(n) = a·u_n + b·v_n − w_n.

- **T(n) is an integer**: g^n z = a·g^n X + b·g^n Y, subtract floors.
- **Range**: a·u_n ∈ [min(a,0), max(a,0)) and likewise for b, w_n ∈ [0,1), so
  T(n) ∈ (a⁻ + b⁻ − 1, a⁺ + b⁺) hence T(n) ∈ [a⁻+b⁻, a⁺+b⁺ − 1] (integers), where
  a⁻ = min(a,0), a⁺ = max(a,0).  (The probes use the superset [a⁻+b⁻, a⁺+b⁺];
  either range is sound - the automaton must merely CONTAIN all true carries.)
- **Recursion**: with x_n = dig_g(X,n) etc., from g·u_{n−1} = x_n + u_n:

      a·x_n + b·y_n + T(n) = g·T(n−1) + z_n,   z_n = dig_g(z, n).

  I.e. digit z_n = (a·x_n + b·y_n + T(n)) mod g and T(n−1) = (…) div g.
  **Carry flows deep → shallow**: T(n) (deeper) determines T(n−1).

Single-track specialization (channels m·x, b = 0, rename a = m): T(n) =
m·u_n − w_n ∈ [0, m−1]; probes use [0, m] (superset, sound).

### 1.3 The joint automaton (Lemma B)

For a family F = {(a_i, b_i, w_i)}: joint state = (carry_i, kmp_i)_i where kmp_i is
the standard factor-automaton state of word w_i over the digits of channel i, read in
the SAME deep→shallow direction (the probes therefore track the REVERSED word; for
single digits kmp is trivial - state dies iff the emitted digit equals the avoided
one).  Input alphabet: (x_n, y_n) ∈ {0..g−1}² (single-track: {0..g−1}).  Transition
on symbol at position n maps state-at-n → state-at-(n−1) by the §1.2 recursion; any
transition that emits a completed word w_i (or the avoided digit) is deleted.

**Soundness**: if every w_i occurs only finitely often in channel i, choose N beyond
all last occurrences; then the TRUE sequence σ_n = (T_i(n), kmp_i(n))_{i}, n ≥ N, is
an infinite deep-ward walk in the automaton (each σ_{n+1} → σ_n is a legal edge).

### 1.4 The zero-entropy certificate (Lemma C)

**Certificate property**: after iteratively pruning states with no outgoing edge,
every strongly connected component of the remaining graph is a simple cycle (every
vertex has exactly one intra-SCC out-edge).  This is a finite, decidable property -
in Lean, `decide`-able on the explicit graph (prefer `decide +kernel` per house
rules).

**Lemma C**: in such a graph, every infinite walk is eventually periodic.  (An
infinite walk crosses SCCs in DAG order, so finitely many crossings; its tail stays
inside one SCC; inside a simple cycle the intra-SCC out-edge is unique, so the tail
follows the cycle.)  ⚠️ Direction note: the true walk (§1.3) runs DEEP-ward
(σ_N ← σ_{N+1} ← …), i.e. it is an infinite walk in the TRANSPOSE graph.  The
certificate property is transpose-invariant (SCCs and being-a-simple-cycle are), so
state Lemma C for the transpose or check the property on both - cheapest is to note
simple-cycle SCC structure survives edge reversal.

### 1.5 Aperiodicity closes it (Lemma D)

If σ_n is eventually periodic in n, the input symbols along the walk are eventually
periodic, i.e. the digit tails of X and Y are eventually periodic, i.e. X and Y are
BOTH rational.  Contrapositive: X, Y not both rational ⟹ no infinite live walk ⟹
some w_i occurs i.o. in channel i.  ∎

**Theorem template** (what each certificate licenses):

> For all reals X, Y not both rational: ⋁_i (w_i occurs i.o. in the base-g digits
> of a_i X + b_i Y).

Single-track: "for every irrational x: ⋁_i (w_i occurs i.o. in base-g of m_i·x)."
Named constants (ln 2, ln 3, π, …) are instances; only irrationality is consumed.

---

## §2. The claims, with certificate data

Every claim below passed the exact SCC/simple-cycle check in our implementation.
"Live/periods" figures are our implementation's, for cross-checking - your counts
may differ if your state encoding differs; the THEOREM depends only on your own
certificate passing.  Regeneration: run the named script (uv shebangs, self-testing).

### Tier 1 - cheapest, hand-provable, do first 🥇

**C1. Ternary digit theorem for {1,2}** (single-track, base 3, m ∈ {1,2}):
For every irrational x and EVERY d ∈ {0,1,2}: d occurs i.o. in base-3 of x or of 2x.
Three certificates (both channels avoid the same d); our sizes: 6 states.
Script: `mahler_minimal_sets.py`.  **Independent hand proof for d = 1** (formalize
this directly if cheaper): suppose x's ternary tail avoids 1, so tail digits ∈
{0,2}.  Then the carry into position n is c = 1 iff x_{n+1} = 2 (since
frac(3^n x) ≥ 1/2 iff its first digit is 2, digits being in {0,2}); digit of 2x at
n is (2x_n + c) mod 3, which is 1 whenever (x_n, x_{n+1}) ∈ {(2,0), (0,2)}.
Avoiding digit 1 in 2x's tail thus forbids both 20 and 02, forcing a constant tail,
making x rational.  Contradiction.  (For d = 0 and d = 2 use the certificates; no
hand proof recorded.)

**C2. Ternary all-digits PRODUCT BLOCK {2,11}**:
For every irrational x: 2x or 11x contains ALL THREE ternary digits i.o.
Evidence = NINE certificates (channels {2,11}, every assignment (d₁,d₂) ∈ {0,1,2}²
of avoided digits collapses; our sizes ≤ 36 states) + one purely logical lemma:

  *Transversal lemma*: if for every (d₁,d₂) the clause "d₁ i.o. in 2x ∨ d₂ i.o. in
  11x" holds, then "all d i.o. in 2x ∨ all d i.o. in 11x."  Proof: contrapositive -
  if 2x misses some d₁ and 11x misses some d₂, clause (d₁,d₂) fails.  (Finitely many
  digits; no compactness subtleties.)

Verified inline (see session log / re-run):
`uv run python3 -c "from mahler_minimal_sets import Mult, exact_zero; print(all(exact_zero([Mult(2,d1),Mult(11,d2)]) for d1 in range(3) for d2 in range(3)))"`.

**C3. {1,5} variants** (single-track, base 3): for every irrational x and every d:
d occurs i.o. in x or 5x.  Same shape as C1, no hand proof, ~12 states.

### Tier 2 - small two-track certificates 🥈

**C4. Base-3 four-channel single-digit family** (two-track, base 3; our 72 live
states, all fixed points): for X, Y not both rational, at least one of -
digit 0 i.o. in Y · digit 2 i.o. in 3Y · digit 0 i.o. in 3X+Y · digit 2 i.o. in X+Y
(instances ln 3, ln 27, ln 24, ln 6).  Channels/digits: (0,1)/0, (0,3)/2, (3,1)/0,
(1,1)/2.  Script: `base3_digit_hunt.py`.

**C5. Escape from Cantor** (two-track, base 3; 261 live, fixed points): for X, Y not
both rational, at least one of Y, 2Y, X+4Y, 2X, 4X has ternary digit 1 i.o.
Channels: (0,1), (0,2), (1,4), (2,0), (4,0), all avoiding digit 1.  Instances:
ln 3, ln 9, ln 162, ln 4, ln 16.  y = x instance: for irrational x, one of
x, 2x, 4x, 5x has ternary digit 1 i.o. (subsumed by C1 - formalize C1 instead;
C5's value is the two-real form).  Script: `base3_cantor_beam.py`.

**C6. Base-4 positioned-binary family** (two-track, base 4; 676 live): for X, Y not
both rational, at least one base-4 digit claim holds i.o.: 3 in X · 1 in X+3Y ·
3 in X+4Y · 2 in 2X−Y · 0 in 2X · 0 in 2X+2Y.  (Base-4 digit d at position n =
binary word [d≥2][d mod 2] at even-aligned position 2n − 1: this family is a
POSITIONED-binary statement.)  Script: `base_g_digit_hunt.py 4`.

### Tier 3 - the base-2 word families 🥉

**C7. Musical (superparticular) family** (two-track, base 2; 9 478 live, periods
{1,2}): channels/words (1,0)/`00`, (0,1)/`11`, (−1,1)/`100`, (2,−1)/`11`,
(−3,2)/`00`, (1,1)/`010`.  Instances ln 2, ln 3, ln 3/2, ln 4/3, ln 9/8, ln 6.
Note negative coefficients: use the §1.2 general carry range.  Script:
`pythagorean_closure.py`.

**C8. Complemented flagship** (two-track, base 2; 23 073 live, periods {1,2}):
(1,0)/`11`, (0,1)/`110`, (1,1)/`00`, (1,2)/`110`, (2,1)/`101`, (1,3)/`111`.
Either certify directly (recommended - independence) or formalize the complement
involution ((x,y,c) ↦ (1−x, 1−y, a+b−1−c) conjugates avoid-w to avoid-w̄) and
derive from the brief's base family.  Script: `product_block_hunt.py` self-test.

**C9 (optional).** Second base-2 channel set and the 7 distance-1 neighbors of the
flagship - data in `docs/adder-family-2026-08-29.md`; same pipeline, lower priority.

### NOT for formalization ⛔

Floors and negatives (product-block k=8 floor 0.4057, base-5 pending, "no other
2-sets") - these are method-relative search outcomes, not theorems, and several
carry a known float-gate caveat (`docs/mahler-sets-2026-08-29.md` §gate-bug).

---

## §3. Practical notes for the Lean side

- **Statement form**: use the i.o. definition of §1.1 directly (∀N ∃n > N …).
  Keep the hedge INSIDE each statement: hypothesis "¬(X ∈ ℚ ∧ Y ∈ ℚ)" (two-track)
  or "Irrational x" (single-track); base g explicit.
- **Decidability route**: define the automaton from §1.2-1.3 rules for the claim's
  (g, channels, words); compute reachable live graph; `decide +kernel` the pruned
  simple-cycle-SCC property.  State counts above say which fit comfortably.
- **Reading direction**: get §1.4's transpose note right before anything else; it is
  the likeliest place for a silent mismatch between your automaton and ours.
- **Transition tables provided**: `experiments/certs/tower-2026-08-29.json` - 20
  per-channel tables covering every claim (C1×3, C2×9, C3×3, C4-C8), each claim
  re-verified at emission; format documented in `emit_tower_certs.py`'s docstring.
  Use them freely for cross-checking and debugging.  The independence point is
  narrower than "don't look": let your Lean DEFINITION of the automaton be the §1.2
  rules (a function `decide` computes), with the tables as expected-output test
  data - then the kernel check is still an independent derivation.  Divergence from
  our live-state counts is fine; divergence in a COLLAPSE VERDICT is a finding -
  report it rather than patching.
- **Known-recurring boundary** (context for why these words/digits): base 2 words
  0, 1, 01, 10 recur for every irrational (transition argument); single digits are
  open in base ≥ 3; 00/11 open for non-algebraic constants.  None of the claims
  above carries a vacuous disjunct.
- Priority if grinding order is yours to choose: C1 (+hand proof), C2, C3, C4, C5,
  C6, C7, C8.  C1+C2 together give the headline "2x or 11x is ternary-digit-alive,
  and every digit lands in x or 2x" pair.
