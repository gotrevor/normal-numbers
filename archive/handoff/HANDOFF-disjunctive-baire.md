# HANDOFF: the disjunctive Baire slate 🥇

*Staged 2026-08-25.  Trevor picks this up in a fresh session; this file is the full context
transfer.  Estimate and de-risking were done live on 2026-08-25 - see "Estimate" below.*

## The target

**Headline (Tier 1, the catalog row `absolutely-disjunctive-comeager`):**  the set of absolutely
disjunctive reals - every finite word occurs in the base-b expansion, for every b ≥ 2 - is
**comeager** (residual) in ℝ.  Calude-Zamfirescu's "the typical real is a lexicon."

**Tier 2 (the punchline):**  for each b ≥ 2, `{x | IsNormal b x}` is **meager**; corollary, the
two comeager sets meet: ∃ x absolutely disjunctive ∧ normal in **no** base.  This delivers a
separating-witness edge on the landscape board (`disjunctive ⇏ normal`, generically) and the
quotable exhibit "a lexicon with no statistics."

Math context: `docs/disjunctive-vs-normal.md` §1.3 and §3 (the category facts and the cheap
witnesses).  This is folklore mathematics - the value is the `Disjunctive` API, the landscape
edges, and (hedged) first-formalization of the corner.

## What exists already (verified 2026-08-25)

- **Repo, all general-base**: `digitOf (b : ℕ) (x : ℝ) (i : ℕ)` and `IsNormal (b : ℕ) (x : ℝ)`
  in `src/NormalNumbers/RealDefs.lean`; digit↔interval toolkit in `DigitInterval.lean`
  (`digits_prefix_iff` is the workhorse: digit-prefix ⟺ b-adic interval membership); counting
  algebra in `Counting.lean`/`Visits.lean`.  ⚠️ Read `RealDefs.lean` FIRST for the exact index
  convention and how `digitOf` treats the integer part / negative x - the statements below must
  align with it, and this handoff deliberately does not guess.
- **mathlib pin has everything needed**: `residual`, `IsMeagre` (`Topology/GDelta/Basic.lean`),
  `dense_iInter_of_isOpen [Countable ι]` (`Topology/Baire/Lemmas.lean`), BaireSpace for ℝ, and
  the direct proof-shape template `Mathlib/NumberTheory/Transcendental/Liouville/Residual.lean`
  (Liouville numbers are residual - same dense-Gδ-by-cylinder-surgery game).
- **Zero measure theory, zero ergodic theory.**  Pure Baire category + digit combinatorics.

## Statement sketches (align with repo conventions before freezing)

```lean
def OccursAt (b : ℕ) (x : ℝ) (w : List ℕ) (n : ℕ) : Prop := ...  -- digits n..n+|w|-1 spell w
def IsDisjunctive (b : ℕ) (x : ℝ) : Prop :=
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ n, OccursAt b x w n
def AbsolutelyDisjunctive (x : ℝ) : Prop := ∀ b, 2 ≤ b → IsDisjunctive b x

theorem residual_absolutelyDisjunctive : {x | AbsolutelyDisjunctive x} ∈ residual ℝ  -- Tier 1
theorem isMeagre_setOf_isNormal (b) (hb : 2 ≤ b) : IsMeagre {x | IsNormal b x}      -- Tier 2
theorem exists_absolutelyDisjunctive_forall_not_isNormal :
    ∃ x, AbsolutelyDisjunctive x ∧ ∀ b, 2 ≤ b → ¬ IsNormal b x                       -- corollary
```

**Freeze decision made 2026-08-25: state on all of ℝ**, not [0,1] (avoids subtype topology; the
occurrence sets are 1-periodic if `digitOf` reads the fractional part - confirm when reading
`RealDefs.lean`, else restrict honestly and say so in the docstring).

## Proof routes

**Tier 1** (`DisjunctiveBaire.lean`).  For each (b, w):
`U b w := ⋃ n, interior {x | OccursAt b x w n}` - open for free.  Dense: inside any open interval
find a full b-adic cylinder (go deep enough), append w to its address; the sub-cylinder's interior
is a nonempty open subset of the occurrence set (`digits_prefix_iff` does the interval bridge).
Using **interiors of half-open cylinders dodges the b-adic double-expansion boundary issue
entirely** - never fight endpoints.  Then intersect over the countable index (b, w)
(`Countable (ℕ × List ℕ)` is free) via `dense_iInter_of_isOpen` / `residual` membership.

**Tier 2** (`NormalMeager.lean`).  Fix b.  For k, N:
`V k N := {x | ∃ n ≥ N, freq of digit 0 in the first n digits > 1 - 1/k}` - contains a dense open
set (openness: the witness condition is determined by finitely many digits, take cylinder
interiors; density: append a giant 0-run to any cylinder address).  On ⋂ V k N the limsup of the
zero-digit frequency is 1, but `IsNormal b x` forces that frequency → 1/b ≤ 1/2 (extract the
single-digit instance from the repo's normality definition).  So the normal set misses a comeager
set ⟹ meager.  Intersect the complements over countable b; combine with Tier 1 for the corollary.

**Optional stretch, while the API is warm**: the `b ↔ b^k` padding lemma (route in the catalog
row body) and `isDisjunctive_iff_denseOrbit` (ROADMAP Track D0 - the topological twin of Wall).
Both are natural residents of `Disjunctive.lean`; neither blocks the headline.

## Estimate (2026-08-25, confidence 75%)

~800-1300 lines total: `Disjunctive.lean` ~200-350, `DisjunctiveBaire.lean` ~250-450,
`NormalMeager.lean` ~300-500.  **2-4 treadmill laps, sonnet/low grinder is plenty with frozen
statements** (easier than Stoneham, which took 2 fable/low laps); 1-2 days wall clock, weekend by
hand.  Overrun mode is floor-arithmetic fiddliness in the density surgery, not math risk.

## Pre-flight (10 minutes, then freeze)

1. `zulip-ro search` for disjunctive/lexicon/comeager-normal - the 2026-08-25 sweep found the
   corner unformalized anywhere, but the formal in-flight check has not been run as such.
2. Read `RealDefs.lean` + `DigitInterval.lean`; align the statement sketches; freeze
   `Disjunctive.lean` defs + the three headline statements.
3. Confirm the ℝ-vs-fract behavior of `digitOf` (see freeze decision above).

## Close-out gates (house standard)

- Guarded `#print axioms` on all three headlines = standard triple; `/lean-review` clean;
  statements byte-identical to the freeze.
- Flip the catalog row `absolutely-disjunctive-comeager` to `shipped` **at ship time** (lesson
  from tao-collatz, which sat `chosen` six weeks: the ship-day list now includes the catalog).
- Update `docs/irregularity-landscape.md` status board (the comeager row + the separation edge)
  and `docs/disjunctive-vs-normal.md` §5 table; re-render/republish the landscape artifact only
  at Trevor's direction.
- **Claim discipline**: the mathematics is Calude-Zamfirescu folklore - never "new math."
  Formalization novelty stays hedged: "apparently first in any prover, per the 2026-08-25 sweep."

## Provenance

Chosen by Trevor 2026-08-25 ("This does seem like a good one to pick up") after the receipt audit
established the row has **no community ask** - the receipt is the 1999 paper itself.  It is an
"unasked-for" target on purpose: cheapest entry to the outer ring, seeds Track D's `Disjunctive`
API, and lands two landscape edges.  Session context: the conditional-disjunctivity axiom slate
(`docs/conditional-disjunctivity.md`) was authored the same day; this target is its unconditional
warm-up.
