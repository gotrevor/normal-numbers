# The transversal ceiling - can disjunctions be sussed into disjunctivity? 🧗

2026-08-29, sixth story.  Operator question (verbatim intent): given many factory clauses
of the shape "a₁ ∈ A ∨ b₁ ∈ B", "a₂ ∈ A ∨ b₂ ∈ B", "a₁ ∈ A ∨ c₁ ∈ C", ... - with enough
classes of families, can we suss out "**A or B or C must be disjunctive**"?

Answer in three layers: an exact propositional characterization (yes, iff the family is
*transversal-complete*), a semantic **no-go** (universal clauses can never be
transversal-complete - explicit blocking pair, probe-verified), and the rung that
survives (a graded joint-visit conjecture, factory-expressible).  Probe:
`experiments/sparse_pair_blocking.py` (self-testing, known-answer control).

## 1. The exact propositional answer: transversal covers 🎯

Atoms `P(w, m)` = "word w occurs i.o. in channel m".  Factory output = monotone clauses
(finite ORs of atoms).  Target, for a finite channel set M:

> ⋁_{m∈M} ⋀_{all words w} P(w, m)   ("some channel in M is disjunctive")

**Characterization.**  A clause family entails the target **iff** for every *failure
transversal* - every choice of one failed word f(m) per channel m ∈ M - some clause has
all its atoms inside {(f(m), m) : m ∈ M}.  (Minimal countermodels fail exactly one word
per channel; a clause dodges them all iff the family covers every transversal.)

Two corollaries:

- **Rainbow lemma.**  A clause naming two different words on the *same* channel is
  useless for this target: no transversal contains both, so every minimal countermodel
  satisfies it for free.  Only rainbow clauses (≤ 1 word per channel, channels ⊆ M)
  contribute.  The flagship six-family is rainbow - it covers exactly the transversals
  extending its own word tuple, i.e. one cylinder out of infinitely many.
- **Positive lemma (what "enough" means).**  A *complete product* family suffices: if for
  EVERY pair of words (u, v) the clause "u ∈ A ∨ v ∈ B" is a theorem, then "A is
  disjunctive ∨ B is disjunctive" follows.  (Countermodel kills some u in A and some v in
  B; the (u, v) clause catches it.  The infinite-conjunction target follows from its
  finite-F truncations by pigeonhole: finitely many channels, nested F's, so one channel
  witnesses cofinally, hence everywhere.)  Any *missing* pair (u, v) re-opens the
  countermodel.  So the question "can the factory get there?" becomes: **can the collapse
  locus contain a full product block over all words?**

## 2. The no-go: universality caps the factory below disjunctivity 🧱

It cannot - and not for internal monotone-logic reasons this time, but semantically.

**Blocking pair.**  Take x = Σ_{k≥1} 2^(−2^k) (irrational - gap growth), and the
admissible pair (X, Y) = (x, x).  Every lattice channel is a·X + b·Y = m·x, m ≥ 1.  The
binary tail of m·x is isolated copies of bin(m) separated by ever-longer 0-runs (the
blocks stop interacting once 2^k outruns len(bin(m))), so the words occurring i.o. in
m·x are exactly the factors of 0^* bin(m) 0^*.  In particular 1^(len(bin(m))+1) never
occurs: **no channel of the entire infinite lattice is disjunctive for this pair.**
Probe-verified at the digit level for m ∈ {1, 3, 5, 6, 7, 100, 1000} with a seeded-random
control that sees both failure modes (`sparse_pair_blocking.py`).

**Consequence.**  Every universal clause (true for ANY pair not both rational) is true on
the blocking pair; the target is false there; so **no set of universal clauses - the
factory's or anyone's - entails "some channel is disjunctive"**, even taking M to be the
whole lattice, even with infinitely many clauses.  This extends the no-singleton negative
and is sharper in kind: no-singleton was a ceiling of *monotone logic*; this is a ceiling
of *universality itself*.  Any proof that a specific channel of (ln 2, ln 3) is
disjunctive must consume arithmetic that distinguishes ln 2 from the blocking pair -
which is exactly the map's method boundary ("the kick 1/n is not finite-state"), now
derived semantically rather than observed operationally.

**Blocking pairs as pre-filters for the classification (story #1).**  Every universal
clause must be TRUE on (x, x): at least one of its atoms (w, m) must have w a factor of
0^* bin(m) 0^*.  So any word tuple violating this for every channel - e.g. assign each
channel m the word 1^(len(bin(m))+1) - **provably never collapses, on any channel set**.
That is a zero-cost necessary condition to bolt onto `adder_family_enum.py`, and a
known-answer test in the other direction: the integer-graph engine must agree that these
pre-filtered tuples stay open (two instruments, independent origins).  Variant sparse
pairs (Σ 2^(−n!), shifted gap sequences, Y = c·X) each yield further blocking conditions;
the collapse locus lives inside their intersection.

## 3. What survives: the graded joint-visit ladder 🪜

The blocking pair does NOT refute this statement: for every finite word set F, some
channel visits all of F i.o. (on (x, x): pick m with bin(m) containing every w ∈ F).  And
§1's positive lemma makes it factory-expressible:

> **Product-Block Conjecture.**  For every finite word set F there is a finite channel
> set M_F on which EVERY word tuple in F^{M_F} collapses.  Each such block yields the
> universal theorem: for any pair not both rational, some channel in M_F contains every
> word of F infinitely often.

This is a genuinely new rung strictly between the factory's rung zero (one word, somewhere)
and disjunctivity (all words, one fixed channel): **all of F, some channel - with the
witness allowed to move as F grows**.  The blocking pair even gives an unconditional
lower bound on how far it must move: on (x, x) a joint-visit witness m needs bin(m) to
contain each w ∈ F, so len(bin(m)) ≥ max_{w∈F} |trim(w)| - the two-variable cousin of the
Mahler / Berend-Boshernitzan g^k witness bounds (same genre, consistent shape).

Current data says nothing yet either way: 7/54 collapsing neighbors is far from a product
block on the six-channel set, but blocks may live on richer channel sets - precisely
where story #1's exhaustive sweep is already pointed.  Smallest interesting instance:
F = {00, 11}, hunt for a channel set where all 2^|M| assignments collapse.

## The or-list is six-ways-true, hence maximally uncollapsible 🎭

(From the 2026-08-29 dialogue.)  Collapsing an or-list means refuting disjuncts - but every
disjunct of the flagship is *believed true* (all six constants are conjecturally normal), so
the disjunction is the deliverable, not a waypoint toward "this one doesn't".  And the two
negatives are complementary ceilings: no-singleton caps *monotone logic* (can't isolate a
constant); the blocking pair caps *universality* (can't reach disjunctivity even of a
disjunction).  Any genuine disjunctivity path must therefore break both at once:
non-monotone reasoning AND arithmetic distinguishing ln 2 from Σ2^(−2^k) - i.e. exactly
the column's non-finite-state 1/n kick.  The factory's ceiling is a quarantine line
pricing the toll, not a dead end for the program.

## Status of the operator's proposal, one paragraph 📌

"Enough classes of families" is exactly the right instinct, and §1 says precisely how
much is enough: a transversal-complete (product-complete) clause family.  The factory can
never supply it - §2's blocking pair caps every universality-preserving method strictly
below disjunctivity, so the answer to "can we suss out A ∨ B ∨ C disjunctive?" is **no,
not from these clauses, provably**.  What the instinct CAN reach is the Product-Block
Conjecture: the same suss-out run at each finite word level, witness channel drifting
upward - the strongest occurrence-currency statement not blocked by any sparse pair.

## Honesty ledger 📋

- The §1 characterization is elementary propositional reasoning (hand argument, no
  probe); the pigeonhole step needs |M| finite - for infinite M the truncations do not
  glue, which is exactly why the Product-Block witness may escape to infinity.
- The blocking-pair factor-language claim is probe-verified at depth 2^13 with a control,
  but "isolated blocks for ALL m simultaneously" rests on the hand argument about
  non-interacting blocks; the probe samples seven m values.  Irrationality of x:
  standard gap argument, not independently checked.
- The pre-filter/engine cross-check (§2, two-instrument agreement on never-collapsing
  tuples) is PROPOSED, not run.
- Nothing here touches the commissioned brief; the flagship theorem is unaffected - this
  story only maps what lies above it.
