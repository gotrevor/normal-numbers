# Tower novelty audit: what is actually new? 🔎

**Audit completed 2026-08-30.**  This is the durable literature and proof audit for
`EVIDENCE-2026-08-29-tower-formalization.md`.  It separates four questions that the
original evidence dossier blurred together:

1. does the finite graph computation say what the prose claims?
2. does the finite graph certificate imply the number-theoretic statement?
3. is the statement already in the literature or an immediate corollary?
4. if it is new, how much mathematical content does it carry?

## Bottom line

**Yes, there is credible real new mathematics here, but not nine independent new
theorems.**  My present judgment:

- **C2 is the cleanest likely-new result:** every irrational `x` has all three
  ternary digits recurring infinitely often in either `2x` or `11x`.  Mahler and
  Alon-Peres prove that some multiplier works, but no inspected source gives this
  fixed universal two-element hitting set.  No singleton can work universally, so
  the cardinality two is optimal.
- **The flagship, C6, C7, and C10 are credible new computer-assisted finite-state
  theorems.**  Their genuinely different feature is simultaneous avoidance across
  fixed linear forms in two arbitrary reals.  I found no theorem in the direct
  Mahler citation cone that subsumes that form.
- **C1 is classical.**  Berend-Boshernitzan explicitly state `M(3,1)=2`, which is
  exactly C1.
- **C4 is elementary, C5 is an immediate corollary of C1, and C8 is a symmetry
  corollary of the flagship.**  They are true, but should not be counted as
  independent new mathematical advances.
- **C3 and C9 are family-census data.**  They may be new exact variants, but they do
  not add a new idea.

Confidence that the surviving exact statements are not already in the inspected
literature: **70% for C2, 65% for the exact two-track families, and 45% for the
general carry-automaton presentation as a novel method.**  Those are novelty
estimates, not correctness estimates.

## Mathematical soundness audit

### What the computation really certifies

The checker builds one transition for each input digit or input digit-pair.  Its
exact-zero test counts repeated rows with multiplicity.  Thus two different input
labels leading from the same state to the same successor count as two intra-SCC
outgoing edges and fail the test.

This matters.  A simple cycle in the underlying unlabeled graph would make the state
sequence periodic without necessarily making the input sequence periodic.  The
implemented certificate is stronger: every recurrent state has one **labeled**
intra-SCC edge.  Therefore an eventually periodic state walk has eventually periodic
input digits, which makes both input reals rational.  The original dossier needs the
word “labeled” in Lemmas C and D.

### KMP state soundness

The dossier refers to a “true sequence” of KMP states without defining it.  The
clean finite argument is to let the word-state at depth `n` be computed from the
finite window of the next `|w|-1` emitted digits.  Beyond the last occurrence of
the forbidden word, these states and the true carries form a legal walk.  An
equivalent proof takes all finite tail walks and applies compactness, but the finite
window definition is cheaper for Lean.

### Carry range correction

For a channel `aX+bY`, the always-sound integer superset is

    [min(a,0)+min(b,0), max(a,0)+max(b,0)].

The sharper upper endpoint one lower is valid when at least one coefficient is
positive, but not for arbitrary all-nonpositive coefficients.  For example the
quantity can equal zero when both coefficients are nonpositive.  The programs use
the sound superset, and every listed negative-coefficient channel also has a
positive coefficient, so this prose error does not invalidate a certificate.

### Present evidence tier

The exact SCC calculations and their self-tests are strong evidence.  Re-encoding
the tables does not make a second mathematical derivation, however, and the Lean
formalization has not yet proved the main collapse theorem.  My correctness estimate
is **88% for C2 and 85% for the larger two-track claims** pending the independent
Lean derivation.  C1, C4, C5, and the complement implication in C8 have direct proofs
and are above **98%**.

## What the primary literature actually says

### Mahler 1973

Mahler's Theorem 1 says that for an irrational `alpha`, a base `g`, and one
specified length-`n` block, some bounded positive integer multiplier makes that
block occur infinitely often.

More importantly, Mahler's Theorem 2 already obtains **one multiplier containing
every length-`N` block infinitely often**.  He applies Theorem 1 to a finite word
containing all length-`N` blocks.  Thus “one multiplier has all ternary digits” is
classical.  The crude specialization `g=3, N=1` gives a multiplier below
`3^7 = 2187`.

### Alon-Peres 1992

Corollary 7.2 gives the same qualitative conclusion: for every irrational
`alpha`, some integer multiple has every base-`b` digit infinitely often.  The
remark following it is much stronger about the available multipliers: the good
multipliers have density one and may be selected from Glasner sets such as the
primes or squares.  This still does not give a fixed finite hitting set independent
of `alpha`.

### Berend-Boshernitzan 1994

Their Theorem 1.1 improves the bound for one prescribed length-`k` block.  On page
318 they state

    M(g,k) >= g^k - 1,

and explicitly say equality holds for `g=2,k=1` and `g=3,k=1`.  Therefore
`M(3,1)=2`: for every irrational `x` and each chosen ternary digit `d`, that
digit occurs infinitely often in `x` or `2x`.  This is exactly C1.

### Berend-Boshernitzan 1995

This paper introduces `M_g`-sets, sets of allowed multipliers that work for every
irrational and every finite block.  Remark 3.1 observes that an `M_g`-set supplies,
for each fixed block length, one member containing every block of that length.
Corollary 3.3 says deleting any finite subset of an `M_g`-set leaves an
`M_g`-set, so no finite set can solve the unrestricted all-block-length problem.

That theorem does **not** rule out C2.  C2 is the truncated length-one problem, for
which a finite hitting set can exist.

### Later papers and surveys

- Adamczewski-Bugeaud 2005 is an expository paper on the block complexity of
  algebraic irrational expansions.  It cites Mahler and Berend-Boshernitzan but does
  not study fixed finite multiplier sets.
- Waldschmidt 2009 surveys words and transcendence.  It locates the result in the
  broader digit-complexity literature but gives no fixed set matching C2 and no
  two-track linear-form theorem.
- Meher-Kumar-Thangadurai 2017 gives quantitative/frequency conclusions under a
  hypothesis that long zero blocks occur in `alpha` with a frequency.  It does not
  give an unconditional fixed set such as `{2,11}`.
- Thangadurai-Tripathi 2025 gives an explicit interval of multipliers, again under a
  prescribed zero-block occurrence hypothesis on `alpha`.  It likewise does not
  subsume C2 or the two-track families.

## Claim-by-claim disposition

| Claim | Correctness route | Novelty disposition | Mathematical weight |
|---|---|---|---|
| C1, `{1,2}` per ternary digit | B-B 1994, plus certificates | **Classical** | Excellent regression theorem |
| C2, `{2,11}` all ternary digits | 9 exact certificates plus transversal lemma | **Likely new exact fixed set** | Cleanest headline |
| C3, `{1,5}` per digit | exact certificates | likely unprinted variant | census datum |
| C4, four base-3 channels | direct elementary proof below | perhaps unprinted, but not deep | do not headline |
| C5, escape from Cantor | immediate C1 case split below | **not new once C1 is known** | redundant middle channel |
| C6, positioned base-4 family | exact certificate | **credible new candidate** | real two-track content |
| C7, musical binary family | exact certificate | **credible new candidate** | real two-track content |
| C8, complemented flagship | complement involution | corollary, not independent | useful consistency check |
| C9, neighbors and second set | exact certificates | likely unprinted variants | collapse-locus census |
| C10, base-5 family | exact large certificate | **credible new candidate** | valid rung, less elegant |
| original flagship | exact certificate | **credible new candidate** | central two-track theorem |

## Short deductions that change the ranking

### C2 has optimal cardinality

No fixed singleton `{m}` can work for every irrational.  Choose an irrational
`beta` whose ternary expansion omits a digit, and set `x = beta/m`.  Then `x`
is irrational and `mx = beta` omits that digit.  Therefore any universal fixed
hitting set needs at least two multipliers.  If the `{2,11}` certificate survives
formalization, it is cardinality-optimal.

This does not prove that the particular pair `{2,11}` is coefficient-optimal, nor
that it is the unique two-element solution.

### C4 has a direct proof

Assume all four disjuncts fail.

1. Digit 2 occurs infinitely often in `3Y` iff it does in `Y`, apart from the
   shift of one digit.
2. Failure of digit 0 in `Y` and digit 2 in `3Y` forces the ternary tail of
   `Y` to consist only of 1s.  Hence `Y` is rational and `2Y` has a terminating
   ternary expansion.
3. Since `X,Y` are not both rational, `A=X+Y` is irrational.
4. `3X+Y = 3A-2Y`.  Subtracting the terminating ternary number `2Y` changes only
   finitely many tail digits, so the tails of `3X+Y` and `3A` agree.
5. Failure of digit 0 in `3X+Y` and digit 2 in `A` now forces the tail of `A`
   to consist only of 1s, making `A` rational.  Contradiction.

### C5 is a C1 corollary

If `Y` is irrational, apply C1 for digit 1 to `Y`: digit 1 recurs infinitely
often in `Y` or `2Y`.  If `Y` is rational, then `X` is irrational and so is
`2X`; apply C1 to `2X`: digit 1 recurs infinitely often in `2X` or `4X`.
The channel `X+4Y` is never needed.

### C8 is one symmetry, not another discovery

The binary digit-complement involution conjugates the flagship avoiding automaton
to C8.  A direct second certificate is valuable independent verification, but C8
should be described mathematically as a corollary of that involution.

## Search boundary and absence claim

The audit read the eight PDFs pinned beside this file.  It also ran:

- an OpenAlex forward-citation crawl of Mahler 1973, Alon-Peres 1992, and
  Berend-Boshernitzan 1994;
- a Semantic Scholar forward-citation crawl of Berend-Boshernitzan 1994;
- exact web searches for `2 alpha`/`11 alpha`, ternary digits, fixed multiplier
  sets, simultaneous digit avoidance, and carry automata.

OpenAlex returned four direct citing works for B-B 1994.  Semantic Scholar returned
the same substantive papers plus Adamczewski-Bugeaud 2005 and a bibliography-only
record for Bugeaud's 2012 book.  Every substantive paper in that union was read.

No inspected source states C2's fixed set or a theorem subsuming the two-real fixed
linear-form families.  This is an evidence-bounded **“not found”**, not proof of
priority.  MathSciNet, zbMATH, theses, non-English literature, and papers missed by
both citation indices remain possible hiding places.  Before an outward priority
claim, an expert literature check is still owed.

## Recommended mathematical presentation

Lead with C2 as an optimal two-multiplier ternary theorem.  Present the two-track
binary/base-4 families as computer-assisted carry-automaton theorems and the
finite-state collapse criterion as the reusable mechanism.  Treat C1 as the
classical calibration point, C4 and C5 as reductions, C8 as symmetry, and C3/C9 as
census evidence.

That presentation says what the mathematics actually contributes without turning a
certificate count into the headline. 🪷
