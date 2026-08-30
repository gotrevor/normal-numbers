# Minimal Mahler sets - the single-track wing 🎯

2026-08-29, eighth story.  Probe: `experiments/mahler_minimal_sets.py` (single-track
machine: channels m·x, base 3, exhaustive over multiple sets S ⊆ {1..12}, |S| ≤ 4,
every hit exact-checked).  Operator prompt: *"we can't even prove 7 occurs i.o. in
decimal π - if we could say it for π, 2π, 3π… that would be something."*  Mahler 1973
already says that shape (some m ≤ g^(2k+1); B-B 1994: m ≤ 2g^(k+1), lower bound
g^k − 1 in their adversary-word problem).  This wing maps the EXACT landscape the
bounds only gesture at.

## ⚠️ CORRECTED RESULTS (2026-08-29, second run - see "The gate bug" below) 📋

- **Every digit has minimal size 2, and {1,2} works for ALL THREE digits**:

  > **For any irrational x and EVERY ternary digit d: d occurs i.o. in x or in 2x.**
  > Instance: for each d, **π or 2π has ternary digit d infinitely often.**

  The digit-1 case has a five-line HAND PROOF (the correction's trigger): for tail
  digits in {0,2}, the digit of 2x at position n is (2xₙ + c) mod 3 with carry c = 1
  iff x_{n+1} = 2; both patterns 20 and 02 emit digit 1, so avoiding it forces a
  constant tail = rational.  {1,5} is also a 2-set for every digit; 133 minimal sets
  total across the three digits, identical digit-0/2 lists (involution cross-check).
  B-B's lower bound (g^k − 1 = 2) is met exactly, by every digit - the earlier
  "edge/interior asymmetry" was ENTIRELY a bug artifact.

- **PRODUCT BLOCK {2, 11}: the joint-visit rung stands.**  All 9 (d₁, d₂) mixed
  assignments collapse on channels {2, 11} (also {6,11} = 3·{2,11}; none containing
  m=1), so by the transversal machinery:

  > **For every irrational x: 2x or 11x contains ALL THREE ternary digits i.o.**
  > Instance: **2π or 11π has every ternary digit infinitely often.**

  On {1,2} the mixed assignments fail in the involution pattern (collapse iff
  d₁ = d₂ or {d₁,d₂} = {0,2}) - a block needs the right arithmetic, not just any
  collapsing pair.  Note the contrast: the base-2 two-track {00,11} product-block
  hunt floored at k = 8, but the single-track ternary digit version closes at TWO
  channels.

## The gate bug: a float prefilter manufactured false negatives 🔬

First run gated on float h ≤ 1e-3 before the exact check; power iteration converges
slowly on graphs with many trivial cycles (true zeros read as ~0.015), so real
collapses - {1,2} included - were silently discarded.  Caught because the operator's
restricted-class thread led to a hand proof contradicting the probe.  **All positives
were always exact-checked and stand; every near-zero NEGATIVE from any probe gated at
1e-3 is suspect until re-run with a slack gate** (this file now gates at 0.05; other
hunts' floors well above noise - 0.4, 0.87 - are safe).  Instrument lesson for the
evidence-tier ledger: a cheap prefilter in front of an exact referee inherits NONE of
the referee's authority - false negatives pool at the filter's noise floor.

## Relation to the two-track wing 🧵

Single-track = Mahler's setting = the y = x diagonal of our two-track machine; the
two-track {1,2,4,5} collapse regression-passes here (diagonal is a subvariety).  What
the two-track wing adds that Mahler structurally cannot: mixed-constant disjunctions
(π and e in one clause).  What single-track adds: exhaustiveness is cheap, so
*minimality* becomes a theorem, not a search artifact.

## The decimal-digit-7 wall 🧱

Per-channel cut log2(g/(g−1)) → base 10 predicts ~22 channels single-track (naive
independent-cut estimate; base 4 collapsed at 6 vs 9.6 predicted, so correlations
help and ~mid-teens is plausible).  State cap is the binding constraint - the base-10
minimal Mahler set for digit 7 is a defined, finite computation that today's exact
checker cannot yet afford.  Named as a target, not attempted.

## ⚠️ Novelty verdict, first casualty (2026-08-29, formalization session's sweep)

**The {1,2}-per-digit theorem is Berend-Boshernitzan 1994's own M(3,1) = 2, stated
explicitly in their paper.**  The wing's ~25%-in-print calibration paid out on its
headline claim.  Reclassification: C1 = rediscovery (independent verification of
B-B by carry automata - a known-answer test the factory passed, and the hand proof
presumably re-derives theirs); {1,5} and the exhaustive minimal-set landscape =
at most a variant/completeness delta over their framework; the PRODUCT BLOCK
{2,11} (joint all-digits realization) is a different statement SHAPE and is under
subsumption check against the same paper - treat its novelty as UNKNOWN until that
verdict lands.  Nothing outward quotes this wing before that check completes.

## Honesty ledger 📋

- 🚨 **Highest folklore risk of the whole tower.**  This is Mahler's own setting with
  elementary machinery; a short hand proof of {1,5} (carry analysis of ×5 on
  {1,2}-streams) seems plausible - calibrated ~40% that an expert produces one in an
  afternoon, ~25% the exact sets are in print (Thangadurai-school descendants of
  Mahler are the place to look).  The exhaustive landscape and the edge/interior
  asymmetry are the parts most likely to be new.
- Same single-implementation caveat as the whole base-3 wing (fresh code path);
  self-tests: full-shift entropy, m=1 leaves 1 bit, two-track regression.
- ⚠️ **Negatives are METHOD-RELATIVE, not just range-limited** (operator question,
  2026-08-29): "no 2-set for digit 1" means no *automaton certificate* with m ≤ 12.
  Positive entropy means aperiodic avoiding SYMBOLIC paths survive - but the automaton
  is a carry-superset, so a surviving path need not be realizable by an actual real x.
  A true lower bound à la B-B needs an adversary CONSTRUCTION (an explicit irrational
  x with x and mx jointly avoiding digit 1 - B-B's own lower bound is exactly such an
  engineered, measure-zero construction; typical numbers, being normal, can never
  witness a lower bound).  Status: minimal-2 for edge digits = theorem; "digit 1
  needs ≥ 3" = certificate-minimality only, construction owed.  Probe idea: greedy
  digit-by-digit construction of x with x, 2x avoiding digit 1 (backtracking; if the
  TRUE constraint system has positive entropy the construction runs forever, and its
  infinite run is the counterexample candidate to formalize).
- All collapses exact (integer graph); "minimal" = no proper subset collapses (checked
  by construction: subsets enumerated first).
