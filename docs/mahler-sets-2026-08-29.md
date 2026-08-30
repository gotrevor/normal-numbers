# Minimal Mahler sets - the single-track wing 🎯

2026-08-29, eighth story.  Probe: `experiments/mahler_minimal_sets.py` (single-track
machine: channels m·x, base 3, exhaustive over multiple sets S ⊆ {1..12}, |S| ≤ 4,
every hit exact-checked).  Operator prompt: *"we can't even prove 7 occurs i.o. in
decimal π - if we could say it for π, 2π, 3π… that would be something."*  Mahler 1973
already says that shape (some m ≤ g^(2k+1); B-B 1994: m ≤ 2g^(k+1), lower bound
g^k − 1 in their adversary-word problem).  This wing maps the EXACT landscape the
bounds only gesture at.

## Results (base 3, single digits, m ≤ 12) 📋

- **Edge digits (0 and 2): minimal size 2, meeting the B-B lower bound.**  Five
  minimal 2-sets each: {1,5}, {3,5}, {9,5}, {2,10}, {10,6} - and all five reduce to
  ONE primitive under the two equivalences (m ~ 3m, since ×3 is a ternary shift; and
  S ~ cS, substituting x → cx):

  > **For any irrational x: x or 5x contains ternary digit 0 i.o.**  (Mirror: digit 2,
  > identical list - the complement involution as a cross-check across 87 sets.)
  > Instance: **π or 5π has ternary digit 0 infinitely often.**

- **The central digit (1, the Cantor digit): minimal size 3** - no 2-set with
  m ≤ 12; ~100 minimal 3-sets, e.g. {1,2,4}:

  > **For any irrational x: x, 2x, or 4x contains ternary digit 1 i.o.**
  > Instance: **π, 2π, or 4π has ternary digit 1 infinitely often.**
  > (Improves the two-track y=x instance {1,2,4,5} of the escape-from-Cantor theorem.)

- **Structural asymmetry**: edge digits achieve the g^k − 1 lower bound; the middle
  digit strictly exceeds it (within m ≤ 12; beyond 12 open).  Conjecture shape: in
  base g, edge digits 0 and g−1 need 2 multiples, interior digits need more - the
  carry mechanism can't feed on an interior digit from one side.

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

## Honesty ledger 📋

- 🚨 **Highest folklore risk of the whole tower.**  This is Mahler's own setting with
  elementary machinery; a short hand proof of {1,5} (carry analysis of ×5 on
  {1,2}-streams) seems plausible - calibrated ~40% that an expert produces one in an
  afternoon, ~25% the exact sets are in print (Thangadurai-school descendants of
  Mahler are the place to look).  The exhaustive landscape and the edge/interior
  asymmetry are the parts most likely to be new.
- Same single-implementation caveat as the whole base-3 wing (fresh code path);
  self-tests: full-shift entropy, m=1 leaves 1 bit, two-track regression.
- Negatives are range-limited: "no 2-set for digit 1" means within m ≤ 12.
- All collapses exact (integer graph); "minimal" = no proper subset collapses (checked
  by construction: subsets enumerated first).
