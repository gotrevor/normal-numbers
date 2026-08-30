# The disjunction factory - a family of collapsing adder theorems 🏭

2026-08-29, fifth story.  Sequel to `docs/adder-collapse-hunt-2026-08-29.md`.  Probe:
`experiments/adder_family_enum.py` (imports the hunt's verified core; every collapse
below passed the exact integer-graph check - all still one implementation agreeing with
itself; the Lean pipeline in `BRIEF-adder-disjunction-formalization.md` remains the
definitive referee, and it is family-agnostic: swap certificate data and statement).

## The reframing first: every collapse is a UNIVERSAL theorem 🌍

Checking what the proof consumes: the certificate never uses ln 2 or ln 3 beyond the
irrationality of ONE of them.  So each collapsing family `(a_i, b_i, w_i)` proves:

> **For ANY reals X, Y not both rational: at least one w_i occurs infinitely often in
> the binary expansion of a_i·X + b_i·Y.**

`(X, Y) = (ln 2, ln 3)` is merely the naming instance.  Free instances of the base
family include `(π, e)`: at least one of {`00` in π, `001` in e, `11` in π+e, `001` in
π+2e, `010` in 2π+e, `000` in π+3e} - note the theorem does not even need π+e to be
proven irrational.  Setting `Y = c·X` gives single-constant multiple families: for any
irrational X, at least one of {`00` in X, `001` in 2X, `11` in 3X, `001` in 5X, `010`
in 4X, `000` in 7X}.  The right way to say what was found: **a Ramsey-type theorem
about binary carries - these six words cannot be simultaneously suppressed across
these six linear forms of any two reals unless both are rational.**  The natural-
constant headlines are its instances.  (This also relocates the novelty sweep:
combinatorics on words / carry automata literature, not just digits-of-constants.)

## Census of the family (all exact unless stated) 📋

- **Base family** (the brief's target): ln2/`00`, ln3/`001`, ln6/`11`, ln18/`001`,
  ln12/`010`, ln54/`000`.  47 415 live states on the tight carry ranges (the brief's
  encoding), cycles of period ≤ 2.
- **Distance-1 neighbors: 7 of 54 single-word swaps collapse exactly** - e.g. ln3's
  word can be `00` or `100` instead of `001`; ln54's can be `00`, `001`, or `100`.
  At least 8 theorems in the immediate Hamming ball; the collapse locus has volume.
- **Second channel set, EXACT COLLAPSE, 4× smaller certificate (12 347 live states):**
  ln2/`00`, ln3/`001`, ln6/`11`, ln12/`00`, ln24/`00`, ln72/`010`.
  A genuinely different theorem; also the cheapest known formalization target if the
  operator ever wants to swap the brief's family (brief currently freezes the base
  family; the pipeline is identical either way).
- **Superparticular family (borrow channels): NEAR-MISS, floor h = 0.0080** with
  greedy words on ln2, ln3, ln(3/2), ln(4/3), ln(9/8), ln6.  Not a collapse; already
  a W3-currency statement (at most a 0.8%-entropy sliver of positions can carry joint
  pathology across the musical family 🎵).  Greedy is not exhaustive - a different
  word assignment or a seventh channel may close it.

## Production axes still unexplored 🏗️

1. **Exhaustive variety mapping**: the full word-tuple search (10⁶ per channel set)
   and channel-set sweep - map the collapse locus properly instead of greedily.
2. **Borrow closure**: word search beyond greedy on the superparticular set; add
   ln(16/9) or ln(32/27) (Pythagorean ladder) as the seventh channel.
3. **Three tracks**: (ln 2, ln 3, ln 5) with channels ln(2^a 3^b 5^c) - three bits of
   entropy to kill but a quadratically richer channel lattice; conjecture: collapse
   needs FEWER channels per track as tracks grow.
4. **Other bases**: the same machine in base 3 (carry automata are base-agnostic);
   collapse there gives ternary-digit disjunctions for the same constants.
5. **Word-length ladder**: length-4 words shrink per-channel cuts but sharpen the
   per-disjunct openness; where does the collapse threshold sit as ℓ grows?

## Honesty ledger deltas

Everything from the hunt doc still owed (kernel referee, novelty sweep - now aimed at
the universal statement, word-openness audit).  New: the neighbor and second-set
collapses used the same single implementation; the toy-family Lean dry run in the
brief covers the pipeline for all of them, but each family's certificate must be
independently re-verified at emit time (the generator's refuse-on-failure rule).
