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

## Folklore check, first pass (web sweep-lite, 2026-08-29 night) 🔎

The genre has a named ancestor, and it was already on our own outer-ring map:
**Mahler 1973** (*Arithmetical properties of the digits of the multiples of an irrational
number*, Bull. Austral. Math. Soc.): for irrational α and ONE chosen length-k word, some
multiple mα with `m ≤ g^(2k+1)` contains it infinitely often; **Berend-Boshernitzan 1994**
(Acta Arith. 66) improved the bound to `2g^(k+1)` and showed `g^k − 1` is a lower bound in
their problem.  Active descendants exist ("A note on Mahler's theorem II", Thangadurai et
al.).  Comparison, precisely:

- Mahler/B-B: one irrational, ONE ADVERSARY-CHOSEN word, ~g^k multiples needed (provably).
- Ours: TWO independent reals, SIX FIXED channels, per-channel different words at the
  open frontier (length 2-3), and we do not get to choose which word lands.  Neither
  statement implies the other; the g^k lower bound in their problem supports the genre's
  non-triviality.

Method sweep: nothing found coupling word-avoidance automata across linear forms via
carries with zero-entropy certificates (searches on the sofic/carry side returned only
generic symbolic dynamics).  NOT-FOUND caveats per house discipline: instruments were
WebSearch only, no MathSciNet/zbMATH; the owed full sweep = forward-citation crawl of
Berend-Boshernitzan, Waldschmidt's *Words and Transcendence* survey (arXiv:0908.4034 -
collects exactly this genre), Allouche-Shallit for carry transducers.

Verdicts (calibrated): exact statements in print ~10%; the certificate method in print
~15%; an expert finding a short HAND proof of the specific six-family (downgrading
"theorem" to "cute proposition" while the factory/universal schema keep their value)
~35%; something in the Mahler-descendant literature subsuming the two-variable universal
version ~15%.

## Can the factory reach a single constant?  NO - and the negative is sharp 🧯

(Operator question, 2026-08-29 night: "with enough of these families, can we get to
something concrete?")  Every factory theorem is a positive OR of occurrence atoms;
entailing one atom needs a singleton clause; a one-channel collapse is a single-track
avoidance system, which has positive entropy unless several words sit on ONE constant -
classical Morse-Hedlund, already known.  The ghost-channel escape (extra track pinned
by word "1" to Z = X+Y, instantiate, strip the false disjunct) buys nothing: the pinned
subsystem's entropy is at most the unpinned system's, so stripping never produces a
clause the direct factory misses.  Monotone logic is conserved; cross-constant
disjunctions are this method's ceiling.

**The meeting point, named precisely:** "w never occurs in c beyond N₀" is "the orbit
of c never visits the cylinder I_w" - rung zero of the Babel main column's hot-spot
ladder (the weakest possible visit lower bound).  The factory quarantines the pure
carry-combinatorics; what remains for a single constant is per-constant arithmetic the
stationary automaton cannot see - the surrogate's position-dependent kick (1/n is not
finite-state; non-stationarity is the exact method boundary).  Factory: "not all can
fail."  Column: "this one doesn't."  Gap: one visit to one interval.

**Concrete things the factory CAN deliver:** the named-constant disjunction theorems
and their free instances ((π, e), single-irrational multiples); the classification of
the full collapse locus (an explicit finite map of how joint digit pathology can
distribute over the log-lattice at short word lengths); minimal-family and
collapse-threshold constants; the near-miss entropy budgets.

## Honesty ledger deltas

Everything from the hunt doc still owed (kernel referee, novelty sweep - now aimed at
the universal statement, word-openness audit).  New: the neighbor and second-set
collapses used the same single implementation; the toy-family Lean dry run in the
brief covers the pipeline for all of them, but each family's certificate must be
independently re-verified at emit time (the generator's refuse-on-failure rule).
