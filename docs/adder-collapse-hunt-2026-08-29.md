# The adder collapse hunt - W1 executed, and it HIT 🧮💥

2026-08-29, night, fourth story.  Babel adder wing (`docs/babel-blueprint-2026-08-29.md`),
W1 computation.  Probe: `experiments/adder_collapse_hunt.py` (self-testing; exact
integer-graph verification, no float in the final claim).

## The sharpened criterion (found while building the automaton)

The blueprint's W2 asked for a FINITE system.  The bar is lower: **zero entropy
suffices.**  In a zero-entropy sofic system every strongly connected component of the
live automaton is a simple cycle with uniquely-labeled edges, so every infinite
consistent stream is eventually periodic.  An eventually periodic pair stream makes the
represented number rational.  So h(S_F) = 0 plus the irrationality of ln 2 ALONE already
forces: at least one channel's word occurs infinitely often.

## Lesson one: the vacuous collapse (the hunt teaches its own rules)

Unrestricted, the greedy immediately "collapses" by choosing the word `01`: avoiding 01
kills a track to `1^a 0^∞` all by itself, and the at-least-one conclusion is witnessed
by "01 occurs i.o.", which Adamczewski-Rampersad already give for every irrational.
The hunt rediscovered the known-recurring-words boundary (0, 1, 01, 10) mechanically.
Rule: channels may carry only OPEN words - `00`, `11`, and the eight length-3 words.

## The hit: six channels, all words open, entropy exactly zero

Greedy decay over open words (channel order by coefficient size, word chosen per channel):

| k | constant | word | h(S_F) | states |
|---|---|---|---|---|
| 1 | ln 2  | `00`  | 1.6942 | 4 |
| 2 | ln 3  | `001` | 1.3885 | 24 |
| 3 | ln 6  | `11`  | 1.0000 | 144 |
| 4 | ln 18 | `001` | 0.5755 | 1 728 |
| 5 | ln 12 | `010` | 0.0212 | 20 736 |
| 6 | ln 54 | `000` | **0** | 311 040 |

**Exact verification (integer graph, no floats):** after pruning, 125 688 live states;
every strongly connected component is a simple cycle with single-labeled edges;
16 surviving cycles, periods 1 and 2 only (the hand-checkable survivor
`x = y = (10)^∞`, i.e. X = Y = 2/3, is among them, and satisfies all six constraints).
Drop-one minimality: every 5-channel subfamily has h > 0 (0.02-0.89), so all six
channels carry load (other 5-families might collapse with different words; minimality
of SIX is not claimed).

## CANDIDATE THEOREM (sand until the owed list clears) 🏛️

> At least one of the following holds:
> - `00` occurs infinitely often in the binary expansion of ln 2;
> - `001` occurs infinitely often in the binary expansion of ln 3;
> - `11` occurs infinitely often in the binary expansion of ln 6;
> - `001` occurs infinitely often in the binary expansion of ln 18;
> - `010` occurs infinitely often in the binary expansion of ln 12;
> - `000` occurs infinitely often in the binary expansion of ln 54.

Every disjunct is individually open (the per-constant frontier sits exactly at `00`/`11`
per Adamczewski-Rampersad, and no specific length-3 block is known for any specific
natural constant).  No single constant carries two constraints, so no Morse-Hedlund
single-sequence argument applies; the force lives entirely in the carry coupling of the
six linear forms over one (ln 2, ln 3) pair stream.  The proof shape is: finite
automaton + simple-cycle structure + irrationality of ln 2.  A Zudilin-style
at-least-one occurrence statement for natural constants, from a finite computation.

**Why this matters for the tower:** it is the first output anywhere in the program in
OCCURRENCE currency - the currency the keystone said we would never need for normality,
but which the wilderness has lacked entirely for specific constants.  If it survives
verification, the wing's W3/W4 stories (entropy floors as quantitative pathology
budgets; equivalence/descent toward a single constant) inherit a working engine.

## Honesty ledger (all owed before any outward whisper) 📋

1. **Independent reimplementation** - different author, different state encoding,
   ideally a different language; the present check is one program agreeing with itself
   (its self-tests: exact golden-mean entropy, exact independence additivity, the
   predicted vacuous collapse, and the hand-verified survivor cycle).
2. **Proof write-up** - the compactness/backward-path argument (true carries are
   bounded by a+b; the reversed walk traps in one SCC; single-labeled simple cycles
   force periodicity; periodic tail contradicts irrationality of ln 2), stated so a
   human can referee it against the printed graph facts.
3. **Novelty sweep** - carry-coupled simultaneous word constraints across
   multiplicatively related constants; nearest literatures: combinatorics on words
   (Adamczewski-Rampersad), sumset/carry automata, Zudilin-style disjunctions.  Nothing
   recalled, nothing swept yet.
4. **Word-openness audit** - re-verify against the literature that each specific
   disjunct is indeed open (in particular `001`/`010`/`000` for these constants).
5. Hunt hygiene for extensions: negative coefficients (borrow automata) unlock
   ln(3/2), ln(4/3), ln(9/8); length-4 words; 5-channel exhaustive search.
