# The restricted-class ladder 🪜 - dodging B-B by shrinking the quantifier

2026-08-29, ninth story (operator direction: *"we could hope to do better than B-B
bounds if we restrict to specific types of irrationals"*).  No probe yet - this doc
forges the conjectures and names the mining target.

## The principle

Lower bounds in this genre (B-B's g^k − 1, our blocking pairs) are paid ONLY by
engineered, measure-zero adversaries - Liouville-flavored, digit-sparse, complexity-
poor.  Restrict the quantifier to a class excluding them and the bounds evaporate.
The catch: the class membership must be something a proof can consume.  The classical
bridge is **digit-stream complexity**: Adamczewski-Bugeaud (via the subspace theorem)
prove every algebraic irrational's base-g expansion has superlinear word complexity;
that is what powers Adamczewski-Rampersad's SINGLETON 00/11 results in base 2 -
algebraicity buys at word length 2 what all-irrationals methods provably cannot
(our universality no-go + B-B's constructions).

## The interpolation conjecture (the story's flagship) 💎

Ternary digit 1, the Cantor digit, has a named ladder with an empty middle rung:

- **Bottom (theorem, tonight)**: for ANY irrational x, one of x, 2x, 4x has ternary
  digit 1 i.o.  ({1,2,4} minimal in-method; `mahler_minimal_sets.py`.)
- **Top (Mahler's open Cantor problem, ~40 years)**: no algebraic irrational lies in
  the middle-thirds Cantor set - i.e. the SINGLETON: every algebraic irrational has
  ternary digit 1 i.o.
- **Middle (FORGED HERE, open, plausibly attackable)**:

  > **For every algebraic irrational x: x or 2x contains ternary digit 1 i.o.**

  Strictly weaker than Mahler's problem, strictly stronger than the unconditional
  theorem; the 2-set adversary would have to be algebraic, where subspace-theorem
  tools bite.  Probes that could kill it: none known (a counterexample would be an
  algebraic x with x AND 2x in Cantor-like sets - would itself be spectacular).

## The new certificate currency: complexity-graded collapse 🎚️

Today's machine distinguishes only h = 0 + simple cycles (kills all aperiodic
streams) from everything else.  Refine the everything-else:

- **h = 0, survivors all eventually-periodic** → unconditional theorem (current).
- **h = 0, aperiodic survivors of POLYNOMIAL complexity** (Sturmian-like) → theorem
  for every x whose expansion has superlinear complexity - by A-B, ALL algebraic
  irrationals.  Smaller families than any unconditional theorem can afford.
- **h > 0** → exponential survivors, no restricted conclusion (blocking pairs live
  here).

**The discard pile is the mine**: every family the night's hunts rejected as "float
zero but exact check FAILED" sits in the middle stratum candidate zone.  Probe
design: re-run the hunts logging failed-exact zero-entropy families; for each,
count length-n paths in the surviving graph (integer matrix powers) and classify
growth polynomial vs exponential; polynomial hits are algebraic-restricted theorem
candidates, with the survivor structure itself (which Sturmian?) as the proof
skeleton.

## Honesty rails ⚖️

- This ladder serves ALGEBRAIC instances (√2, φ, ...).  It does NOT reach ln 2/ln 3:
  no complexity lower bound is known for any log's expansion - the named-constant
  lattice stays with the B-ladder's non-finite-state 1/n kick.  Do not let the wing's
  instances drift back to logs in write-ups.
- A-B/A-R attributions from memory (~85%); verify statements in the novelty sweep
  before leaning an outward claim on them.  Mahler's Cantor problem being open:
  high confidence, same sweep.
- The middle-rung conjecture is forged, not evidenced: no probe supports it beyond
  the structural analogy; its value is position (between a theorem and a famous
  problem), which is exactly what makes it a good conjecture-graph node.
