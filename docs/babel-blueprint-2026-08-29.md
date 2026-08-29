# The Babel blueprint - a path out of the wilderness 🗼

2026-08-29, third story of the evening.  Operator charter: *"Keep conjecturing.  Build a
blueprint.  Build a tower of Babel.  All unformalized, simply stated and conjectured, finding
a path out of the wilderness - the path must be found before a road is ever put down."*

Everything below is conjecture and architecture.  Nothing here is a work item.  Sand is
labeled sand; the few floors that already exist as mathematics are labeled BUILT because a
tower needs to say what it stands on.  Refutation probes are named because sand that cannot
collapse is not load-bearing; two were run tonight (`experiments/lntwo_hotspot_census.py`,
results inline; the second story's probes carry the other wings).

---

## The keystone: the roof is reachable in avoidance currency 🔑

The wilderness feeling of this subject comes from a currency mismatch: everything provable
about specific constants is an UPPER bound (runs capped, approaches excluded, windows
avoided), while normality seems to demand LOWER bounds (every word must keep occurring).
The keystone observation is that the mismatch is an illusion:

> **BUILT (Bailey-Misiurewicz strong hot-spot theorem; a version of it is proved in this
> repository and carried the Stoneham normality proof).**  If every binary cylinder is
> visited by the orbit at no more than a CONSTANT FACTOR above its fair share, at every
> scale, then the number is normal.  Mass conservation converts uniform upper bounds into
> the matching lower bounds, and Lebesgue is the only absolutely continuous invariant
> measure available as a limit.

So the sink itself, "ln 2 is normal in base 2", is EQUIVALENT to a statement made purely of
one-sided counting exclusions:

> **no binary word is ever over-visited by more than a constant factor.**

No occurrence axiom, no recurrence axiom, no density axiom is needed anywhere in the tower.
The entire remaining wilderness is the breadth of the exclusions: today we can exclude only
the two extreme cylinders (all-zeros, all-ones) at the extreme depth (runs); the path is to
widen exclusion technology from the ends of the interval to all of it, and from depth to
counting.  The path was under the lamppost: **turn the run machinery ninety degrees.**

Costume check, per house discipline: the FULL package of hot-spot bounds is of course
equivalent to the conclusion, as any exact characterization must be.  The content is that
the package decomposes into graded, individually-weaker, individually-refutable rungs, all
in the currency we already know how to mint, with constant-factor slack (an enormous margin
compared to asking for equidistribution directly).

## The main column: the B-ladder for ln 2 🪜

The orbit is, up to a tracking error that vanishes and cannot move visit ratios, the
explicit rational sequence `x_n = res_n / L_n` with the self-contained integer recurrence
`res_{n+1} = (2 r res_n + L_{n+1}/(n+1)) mod L_{n+1}`.  The transcendental has left the
building: the column stands on one explicit integer sequence.

- **B0 (BUILT).**  Window certificates: "the orbit visits cylinder I at time n" is one
  integer window event for `res_n`, at every cylinder, at every scale.  (Proved tonight-
  adjacent machinery; the run case is the existing lattice-window family.)
- **B1 (SAND, the whole remaining wilderness, graded by depth ℓ and word w).**
  **Conjecture B1(w, C):** the orbit visits the cylinder of w at most `C·2^{-|w|}·N` times
  up to time N, for all large N.
  **Conjecture B1-full:** one constant C works for every word simultaneously.
  Gradings that matter: per-word rungs are individually weaker; deep rungs (|w| ~ log N)
  are exactly the run/Poisson statements (the first slate's N1 and the second story's
  PairMiss are the two deepest rungs of THIS ladder, recognized after the fact); shallow
  rungs aggregate to the discrepancy ladder (first slate N4) and the frequency rung (D5).
  One ladder, everything previously built hangs on it.
- **B2 (BUILT).**  The keystone: B1-full implies equidistribution of the orbit.
- **B3 (BUILT).**  The Bailey-Crandall reduction: equidistribution implies ln 2 is
  2-normal.

**Census (tonight, N = 50 000, depths 1-12):** max visit ratios shrink with N at every
depth and sit at the Poisson-maximum envelope (depth 6: 1.24 → 1.15 → 1.07; depth 12:
5.7 → 2.7 → 2.2 against an envelope of 1.86).  No persistent hot spot anywhere in range.
The ladder holds where we can see it.

**Where the wall now lives, exactly:** proving any single B1(w, C) for a word w that is not
a pure run, at any fixed constant C, is the frontier.  The deep-rung technology (integer
certificates + coincidence exclusion) applies verbatim; what is missing is the counting
version of separation - bounding how OFTEN the explicit sequence `res_n` enters a positioned
window, rather than how deeply.  The large-prime obstruction will reappear there; it now has
one job instead of five.

**The π variant, cleaner still:** π's BBP surrogate tracks every hex digit from position 2
on (second slate, D12), so the same column for π stands entirely on an explicit rational
recursion with quadratically-decaying kicks, and the disagreement corrections are FINITE
rather than density-zero.  Every rung statement transfers with `res_n` replaced by the BBP
partial-sum numerators.

## The adder wing: carry-coupled families and at-least-one theorems 🧮

New tonight.  The pair `(ln 2, ln 3)` has a joint orbit on the torus, and every constant
`ln(2^a 3^b)` reads off that ONE orbit through an integer linear form with carries.  Digit
constraints on any family of such constants are therefore constraints on a single two-track
bit stream, and finite automata recognize them (adders, borrowers, word-avoiders).  For a
finite family F of pairs `((a,b), w)`, let S_F be the set of two-track streams satisfying
every channel's avoidance; S_F is a sofic system, its entropy is computable by a transfer
matrix, and its finiteness is decidable.

- **W1 (COMPUTATION, not conjecture).**  Hunt: compute entropy of S_F over small families;
  find the collapse frontier.  Trivial obstructions (all-zero streams, periodic points)
  force mixed word choices across channels; carries are the only coupling, which is exactly
  the missing structure theory named in Axiom C - this wing gives the carry-theory gap a
  POSITIVE target instead of a per-number axiom.
- **W2 (SAND, the wing's load-bearing beam).**  **Conjecture:** some explicit finite family
  F* has S_F* finite (only periodic streams survive).  Consequence, UNCONDITIONAL given W2,
  since log 2 / log 3 is irrational and the pair stream is aperiodic: **at least one
  constant in the explicit family {ln(2^a 3^b)} realizes its designated word infinitely
  often in binary.**  A Zudilin-flavored occurrence theorem for natural constants, reached
  by finite symbolic dynamics.
- **W3 (SAND).**  Growing families drive surviving entropy to zero: for every ε there is a
  family size beyond which at most an ε-fraction of positions can be jointly pathological
  across the family.  (The quantitative fallback if finiteness never quite happens.)
- **W4 (SAND, the descent).**  **Equivalence conjecture:** 2-disjunctivity is constant on
  the log-lattice {ln(2^a 3^b)}.  With W2: ln 2 itself is 2-disjunctive.  This is the
  wing's weakest joint and is stated so it can be attacked separately.

Refutation probe for the wing: transfer-matrix entropies for families of 2-10 channels
with adversarial word choices; a floor `h(S_F) ≥ c > 0` persisting across all small
families kills W2 in the small and demotes the wing to W3's quantitative form.

## The solenoid wing: the engineered informant 🪨

(Second story, restated as architecture.)  The base-6 digits of Stoneham's α₂,₃ read out
the 2-adic digits of powers of 3 exactly; the staircase slices are the two-exponential
family, mid-block is Mahler's `(3/2)^m` sampled along `m = (3^k - k)/2`.

- **S1 (SAND).**  **Conjecture (ShortOrbitCancel):** for each fixed frequency h, the Weyl
  sums of the block readouts cancel nontrivially along infinitely many blocks.  Probe:
  square-root-strength cancellation, blocks 5-11, every h ≤ 8.
- **S2 (SAND, weaker and sufficient).**  Every base-6 word occurs in infinitely many block
  readouts (the union over blocks is what disjunctivity needs; no per-block equidistribution
  required, and no known technique exploits the union - a genuinely open direction, not a
  graveyard).
- **S3 (roof of the wing).**  α₂,₃ is 6-disjunctive, and every advance flows both ways
  across the ×2×3 wall it shares with the sibling program.

The wing's role in the tower: it is the one place where the wall's object (`3^a mod 2^c`)
is the ENTIRE story with no transcendental residue, so any new idea about short
multiplicative orbits gets tested here first, in both directions.

## The classical attic: why the old roads stop where they stop 🏚️

For context, the strongest known depth-currency road: improving μ(ln 2) below 2.324 would
buy (Bugeaud-Kim) superlinear subword complexity; even the dream μ = 2 buys only that.
Complexity `p(ℓ)/ℓ → ∞` is the ceiling of ALL irrationality-measure roads, and it sits
far below occurrence of any single word.  Depth currency never counts visits; that is the
precise sense in which the classical road ends in wilderness, and why the column (counting
currency) and the wings (family and readout currency) are built where they are.

## The floor plan 🗺️

```
                     ln 2 normal (base 2)            ROOF
                            ▲ B3 (BUILT)
                  orbit equidistributed
                            ▲ B2 (BUILT, keystone)
        B1-full: no word over-visited (constant factor)      ← ALL the sand
          ▲ graded: B1(w,C) per word, per depth
          │   deep rungs  = N1 QuotientMiss, PairMiss (runs)
          │   mid rungs   = THE FRONTIER (counting separation)
          │   shallow     = discrepancy ladder N4, Freq D5
        B0: window certificates (BUILT)
        ground: res_n integer recurrence (BUILT)

  ADDER WING (families)                SOLENOID WING (α₂,₃)
  W2 collapse → at-least-one           S1/S2 readout visits
  occurrence (UNCONDITIONAL            → S3 α 6-disjunctive
  given a finite computation)          ↔ ×2×3 both directions
  W4 equivalence → descent to ln 2
```

**The path, walked in words:** stand on the integer recurrence; prove counting exclusions
window by window, scale by scale, with constant-factor slack, deepest scales first because
those are already runs; let mass conservation and the hot-spot keystone do all lower-bound
work for free; meanwhile the adder wing hunts a finite computation whose collapse would
yield the first unconditional occurrence theorem for a family of natural constants, and the
solenoid wing keeps the ×2×3 object honest in both directions.  Nothing on the path asks
for a lower bound; nothing on it needs new currencies; every rung can be knocked down by a
computation, and tonight's censuses knocked down none of them.
