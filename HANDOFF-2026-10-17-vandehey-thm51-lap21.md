# Vandehey Theorem 5.1 lap 21: reflection audit and permanent trust gate

## Concrete advance

- Audited the exact frozen proposition against Vandehey, *Differencing methods for Korobov-type
  exponential sums*, Lemmas 2.1--2.3, Proposition 4.1, and Theorem 5.1.  The Lean statement is
  faithful-or-weaker: it replaces the paper's strict bound by `≤` and excludes only `m = 1`;
  the quantifiers and the recursions for `alpha`, `expPair`, `constPair`, `primeProd`, and `bigM`
  match the displayed theorem.
- Reconstructed the proof dependency graph.  The 13 `VandeheyKorobov*` modules contain 4,985
  lines and no `sorry`, `admit`, declared axiom, or `native_decide`; they implement the order
  bound, completion/base case, differencing, divisor/counting lemmas, rounded modulus, order/gcd
  reduction, correlation aggregation, and Proposition 4.1.  `VandeheyProof` then proves the
  recursive invariants and closes Theorem 5.1 by induction.
- Checked the campaign's recurring failure modes rather than merely replaying the terminal gate.
  Review laps corrected four genuinely route-decisive details: ambient `P` versus the modulus's
  actual prime support, the direction of Claim 4.6, the strict shift endpoint in Lemma 4.3, and
  the use of the Lemma 2.1 order bound at `mbar`.  Each correction now has its own proved API;
  none survives as prose-only reasoning or hidden proof debt.
- Added four whitespace-robust `#guard_msgs` assertions to `VandeheyProof.lean`.  The kickoff's
  trust condition is now executable in every target/full build: the main theorem and all three
  unconditional consumers must continue to depend on exactly
  `[propext, Classical.choice, Quot.sound]`.  A future `sorryAx`, named axiom, or native-computation
  axiom will fail compilation instead of relying on another manual terminal audit.
- The frozen `VandeheyThm51` definition and all four theorem signatures remain unchanged.  The
  pre-existing untracked `TestVand.lean` remains untouched.

## Verification actually run

- `lake env lean src/NormalNumbers/VandeheyProof.lean` -> passed silently with all four new
  compile-time axiom guards.
- `lean-green /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof --axioms
  NormalNumbers.VandeheyProof.vandeheyThm51_holds` -> 8,936-job target build passed; axiom list
  `['Classical.choice', 'Quot.sound', 'propext']`; final verdict `FORMALIZE-TIER GREEN`.
- `lean-green /Users/gotrevor/src/nn-vandehey` -> full 10,868-job build passed; `BarrierAudit`
  reports 34 barriers, 25 linked cruxes, 77 waivers, and no stale Vandehey waiver; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff 0807f767..HEAD -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean` -> empty.
- Source scans found no `sorry`, `admit`, declared axiom, or `native_decide` in the scoped proof
  file or any `VandeheyKorobov*` module.

## Current blocker

None.  The scoped host predicate and the stronger source-faithfulness, dependency, axiom, and
full-build gates are satisfied.

## Next highest-value attack

None in scope.  Terminate the completed campaign with `box done`; a later objective requires a
new operator directive.
