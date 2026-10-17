# Vandehey Theorem 5.1 lap 27: executable statement-fidelity audit

## Concrete advance

- Performed the deep-reflection audit from the exact paper statement through the completed Lean
  dependency graph.  The proof/axiom gate was already permanent, but statement fidelity still
  relied on repeatedly diffing the ratified source file against commit `cba101f9` by hand.
- Added an executable audit surface to `VandeheyProof.lean`: definitional-equality pins for
  `primeProd`, `bigM`, `cP`, `alpha`, both equations of `expPair`, both equations of `constPair`,
  and the complete quantified type of `VandeheyThm51`.  A semantic edit to any paper-defined
  ingredient or to the theorem contract now breaks every ordinary target/full build.
- Kept the pins outside `LiteratureVandeheyDifferencing.lean`; that ratified source file remains
  byte-unchanged from its introduction.  The theorem proof, all four permanent axiom guards, and
  every frozen consumer signature are unchanged.  The pre-existing untracked `TestVand.lean`
  remains untouched.
- The reflection found no cargo-culted proof route, hidden statement mismatch, circularity, or
  missing proof abstraction.  The only cargo-culted activity was repeated manual terminal
  rechecking; the new audit surface removes its statement-fidelity blind spot.

## Verification actually run

- `lake env lean src/NormalNumbers/VandeheyProof.lean` -> passed with all new definitional pins
  and the four existing compile-time axiom guards.
- `git diff --exit-code cba101f9..HEAD --
  src/NormalNumbers/LiteratureVandeheyDifferencing.lean` -> empty.
- Scoped proof-escape and circularity scans over `VandeheyProof.lean` and all
  `VandeheyKorobov*.lean` modules -> no `sorry`, `admit`, declared axiom, `native_decide`,
  unsafe/partial declaration, import of `VandeheyProof`, or use of `vandeheyThm51_holds`.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target
  NormalNumbers.VandeheyProof --axioms NormalNumbers.VandeheyProof.vandeheyThm51_holds` ->
  8,936-job target build passed; axiom list
  `['Classical.choice', 'Quot.sound', 'propext']`; final verdict `FORMALIZE-TIER GREEN`.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey` -> full 10,868-job
  build passed; `BarrierAudit` reports 34 barriers (26 proved, 6 cited, 2 frozen), 25 linked
  cruxes, 77 waivers, and 104 unrelated open sorries; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` -> passed.

## Current blocker

None.  The scoped host predicate and every stronger kickoff proof-trust, statement-fidelity, and
full-build condition are satisfied.

## Next highest-value attack

None in scope.  Call `box done`; later work requires a new operator objective.
