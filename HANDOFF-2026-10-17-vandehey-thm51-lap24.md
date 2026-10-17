# Vandehey Theorem 5.1 lap 24: adversarial completion review

## Concrete advance

- Reconstructed the campaign from the ratified theorem statement, Vandehey's paper, the current
  proof sources, recent proof commits, and the live direction/status/queue rather than relying on
  the preceding terminal-check narrative.
- Compared `Literature.VandeheyDiff.VandeheyThm51` with Lemmas 2.1--2.3, Proposition 4.1, and
  Theorem 5.1 in the source.  Its quantifiers and the `alpha`/`expPair`/`constPair` recursions still
  match, modulo the documented weakening from `<` to `≤` and exclusion of `m = 1`; the definition
  is byte-unchanged from commit `cba101f9` where it was introduced.
- Audited the route into the headline.  No `VandeheyKorobov*` module assumes
  `VandeheyThm51`, so the final induction is non-circular.  The decisive Proposition 4.1 proof
  still uses Lemma 2.1 at `mbar` to obtain `mbar ≤ M(P) * ord(b,mbar)`, while the separately proved
  Claim 4.6 retains its correct `mbar / m' ∣ M(P)` role.  The strict ceiling endpoint and actual
  modulus-support interfaces remain explicit proved lemmas.
- Re-scanned the scoped proof and all 13 machinery modules (4,985 lines) for `sorry`, `admit`,
  declared axioms, `native_decide`, unsafe/partial escape hatches, and circular use of the target;
  the scans are empty.  The BarrierAudit waiver remains absent and the four compile-time axiom
  guards remain active.
- The frozen theorem and consumer statements were not edited.  The pre-existing untracked
  `TestVand.lean` was left untouched.

## Verification actually run

- `git diff --exit-code cba101f9..HEAD --
  src/NormalNumbers/LiteratureVandeheyDifferencing.lean` -> empty.
- Debt/escape/circularity scans over `src/NormalNumbers/VandeheyProof.lean` and
  `src/NormalNumbers/VandeheyKorobov*.lean` -> no relevant matches.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target
  NormalNumbers.VandeheyProof --axioms NormalNumbers.VandeheyProof.vandeheyThm51_holds` ->
  8,936-job target build passed; axiom list
  `['Classical.choice', 'Quot.sound', 'propext']`; final verdict `FORMALIZE-TIER GREEN`.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey` -> full 10,868-job
  build passed; `BarrierAudit` reports 34 barriers (26 proved, 6 cited, 2 frozen), 25 linked
  cruxes, 77 waivers, and 104 unrelated open sorries; final verdict `FORMALIZE-TIER GREEN`.

## Current blocker

None.  The scoped host predicate and every stronger kickoff faithfulness, trust, and build
condition remain satisfied.

## Next highest-value attack

None in scope.  Call `box done`; later work requires a new operator objective.
