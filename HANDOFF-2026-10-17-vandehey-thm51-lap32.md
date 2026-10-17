# Vandehey Theorem 5.1 lap 32: adversarial terminal review

## Concrete advance

- Reconstructed the campaign independently from the checked-in paper text, the frozen theorem
  statement, current proof sources, recent commits, status/direction records, and the lap-31 baton.
  The route still reaches the exact headline: `vandeheyThm51_k_zero` supplies Vandehey's Lemma 2.3,
  `norm_power_sum_le_step` supplies the complete Proposition 4.1 induction step (including both
  trivial branches), and `expPair_bounds` plus `constPair_second_one_le` discharge the recursive
  side conditions.
- Rechecked Theorem 5.1 and its displayed recursions against pp. 13--14 of the local source, and
  Proposition 4.1 against pp. 8--13.  The executable pins in `VandeheyProof.lean` match the source;
  the Lean statement's exclusion of `m = 1` is the already-documented weakening, not drift.
- Confirmed that the ratified `LiteratureVandeheyDifferencing.lean` is byte-unchanged from commit
  `cba101f9`, and that the helper graph contains no proof escape or circular dependency on
  `vandeheyThm51_holds`.  The permanent axiom guards for all four kickoff declarations remain
  active, and the `BarrierAudit` waiver for the headline remains absent.
- Re-ran the exact host predicate and both authoritative gates.  No proof/source edit was needed;
  the only pre-existing working-tree item, untracked `TestVand.lean`, remains untouched.

## Verification actually run

- Shared-store preflight: `/Users/gotrevor/personal/bin/lake-base status v4.33.1` reported no
  canonical store; `/Users/gotrevor/personal/bin/relake plan --from
  /Users/gotrevor/.lake-base/v4.33.1 /Users/gotrevor/src/nn-vandehey` consequently reported that
  the source directory does not exist.  The existing repository build tree was used.
- Paper/source review: `sed` over lines 215--330, 720--810, and 930--1630 of
  `/Users/gotrevor/src/normal-numbers/tmp/joint-bc-orbits/lit-dl/vandehey/p.txt`, compared with
  `LiteratureVandeheyDifferencing.lean`, `VandeheyProof.lean`, and the final step machinery.
- Exact scoped `sorry`/`admit` scan -> zero occurrences.
- `git diff --exit-code cba101f9..HEAD --
  src/NormalNumbers/LiteratureVandeheyDifferencing.lean` -> empty.
- Scoped helper proof-escape/circularity scan over `VandeheyKorobov*.lean` -> no declared axiom,
  `native_decide`, unsafe/partial declaration, `sorry`/`admit`, import of `VandeheyProof`, or use of
  `vandeheyThm51_holds`.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target
  NormalNumbers.VandeheyProof --axioms NormalNumbers.VandeheyProof.vandeheyThm51_holds` ->
  8,936-job target build passed; axiom list `['Classical.choice', 'Quot.sound', 'propext']`; final
  verdict `FORMALIZE-TIER GREEN`.  The target build also checked the three downstream permanent
  axiom guards.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey` -> full 10,868-job
  build passed; `BarrierAudit` reports 34 barriers (26 proved, 6 cited, 2 frozen), 25 linked cruxes,
  77 waivers, and 104 unrelated open sorries; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` -> clean immediately before commit.

## Current blocker

None.  The scoped host predicate and every stronger kickoff statement-fidelity, proof-trust, and
full-build condition remain satisfied.

## Next highest-value attack

None in scope.  Call `box done`; later work requires a new operator objective.
