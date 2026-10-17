# Vandehey Theorem 5.1 lap 34: reflection closes the remaining semantic audit gap

## Concrete advance

- Re-read the treadmill/reflection policies, kickoff, campaign ledgers, paper text, frozen
  statement, completed proof route, and recent terminal laps.  The mathematical architecture is
  still sound: `vandeheyThm51_k_zero` supplies Lemma 2.3, `norm_power_sum_le_step` supplies the
  complete Proposition 4.1 step, and `expPair_bounds` plus `constPair_second_one_le` discharge the
  induction invariants.  The recurring campaign corrections (ambient versus supported primes,
  Claim 4.6's direction, the strict correlation endpoint, and the order bound at `mbar`) remain
  isolated in proved interfaces.
- Found one genuine blind spot in the lap-27 executable statement audit.  The full theorem-type
  pin mentioned the repo-owned symbol `ePhase` on both sides, so changing that definition's
  normalization would leave every existing type and axiom guard green while changing the paper's
  additive character.  Added a definitional pin
  `ePhase x = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))`.
- Added executable contract witnesses for all three frozen unconditional consumers.  Their exact
  intended conclusions and hypotheses are now re-elaborated in every target/full build, beside
  the existing theorem-type and recursion pins and the four permanent axiom guards.
- The ratified `LiteratureVandeheyDifferencing.lean` file, `VandeheyThm51`, the four theorem
  signatures, and every proof body remain unchanged.  The pre-existing untracked `TestVand.lean`
  was left untouched.

## Verification actually run

- Reference-corpus review: `axiom-clean-not-statement-faithful.md`,
  `guard-ratified-statements-by-name.md`, and `freeze-the-contract-not-the-route.md`; these identify
  repo-owned definition drift as a gap not covered by `#print axioms`.
- Paper/source review: Theorem 5.1 and its recursion (pp. 13--14), Proposition 4.1 (pp. 8--13),
  Lemmas 2.1--2.3, and the definition of `N_P` were compared with the frozen Lean contract and
  completed route.  The only deliberate weakening remains exclusion of `m = 1`.
- Shared-store preflight: `/Users/gotrevor/personal/bin/lake-base status v4.33.1` reported no
  canonical store; `relake plan --from /Users/gotrevor/.lake-base/v4.33.1` reported that source
  directory absent, so the repository's existing build tree was used.
- `git diff --exit-code cba101f9..HEAD --
  src/NormalNumbers/LiteratureVandeheyDifferencing.lean` -> empty before the audit-only edit; that
  edit touches only `VandeheyProof.lean`.
- Scoped exact proof-escape scan over `VandeheyProof.lean` and `VandeheyKorobov*.lean` -> no
  `sorry`, `admit`, declared axiom, `native_decide`, unsafe declaration, or partial declaration.
  Reverse-dependency scan -> no helper import of `VandeheyProof` and no helper invocation of
  `vandeheyThm51_holds`.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target
  NormalNumbers.VandeheyProof --axioms NormalNumbers.VandeheyProof.vandeheyThm51_holds` ->
  8,936-job target build passed; axiom list exactly `['Classical.choice', 'Quot.sound',
  'propext']`; final verdict `FORMALIZE-TIER GREEN`.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey` -> full 10,868-job
  build passed; `BarrierAudit` reports 34 barriers (26 proved, 6 cited, 2 frozen), 25 linked
  cruxes, 77 waivers, and 104 unrelated open sorries; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check` -> clean.

## Current blocker

None.  The exact host predicate and every stronger kickoff condition remain satisfied, and the
paper semantics now have a narrower executable drift surface than at lap 33.

## Next highest-value attack

None in scope.  Call `box done`; later work requires a new operator objective.
