# Vandehey Theorem 5.1 lap 36: adversarial terminal review

## Concrete advance

- Reconstructed the campaign independently from the paper, frozen statement source, current
  proof, recent source commits, status/direction/pending files, and the latest handoff.  The proof
  still follows the load-bearing route: Lemma 2.3 supplies `k = 0`,
  `VandeheyKorobov.norm_power_sum_le_step` supplies the complete Proposition 4.1 recurrence, and
  `VandeheyProof.vandeheyThm51_holds` closes the exact recursive theorem by induction.
- Rechecked Theorem 5.1 and its displayed definitions against the paper's proof.  The frozen Lean
  statement remains faithful except for its already-documented restriction `2 <= m`, which omits
  only the paper's trivial `m = 1` case and therefore weakens rather than changes the claim.
- Confirmed that `src/NormalNumbers/LiteratureVandeheyDifferencing.lean` is byte-identical to the
  ratified `cba101f9` baseline, that the scoped machinery has no proof escape or reverse dependency,
  and that the four permanent statement/trust guards remain active.  No Lean source correction was
  warranted.  The pre-existing untracked `TestVand.lean` was left untouched.

## Verification actually run

- Read the source paper's Lemmas 2.1--2.3, Proposition 4.1 and its proof, and Theorem 5.1 with its
  recursion; read the reference-corpus notes on frozen statement guards and statement faithfulness.
- `rg -n '\b(sorry|admit)\b' src/NormalNumbers/VandeheyProof.lean` -> no matches (exit 1), so the
  exact host predicate remains satisfied.
- Proof-escape scan over `VandeheyProof.lean` and `VandeheyKorobov*.lean` -> no `sorry`, `admit`,
  declared axiom, `native_decide`, `unsafe`, `partial`, or `ofReduceBool` occurrence.
- `git diff --exit-code cba101f9..HEAD --
  src/NormalNumbers/LiteratureVandeheyDifferencing.lean` -> empty; both baseline and current file
  have SHA-256 `ae7ada2603614fbc2f26a0069eca6ae5384601384d4a8f45e054ae7f583000f9`.
- Reverse-dependency scan -> no `VandeheyKorobov*.lean` import of `VandeheyProof` and no helper
  invocation of `vandeheyThm51_holds`; `BarrierAudit.lean` has no headline waiver.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target
  NormalNumbers.VandeheyProof --axioms
  NormalNumbers.VandeheyProof.vandeheyThm51_holds`: the 8,936-job scoped build completed
  successfully, including all four permanent exact-axiom guards.  Its redundant standalone axiom
  traversal was interrupted after 15:55 under the treadmill's per-process cutoff; it had emitted no
  error, and the same exact axiom condition had already been kernel-checked by the guards.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey` -> full 10,868-job build
  passed; `BarrierAudit` reports 34 barriers (26 proved, 6 cited, 2 frozen), 25 linked cruxes, 77
  waivers, and 104 unrelated open sorries; final verdict `FORMALIZE-TIER GREEN`.

## Current blocker

None.  The exact host predicate and all stronger kickoff conditions are satisfied.

## Next highest-value attack

None in scope.  Call `box done`; later work requires a new operator objective.
