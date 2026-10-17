# Vandehey Theorem 5.1 lap 9: rounded divisor proved

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovRounded` and imported it from
  `VandeheyProof.lean` without changing the frozen `VandeheyThm51` definition or any consumer
  statement.
- Defined the support-local rounded divisor from equations (12)--(13).  At each prime `p | m`
  its exponent is `floor (x * v_p(m)) + 1`; when `p = 2`, `4 | m`, and that exponent would be
  one, one additional factor of `2` is inserted.
- `roundedDivisor_spec` proves in one production endpoint, for `0 <= x < 1`, that the rounded
  integer divides `m`, has exactly the same prime support, preserves `4 | m`, and satisfies

  `m^x <= roundedDivisor m x <= 2 * primeProd P * m^x`.

  The proof first obtains the sharper upper bound with `supportProd m`, the paper's `Q`, and
  then bounds it by the frozen theorem's ambient prime product.
- The proof includes exact factorization and support lemmas, the real product identity
  `m^x = product_{p | m} p^(x * v_p(m))`, and factorwise floor bounds.  The exceptional
  correction product is proved to be at most `2`, so the paper's constant is retained.
- `ambient_primeProd_need_not_dvd` records the executable counterexample
  `¬ primeProd {2,3} ∣ 2`.  This prevents a later proof from accidentally substituting the
  ambient product for the support product inside equation (12).
- The scoped file still has exactly its single headline `sorry`; this lap advances the next
  ordered Proposition 4.1 prerequisite and does not claim completion.

## Reflection audit

- **Headline and trust boundary:** `VandeheyProof.vandeheyThm51_holds` still has the exact frozen
  type `Literature.VandeheyDiff.VandeheyThm51`.  The three corollary statements are unchanged.
  The new endpoint prints only `[Classical.choice, Quot.sound, propext]`; there is no new axiom,
  `native_decide`, heartbeat override, or hidden proof debt.
- **Source faithfulness:** the primary source defines `Q = p_1 ... p_s` after writing
  `m = product p_i^ell_i`; hence equation (12) uses the radical of the actual support, not the
  ambient set `P`.  The frozen formal statement packages constants using the ambient product.
  The module now makes this conversion explicit and proves its monotonicity, rather than
  silently conflating the two products.
- **Dependency graph:** rungs 1--4 are proved.  Within rung 5, Lemma 3.1, Lemma 4.2, Lemma 4.3,
  and equations (12)--(13) are now proved.  The live path is Claims 4.4--4.6, the remaining
  Proposition 4.1 estimates, and finally the Theorem 5.1 induction.
- **Missing abstraction exposed:** the kickoff says the inequality form of Lemma 2.1 is the only
  downstream consumer, which was true for the completed base-case path.  The paper's literal
  proofs of Claims 4.5 and 4.6 also use the exact local order-lifting data.  The existing rung-1
  LTE lemmas contain much of that arithmetic, but it is not yet packaged as an order-stability
  interface.  The next laps should build only the local equivalence needed by those claims,
  rather than cargo-culting the paper's full notation.
- No headline mismatch or false constant was found.  The support/ambient distinction is a
  formalization trap, now guarded by a theorem, not an error in the source.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovRounded.lean`: passed.
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovRounded
  NormalNumbers.VandeheyProof`: `Build completed successfully (8929 jobs)`.
- The commit hook's `taskset -c 0-5 lake build` completed successfully (10861 jobs), covering
  the repository's full build.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.roundedDivisor_spec`: axiom list
  `[Classical.choice, Quot.sound, propext]`; final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
  src/NormalNumbers/VandeheyKorobovRounded.lean`: exactly the headline `sorry` in
  `VandeheyProof.lean`.
- The focused frozen-file diff shows only the new module import in `VandeheyProof.lean`; the
  `VandeheyThm51` definition and all four frozen declarations are intact.

## Current blocker

Kickoff rung 5 now reaches Claim 4.4.  Given `tau = ord(b,m')` and
`mbar = gcd(b^tau - 1,m)`, one must prove that `ord(b,mbar) = tau` and that every divisor
`D | m` with order `tau` divides `mbar`.  Claims 4.5--4.6 then require the exact local
order-growth behavior identified in the reflection audit; the existing equation-(5)
inequality alone cannot justify their iff statements.

## Next highest-value attack

Formalize Claim 4.4 as a standalone divisibility/maximality theorem.  Use `m' | mbar`, order
monotonicity under modulus divisibility, and `mbar | b^tau - 1` to sandwich the two orders;
state maximality as `D | mbar`, which is stronger and cleaner than a numerical comparison.
Then isolate the smallest LTE/order-growth lemma that turns
`mbar*d | b^(i*tau)-1` into `d | i`.  That interface should discharge Claim 4.5 and expose
Claim 4.6 without reintroducing the paper's auxiliary `tau'`/`m_1` notation wholesale.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
