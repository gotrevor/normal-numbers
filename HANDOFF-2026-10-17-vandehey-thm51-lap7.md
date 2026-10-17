# Vandehey Theorem 5.1 lap 7: review confirms route; Lemma 4.2 proved

## Adversarial review verdict

- Reconstructed the campaign from the frozen declarations, kickoff, paper text,
  source modules, and commits since kickoff commit `0807f767`.  Against that
  baseline, `LiteratureVandeheyDifferencing.lean` is unchanged and
  `VandeheyProof.lean` differs only by the import of the new proof modules.  No
  frozen definition, theorem statement, or consumer statement has drifted.
- Rechecked the last lap's load-bearing theorem against paper equation (11).
  `norm_power_sum_range_sq_le_differencing` has the paper's `m' * N + 2 * m'`
  coefficients, shift length `N - i * tau`, and reduced numerator
  `a * (b^(i*tau) - 1)`.  The current route therefore still reaches the
  Proposition 4.1 induction step rather than a weakened surrogate.
- The next route-decisive prerequisite really was Lemma 4.2: it is used in all
  three divisor sums that produce the displayed `A'` and `B'` constants.  The
  review found no reason to change direction, so this lap proved it.
- The paper's Proposition 4.1 writes `B' = max(sqrt(...), 1)`, while the frozen
  Theorem 5.1 recursion omits the maximum.  This remains harmless for the
  eventual induction because `B_(k+1)^2 >= 2 * B_k` and `B_0 = M >= 1`, as
  already recorded in the source audit.  The induction must make this explicit;
  it is not permission to alter `constPair`.

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovDivisors` and wired
  it into `VandeheyProof.lean`.
- `sum_divisors_rpow_eq_prod` factors the real-power divisor sum into the exact
  product of finite prime-power geometric sums, using a multiplicative
  arithmetic function rather than assuming a factorization formula.
- `sum_divisors_rpow_neg_le_cP` proves the negative-power half of Vandehey's
  Lemma 4.2 for every nonzero `n` supported on the finite prime set `P`:

  `sum_(d|n) d^(-x) <= cP P x` for `x > 0`.

- `sum_divisors_rpow_le_cP_mul` proves the positive-power half:

  `sum_(d|n) d^x <= cP P x * n^x`.

  It uses the exact involution `d |-> n / d` on `n.divisors`, so no extra
  constant or support hypothesis is introduced.
- The production endpoint has exactly the standard trust-base axioms
  `[Classical.choice, Quot.sound, propext]`.  The new module has no `sorry`;
  the scoped target still has exactly the single headline `sorry` at
  `VandeheyProof.vandeheyThm51_holds`.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 ScratchVandeheyDivisors.lean`
  -- passed for both Lemma 4.2 halves in an isolated arithmetic harness (the
  scratch file was then removed).
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovDivisors`
  -- `Build completed successfully (8879 jobs)`.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
    /Users/gotrevor/src/nn-vandehey
    --target NormalNumbers.VandeheyProof
    --axioms NormalNumbers.VandeheyKorobov.sum_divisors_rpow_le_cP_mul`
  -- `Build completed successfully (8927 jobs)`; axiom list
  `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff 0807f767 -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean
    src/NormalNumbers/VandeheyProof.lean`
  -- only the proof-module import differs; the frozen declarations are intact.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
    src/NormalNumbers/VandeheyKorobovDivisors.lean`
  -- exactly the headline `sorry` in `VandeheyProof.lean`.

## Current blocker

Kickoff rung 5 still needs the rest of Proposition 4.1.  The immediate missing
input is Lemma 4.3's inclusion-exclusion estimate for
`phi_d(n,x) = #{i in [1,x) : gcd(i,n)=d}`:

`phi_d(n,x) <= (x / n) * phi(n / d) + 2^s`

when `d | n` and `n` has at most `s` distinct prime factors.  After that come
the rounded supported divisor `m'` from equations (12)--(13), Claims 4.4--4.6,
and the analytic assembly/optimization of Proposition 4.1.

## Next highest-value attack

Formalize Lemma 4.3 in a small imported iterative module.  Prefer an exact
finite inclusion-exclusion/Moebius count over a coarse cardinality argument,
because Proposition 4.1 needs the main term with `Nat.totient (n / d)` and the
error `2^P.card` separately.  Then build the equation (12) rounded divisor and
prove its support, divisibility, and two-sided equation (13) bounds before
touching the final exponent algebra.

Do not call `box done`: the host predicate
`sorry-free:src/NormalNumbers/VandeheyProof.lean` is not met.
