# Vandehey Theorem 5.1 lap 5: completion and `k = 0` proved

## Concrete advance

- Added `NormalNumbers.VandeheyKorobovCompletion`, completing kickoff rung 3.
  Its public endpoint
  `NormalNumbers.VandeheyKorobov.norm_power_sum_Icc_le_sqrt_mul_log`
  proves the repaired coprime (`d = 1`) case of Vandehey Lemma 2.2 in the
  repository's actual `ePhase` notation:

  `‖∑ n ∈ Icc 1 N, ePhase (a * b^n / m)‖ ≤ √m * (1 + log m)`

  whenever `N ≤ ord(b,m)`.
- Proved the sharp coefficient-mass estimate required for the frozen constants:

  `(1 / τ) * ∑ h, ‖∑ j < N, e(hj/τ)‖ ≤ 1 + log τ`.

  The proof treats odd and even `τ` separately, pairs the centered frequencies,
  and proves the exact harmonic estimates
  `H_n ≤ log(2n+1)` and `H_{n-1} + 1/(2n) ≤ log(2n)` from
  `Real.sum_range_le_log_div`.  There is no extra additive constant.
- Proved finite Fourier inversion for an initial interval on `ZMod τ`, then
  combined it termwise with lap 4's
  `norm_completed_power_sum_le_sqrt`.  The intermediate theorem
  `norm_power_sum_Icc_le_sqrt_mul_log_order` retains the sharper
  `1 + log(ord(b,m))` factor.
- Strengthened rung 1 to its exact multiplicative form
  `le_bigM_mul_orderOf : m ≤ M(P) * ord(b,m)`.  The previously published
  quotient theorem `div_bigM_le_orderOf` remains available as a corollary.
  This avoids the rounding loss that natural-number division would introduce
  in Lemma 2.3.
- Completed kickoff rung 4.  The theorem
  `norm_power_sum_Icc_le_k_zero` splits an arbitrary interval into full order
  periods plus one remainder and proves

  `(√m + M(P) m^(-1/2) N) * (1 + log m)`.

  `vandeheyThm51_k_zero` then checks this against the frozen `constPair`,
  `alpha`, and `expPair` expression exactly; no restatement is being proved.
- `VandeheyProof.lean` now imports the completion module.  No frozen definition
  or corollary statement changed.

## Review and fidelity audit

- Re-read the paper statement and proof route for Lemmas 2.1--2.3 and the
  frozen `VandeheyThm51`.  The base case has the paper's two terms and the
  logarithmic exponent simplifies to one exactly.
- The finite completion is on the actual cyclic exponent group, not a dense
  surrogate.  The index shift from `n = 1` is absorbed by replacing the unit
  frequency `a` with `a*b` in each completed twist.
- The period decomposition uses `m ≤ M(P) * ord(b,m)`, which is what the lap-3
  LTE proof already established internally.  Merely using
  `m / M(P) ≤ ord(b,m)` would be too weak because of floor rounding.
- `src/NormalNumbers/VandeheyKorobovCompletion.lean` contains no `sorry`.
  The only `sorry` on this campaign remains the headline
  `VandeheyProof.vandeheyThm51_holds`; kickoff rungs 5 and 6 remain.

## Verification actually run

- `taskset -c 0-3 lake env lean -j 1 src/NormalNumbers/VandeheyKorobov.lean`
  -- passed.
- `taskset -c 0-3 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovCompletion.lean`
  -- passed, warning-free.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green \
    /Users/gotrevor/src/nn-vandehey \
    --target NormalNumbers.VandeheyProof \
    --axioms NormalNumbers.VandeheyKorobov.vandeheyThm51_k_zero`
  -- `Build completed successfully (8925 jobs)`; the exact frozen base case's
  axiom list was `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.

## Current blocker

Kickoff rung 5, Proposition 4.1, is now the route-decisive crux.  The paper's
proof first needs its Lemma 3.1 differencing inequality (paper equation (11)):
for a chosen divisor `m' | m`, with `τ = ord(b,m')`, square the original sum,
average shifts by multiples of `τ`, and bound it by the shifted sums with phase
coefficient `a * (b^(i*τ) - 1) / m`.

The proposition then needs three supporting packages, in this order:

1. elementary divisor-sum bounds corresponding to Lemmas 4.2 and 4.3;
2. construction of the rounded divisor `m'` with the paper's lower/upper
   bounds (12)--(13) and its `4 | m` correction;
3. the gcd/order claims 4.4--4.6 that identify the reduced modulus of every
   shifted phase and show `m / gcd(b^τ-1,m) | M(P)`.

Only after these are kernel-checked should the long exponent-and-constant
optimization be assembled.

## Next highest-value attack

State and prove the standalone Lemma 3.1 differencing inequality in a new
`VandeheyKorobovDifferencing.lean` module.  Keep it abstract over a complex
sequence/phase where practical, but instantiate it immediately to the power
sum so that the exact factor `m' * N + 2*m' * ...` in equation (11) is checked
before formalizing the rounded modulus construction.

Do not call `box done`: the host predicate
`sorry-free:src/NormalNumbers/VandeheyProof.lean` is not met.
