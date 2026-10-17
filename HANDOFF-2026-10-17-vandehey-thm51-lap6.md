# Vandehey Theorem 5.1 lap 6: differencing lemma proved

## Concrete advance

- Added `NormalNumbers.VandeheyKorobovDifferencing`, completing the first and
  route-decisive component of kickoff rung 5: Vandehey's Lemma 3.1.
- The public endpoint
  `NormalNumbers.VandeheyKorobov.norm_power_sum_range_sq_le_differencing`
  proves paper equation (11), in the repository's actual finite-Fourier
  `phase` notation, with exactly

  `m' * N + 2 * m' * sum_{1 <= k < N} |sum_{j < N-k*tau}
    e(a * (b^(k*tau)-1) * b^(j+1) / m)|`,

  where `tau = orderOf (b : ZMod m')`.  The range index `j` is the paper's
  `n-1`; hence the inner length and coefficient are literal equation (11), not
  a relaxed surrogate.
- Proved the reusable abstract inequality
  `norm_sum_range_sq_le_differencing` for every unimodular complex sequence
  and every positive period `T <= q`.
- Formalized the two bookkeeping identities on which it rests:
  `sum_upper_modEq_eq_sum_shifts` gives a genuine bijection from upper pairs
  agreeing modulo `T` to positive shifts `k*T`, and
  `sum_range_square_symmetric` splits the correlation square into its diagonal
  plus twice its upper triangle.
- Proved the aliased finite Parseval identity `sum_norm_sq_twisted_eq` by
  additive-character orthogonality.  This mirrors Vandehey's proof: the
  untwisted coefficient is one nonnegative term of the total Fourier mass,
  and orthogonality retains precisely the pairs in the same exponent class.
- `VandeheyProof.lean` now imports the differencing module.  No frozen
  definition or corollary statement changed.

## Fidelity details

- No divisibility assumption `m' | m` was added to Lemma 3.1: as in the paper,
  the lemma itself only needs `gcd(b,m') = 1`; divisibility is used later when
  Proposition 4.1 chooses `m'`.
- The factor in front is `m'`, not `tau`; the abstract proof first obtains the
  sharper period factor and spends `tau <= m'`, exactly validating the paper's
  constant.
- The apparent sign reversal in the raw correlation is removed by complex
  conjugation, whose norm is unchanged.  The resulting displayed coefficient
  is exactly `a * (b^(k*tau) - 1)`.
- `src/NormalNumbers/VandeheyKorobovDifferencing.lean` contains no `sorry`.
  The campaign still has exactly the headline `sorry` in
  `VandeheyProof.vandeheyThm51_holds`.

## Verification actually run

- `taskset -c 0-3 lake env lean -j 1
    src/NormalNumbers/VandeheyKorobovDifferencing.lean`
  -- passed.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
    /Users/gotrevor/src/nn-vandehey
    --target NormalNumbers.VandeheyProof
    --axioms NormalNumbers.VandeheyKorobov.norm_power_sum_range_sq_le_differencing`
  -- `Build completed successfully (8926 jobs)`; the theorem's axiom list was
  `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.

## Current blocker

The remainder of kickoff rung 5 is Proposition 4.1.  With equation (11) now
kernel-checked, the next missing inputs are the paper's elementary Lemmas 4.2
and 4.3, followed by the rounded divisor construction (12)--(13) and the
gcd/order claims 4.4--4.6.  Only then should the exponent/constant optimization
be assembled.

## Next highest-value attack

Formalize Lemma 4.2 in the differencing module (or a small imported arithmetic
module): for a modulus supported on the finite prime set `P`, prove the positive
and negative divisor-power sums bounded by
`C(P,alpha) * n^alpha` and `C(P,alpha)`.  Then prove Lemma 4.3's
inclusion-exclusion bound for the number of `i < x` with `gcd(i,n)=d`.

Do not call `box done`: the host predicate
`sorry-free:src/NormalNumbers/VandeheyProof.lean` is not met.
