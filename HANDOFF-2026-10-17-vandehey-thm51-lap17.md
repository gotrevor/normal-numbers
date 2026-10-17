# Vandehey Theorem 5.1 lap 17: three-term normalization proved

## Concrete advance

- Added the sorry-free real-algebra lemma `weighted_main_term_le`.  It rewrites the main
  correlation factor with `q = m'/mbar` and proves the uniform bound
  `m' ((N/τ)/(m/mbar)) (m/mbar)^(1+e) ≤ M N (m/m')^e` whenever `0 ≤ 1+e`.
  The same statement handles both `e = α` and `e = -δ`; this is the delicate point in
  the negative-power term.
- Proved `aggregated_rhs_le_three_terms`.  It applies that lemma to the two main terms,
  uses `m' ≤ 2QN` on the positive error term, and collects the complete aggregate from
  `norm_power_sum_sq_le_aggregated` into exactly the paper's three squared terms:
  `(2^(s+1) B C[P,δ] + 1)m'N^νL`,
  `(2AM C[P,1+α] + 2^(s+2)AQ C[P,α])(m/m')^αN^(1+γ)L`, and
  `2BM C[P,1-δ](m/m')^(-δ)N^(1+ν)L`.
- This discharges the final standalone normalization requested by lap 16.  The scoped file
  still has exactly its one headline `sorry`; this lap does not claim Proposition 4.1 or
  Theorem 5.1 complete.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovStep.lean`: passed.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.aggregated_rhs_le_three_terms`: target build
  completed successfully (8936 jobs); axiom list `[Classical.choice, Quot.sound, propext]`;
  final verdict `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `git diff 0807f767 -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean`: empty;
  the frozen statement remains unchanged.
- `rg -n '\bsorry\b|\badmit\b|^axiom '` over `VandeheyProof.lean` and the step module:
  exactly `VandeheyProof.lean`'s headline `sorry`.

## Current blocker

The algebraic normalization is proved but not yet instantiated with the natural-number
rounded modulus.  The wrapper must derive `m' ∣ mbar`, `mbar ≤ M(P)τ` (use Claim 4.4 plus
`le_bigM_mul_orderOf`), positivity, the `cP` signs, and the logarithmic factor `L ≥ 1`, then
feed `norm_power_sum_sq_le_aggregated` into `aggregated_rhs_le_three_terms`.  Afterward the
rounded lower/upper bounds must substitute the defining `x`; the two trivial branches and
the square-root step still remain before induction.

## Next highest-value attack

Prove a natural-number wrapper `norm_power_sum_sq_le_three_terms` for the nontrivial branch
`m' ≤ 2QN`, using the exact three-term conclusion already established.  Keep the conversion
from `m / mbar` as a natural quotient to the real quotient explicit (`Nat.cast_div` with the
known divisibilities).  Then specialize to `m' = roundedDivisor m x` and substitute equations
(12)--(13).

The pre-existing untracked `TestVand.lean` was inspected but left unchanged.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
