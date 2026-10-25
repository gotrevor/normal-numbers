# HANDOFF: EB endpoint Step 2, EK laps 1--7 (COMPLETE)

Branch `research/eb-endpoint` is local only.  Never push it.  The scoped host predicate is
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean`.  Do not change any existing
statement in that file, and keep `ErdosKacFiniteDim` as the named hypothesis exactly as planted.

## Concrete advance

### Lap 7: Step 2 and both headlines closed

The scoped objective is complete: `CoefmassErdosBorweinEndpointEK.lean` is sorry-free, with every
pre-existing statement unchanged.  The last theorem `divisorVariance_diverges_at_ln2` is proved
from the named hypothesis `ErdosKacFiniteDim`; no proof or axiom for that hypothesis was added.

The final probability layer consists of:

- `gaussianReal_abs_tail_le` and `gaussianProduct_sum_abs_tail_le`, elementary Chebyshev bounds
  using the exact Gaussian mean and variance and independence of product coordinates;
- `brownianFDD_first_ge_le` and `brownianFDD_last_ge_le`, identifying the first equal-grid
  Brownian coordinate with one increment and the terminal coordinate with their sum;
- `equalTimeGrid_control_bounds`, the explicit choice `R = q^8`, `delta = q^-2`, which bounds the
  ballot rectangle by `4/q` and the first-coordinate failure by `1/q`.

For the final FDEK assembly, the bounded-mass event is included in the union of three closed
events: the constant upper rectangle, first-coordinate failure, and terminal-coordinate failure.
Outside the two control failures, `normalized_omegaUpTo_cutoff_le` supplies every later grid
coordinate.  The proof then handles the fixed shift via `card_filter_Icc_add_le` and the denominator
change with `(N+a0)/N <= 2` eventually.  This closes `divisorVariance_diverges_at_ln2`, and therefore
the already-assembled `ebRandom_ae_normal_le_ln2_of_EK` and `ebPowerCandidateNormal_of_EK` are now
sorry-free and axiom-clean.

### Lap 6: local soft Gaussian ballot layer

The source-located Gaussian ballot dependency is now ported locally and connected to the exact
equal-grid event used by the endpoint proof.  No planted statement was changed.

- New module `CoefmassErdosBorweinEndpointEKAux.lean` contains the self-contained kernel proof
  through `gaussianWalk_survival_probability_le_fourthRoot`: the Gaussian barrier potential,
  killed-walk recursion, terminal-law calculation, and optimized near/far split.  It imports only
  Mathlib; the read-only sibling repository is not a dependency.
- `gaussianWalk_fixedVariance_survival_probability_le_fourthRoot` rescales iid centered Gaussian
  increments of every nonzero variance to the standard walk.
- `gaussianWalkSurvives_iff_prefix_sums` identifies recursive survival with the simultaneous
  prefix-sum inequalities.
- In the endpoint module, `gaussianPartialSumUpperSet_eq_survivalSet` connects that event to the
  existing Brownian adapter, and `brownianFDD_upperRectangle_equalTimeGrid_le` proves the explicit
  equal-grid rectangle estimate

  ```text
  brownianFDD(R, equal grid){all coordinates ≤ δ}
    ≤ 2 * sqrt(δ / sqrt(1/R) + 2) / sqrt(sqrt R).
  ```

This discharges the main source-port risk identified in lap 5.  The remaining probability work is
the two Gaussian control-coordinate tails and the finite-grid/FDEK union bookkeeping.

### Lap 5: adversarial route correction and equal-grid Gaussian adapter

The review reconstructed the remaining route from the frozen statement and found a genuine gap in
the lap-4 plan: the hard-coded terminal condition
`((ω-L)/√L) ≤ 1` leaves a fixed Brownian tail of about `P(B₁ > 1)`.  That exceptional set cannot
be made arbitrarily small, so it cannot prove density convergence to zero.

The deterministic interface is now corrected without changing or deleting the old helper.

- `omegaUpTo_le_two_mul_of_normalized_terminal_le` accepts any fixed terminal threshold `A`, once
  `A ≤ √L`; `eventually_const_le_sqrt` supplies that comparison.  The terminal Brownian tail can
  therefore be sent to zero by choosing `A` large.
- `eventually_collisionCutoff_le_exp_log_rpow_add` closes the missing cutoff comparison for every
  fixed positive time `s`, directly in the shifted form needed later:

  ```text
  collisionCutoff N ≤ exp((log(N+a))^s) eventually.
  ```

  Its proof uses `log(x)^2 = o(x^s)` at `x = log N` and the monotonicity under `N ≤ N+a`.

The probability route was also replaced by a source-backed equal-grid route.

- `equalTimeGrid`, `strictMono_equalTimeGrid`, `equalTimeGrid_last`, and
  `equalTimeGrid_increment` give the admissible FDEK grid `j/R`, with every increment variance
  exactly `1/R`.
- `gaussianPartialSumUpperSet` is the iid-increment event that all partial sums stay below a
  constant barrier.
- `brownianFDD_upperRectangle_equalTimeGrid` proves from the actual `brownianFDD` definition that
  its constant upper rectangle on this grid is exactly the product-Gaussian partial-sum event.

The read-only sibling development
`/Users/gotrevor/src/lean-proofs/src/latest/ErdosProblems/Erdos520/` contains a kernel-checked,
self-contained soft Gaussian ballot proof.  In particular,
`HarperGaussianWalk.gaussianWalk_survival_probability_le_fourthRoot` and its fixed-variance
rescaling are directly adaptable to `gaussianPartialSumUpperSet`; no new probability hypothesis is
needed.  This is a much firmer route than the previously proposed geometric Gaussian recursion.

For the final parameter choice, take an equal grid of size `R`, early threshold
`δ = R^(-1/4)`, and an independent large terminal-control threshold `A`.  Then:

- the soft fixed-variance ballot bound is `O(R^(-1/8))`;
- the first-coordinate failure has Chebyshev bound
  `(1/R)/δ² = R^(-1/2)`;
- the terminal-control failure is at most `A^(-2)`.

Choose `A`, then `R`, then the FDEK portmanteau error.  On the complement of the two control
failures, `normalized_omegaUpTo_cutoff_le` puts every equal-grid coordinate in the `δ` upper
rectangle.

### Lap 4: deterministic FDEK rectangle layer

The pointwise implication from bounded divisor mass to the coordinatewise FDEK upper rectangle is
now formalized.  No planted statement was changed.

- `upperRectangle` and `isClosed_upperRectangle` provide the closed set required by the
  portmanteau hypothesis.
- `log_log_exp_log_rpow`, `exp_log_rpow_mono`, and `exp_log_rpow_one` identify the exact FDEK
  centering, order its cutoffs, and identify the terminal cutoff with the sample size.
- `card_filter_Icc_add_le` handles the fixed shift `n ↦ n+a₀`: the shifted filtered interval
  injects into the unshifted interval ending at `N+a₀`.
- `omegaUpTo_le_two_mul_of_normalized_terminal_le_one` converts the terminal FDEK good-coordinate
  bound into the `ω ≤ 2L` input of the walk cap.
- `normalized_omegaUpTo_cutoff_le` combines the lap-3 cutoff alternative with the early-coordinate
  and terminal-coordinate controls.  At each later grid coordinate, bounded divisor mass implies
  the normalized count is at most `δ`: the no-jump branch gains `-(t-s)√L`, while the jump branch
  uses the endpoint chain cap.
- `eventually_walk_cap_le_sqrt` and `eventually_early_gap_le` prove the two scalar eventual bounds
  required by that implication.

Thus the deterministic heart of the simultaneous rectangle inclusion has been reduced to routine
finite-grid bookkeeping plus the still-needed eventual comparison
`collisionCutoff N ≤ exp ((log (N+a₀))^s)`.

### Lap 3: finite cutoffs inherit the prime-jump cap

The bridge requested at the end of lap 2 is proved, again without changing any planted statement.

- `omegaUpTo_eq_of_greatest_primeFactor` identifies the cutoff count with the count at its greatest
  prime factor.
- `omegaUpTo_primeJump_or_eq_early` makes the decisive split for `P ≤ x ≤ y`: if a prime factor
  of `n` lies in `(P,y]`, it selects the largest one and proves that `omegaUpTo y n` is attained at
  that jump; otherwise it proves the exact equality `omegaUpTo y n = omegaUpTo x n`.
- `omegaUpTo_cutoff_eq_early_or_sub_log_log_le` combines that split with the lap-2 cap.  On
  `divisorVarianceMass v P n ≤ T` and `omegaUpTo y n ≤ 2L`, either the count is unchanged from
  the early cutoff or

  ```text
  omegaUpTo y n - log (log y)
    ≤ 1 + log (2*L) + log (T/c) / log 2.
  ```

Thus the remaining deterministic work no longer needs to reason about the location of the last
prime factor at every FDEK coordinate.

### Lap 2: endpoint walk cap

The load-bearing pointwise walk cap is proved, with no change to any planted statement.

- `walk_cap_analytic` rigorously takes logarithms in the chain inequality and proves

  ```text
  k - log x ≤ 1 + log k + log(T/c) / log 2.
  ```

  Its proof also derives `0 < T` from the positive chain lower bound, so no extra positivity
  assumption on the threshold was introduced.
- `omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le` supplies `k ≥ 1` from the terminal prime
  and specializes the scalar inequality to a prime jump `p | n` above the divisor cutoff.
- `omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le_of_le` combines this with
  `omegaUpTo p n ≤ 2L`, giving the exact uniform form needed on an FDEK good set:

  ```text
  omegaUpTo p n - log (log p)
    ≤ 1 + log (2*L) + log(T/c) / log 2.
  ```

All three new theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

### Lap 1: chain and assembly

Two of the three planted proof debts are closed.

- `ebRandom_ae_normal_le_ln2_of_EK` applies
  `ebRandom_ae_normal_of_divisorVariance_diverges` with variance
  `delta m * (1 - delta m)`; nonnegativity comes directly from `BernoulliLawNat`.
- `exists_powerDelta_variance_lower` proves a uniform positive endpoint constant for every
  `0 < a ≤ log 2`, including the exceptional value `m = 2`.  This closes
  `ebPowerCandidateNormal_of_EK` without changing its statement.

The load-bearing deterministic part of Step 2 is formalized too.

- `primeFactorsUpTo` and `primeChainDivisors` define the prime chain.
- `primeProducts_injOn` proves unique subset products by recovering each subset with
  `Nat.primeFactors`.
- `card_primeChainDivisors` proves the exact cardinality `2^(t-1)`.
- `mem_primeChainDivisors_bounds` proves every chain member divides `n` and lies in `[p,p^t]`.
- `divisorVarianceMass_ge_primeChain_endpoint` sums the endpoint lower bound and proves the exact
  paper inequality

  ```text
  2^(t-1) * (c * (t * log p)^(-log 2)) ≤ divisorVarianceMass v P n,
      t = omegaUpTo p n.
  ```

All pre-existing statements in `CoefmassErdosBorweinEndpointEK.lean` remain unchanged.

## Verification

Narrow elaboration:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean
```

Exit 0.  Its sole proof-debt warning is now `divisorVariance_diverges_at_ln2`.

Lap-2 narrow elaboration reran the same command after adding the walk-cap lemmas, again exit 0 with
the same sole scoped proof debt.

Repository gate and audits:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.divisorVarianceMass_ge_primeChain_endpoint \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.exists_powerDelta_variance_lower
```

Verdict: `FORMALIZE-TIER GREEN`.  Both audited helpers use only `propext`, `Classical.choice`, and
`Quot.sound`.

Lap-2 gate:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.walk_cap_analytic \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le_of_le
```

Verdict: `FORMALIZE-TIER GREEN`; all three audited walk-cap theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

Lap-3 narrow elaboration:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean
```

Exit 0.  The sole scoped proof-debt warning remains `divisorVariance_diverges_at_ln2`.

Lap-3 repository gate and audits:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_eq_of_greatest_primeFactor \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_primeJump_or_eq_early \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_cutoff_eq_early_or_sub_log_log_le
```

Verdict: `FORMALIZE-TIER GREEN`; all three finite-cutoff helpers use only `propext`,
`Classical.choice`, and `Quot.sound`.

Lap-4 narrow elaboration:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean
```

Exit 0.  The sole scoped proof-debt warning remains `divisorVariance_diverges_at_ln2`.

Lap-4 repository gate and audits:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.isClosed_upperRectangle \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.log_log_exp_log_rpow \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.exp_log_rpow_mono \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.card_filter_Icc_add_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.eventually_walk_cap_le_sqrt \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.eventually_early_gap_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_le_two_mul_of_normalized_terminal_le_one \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.normalized_omegaUpTo_cutoff_le
```

Verdict: `FORMALIZE-TIER GREEN`; all eight audited helpers use only `propext`,
`Classical.choice`, and `Quot.sound`.

Lap-5 narrow elaboration:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean
```

Exit 0.  The sole scoped proof-debt warning remains `divisorVariance_diverges_at_ln2`.

Lap-5 repository gate and audits:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.strictMono_equalTimeGrid \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.equalTimeGrid_increment \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.brownianFDD_upperRectangle_equalTimeGrid \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.eventually_collisionCutoff_le_exp_log_rpow_add \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.omegaUpTo_le_two_mul_of_normalized_terminal_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.eventually_const_le_sqrt
```

Verdict: `FORMALIZE-TIER GREEN`; all six audited helpers use only `propext`,
`Classical.choice`, and `Quot.sound`.

Lap-6 integration build:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointEK
```

Exit 0.  The new auxiliary module is sorry-free, and the sole scoped proof-debt warning remains
`divisorVariance_diverges_at_ln2`.

Lap-6 repository gate and audits:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEKAux.gaussianWalk_survival_probability_le_fourthRoot \
  --axioms NormalNumbers.ErdosBorweinEndpointEKAux.gaussianWalk_fixedVariance_survival_probability_le_fourthRoot \
  --axioms NormalNumbers.ErdosBorweinEndpointEKAux.gaussianWalkSurvives_iff_prefix_sums \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.gaussianPartialSumUpperSet_eq_survivalSet \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.brownianFDD_upperRectangle_equalTimeGrid_le
```

Verdict: `FORMALIZE-TIER GREEN`; all five audited ballot/adapter theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

At the lap-6 checkpoint the two downstream headlines still reported `sorryAx`, solely through the
then-open Step-2 theorem.  The lap-7 audit below supersedes that historical result.

Lap-7 narrow elaboration and module build:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean
lake build NormalNumbers.CoefmassErdosBorweinEndpointEK
```

Both exit 0.  The scoped file contains no `sorry`, `native_decide`, or hand-declared axiom.

Lap-7 repository gate and final audits:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --import NormalNumbers.CoefmassErdosBorweinEndpointEK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.gaussianReal_abs_tail_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.gaussianProduct_sum_abs_tail_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.brownianFDD_first_ge_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.brownianFDD_last_ge_le \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.equalTimeGrid_control_bounds \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.divisorVariance_diverges_at_ln2 \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.ebRandom_ae_normal_le_ln2_of_EK \
  --axioms NormalNumbers.ErdosBorweinEndpointEK.ebPowerCandidateNormal_of_EK
```

Verdict: `FORMALIZE-TIER GREEN`.  All eight audited declarations use exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Current blocker

None in scope.  The host predicate
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean` is satisfied.

## Next highest-value attack

No stretch work was requested for this lap.  Preserve the completed frozen statements and the
named-hypothesis status of `ErdosKacFiniteDim`; any later objective should begin from this green
checkpoint.
