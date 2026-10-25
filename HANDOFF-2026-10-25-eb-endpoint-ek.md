# HANDOFF: EB endpoint Step 2, EK laps 1--4

Branch `research/eb-endpoint` is local only.  Never push it.  The scoped host predicate is
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean`.  Do not change any existing
statement in that file, and keep `ErdosKacFiniteDim` as the named hypothesis exactly as planted.

## Concrete advance

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

Auditing the two downstream headlines currently reports `sorryAx`, as expected, solely because
they transitively call the one open Step-2 theorem.  Once that theorem closes, rerun the headline
audits required by `EB-ENDPOINT-EK-NEXT.md`.

## Current blocker

Exactly one `sorry` remains: `divisorVariance_diverges_at_ln2`.  Its combinatorial chain lower
bound is no longer part of the blocker.  The remaining layers are:

1. finish the finite-grid bookkeeping around `normalized_omegaUpTo_cutoff_le`, including the
   eventual comparison placing `collisionCutoff N` below the early FDEK cutoff;
2. apply `ErdosKacFiniteDim` to the now-proved closed coordinatewise upper set;
3. prove the elementary `brownianFDD` Gaussian recursion/grid probability tends to zero, then
   finish the density limit (including the fixed shift `n ↦ n+a₀`).

The main formalization risk is the probability layer: `brownianFDD` is a mapped finite product of Gaussian
increments, and the needed rectangle probability/factorization API has not yet been developed in
this repository.  The Lean reference corpus search found no existing implementation to reuse.

## Next highest-value attack

Prove
`collisionCutoff N ≤ exp ((log (N+a₀))^s)` eventually for every fixed `s > 0`, then choose a
concrete strictly increasing time vector containing `s`, the geometric grid, and `1`.  Use
`normalized_omegaUpTo_cutoff_le` coordinatewise to obtain membership in `upperRectangle`, invoke
`hEK`, and begin the finite Gaussian recursion estimate.  The probability layer should reuse
Mathlib's product-measure cylinder API and `gaussianReal_apply`; the sibling TauCeti repository has
proved Gaussian CDF/density infrastructure to consult, but it is not a dependency of this repo.
