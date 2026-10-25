# HANDOFF: EB endpoint Step 2, EK laps 1--2

Branch `research/eb-endpoint` is local only.  Never push it.  The scoped host predicate is
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean`.  Do not change any existing
statement in that file, and keep `ErdosKacFiniteDim` as the named hypothesis exactly as planted.

## Concrete advance

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

Auditing the two downstream headlines currently reports `sorryAx`, as expected, solely because
they transitively call the one open Step-2 theorem.  Once that theorem closes, rerun the headline
audits required by `EB-ENDPOINT-EK-NEXT.md`.

## Current blocker

Exactly one `sorry` remains: `divisorVariance_diverges_at_ln2`.  Its combinatorial chain lower
bound is no longer part of the blocker.  The remaining layers are:

1. cover a fixed FDEK grid point by the proved prime-jump cap or the
   no-prime-since-an-early-grid-point case,
   using extra grid points `s₀` and `1` to control small primes and total omega;
2. apply `ErdosKacFiniteDim` to the closed coordinatewise upper set;
3. prove the elementary `brownianFDD` Gaussian recursion/grid probability tends to zero, then
   finish the density limit.

The main formalization risk is layer 4: `brownianFDD` is a mapped finite product of Gaussian
increments, and the needed rectangle probability/factorization API has not yet been developed in
this repository.  The Lean reference corpus search found no existing implementation to reuse.

## Next highest-value attack

Prove the finite-cutoff bridge before introducing measures.  For a real grid cutoff `y`, split on
whether `n` has a prime factor in `(P,y]`.  In the jump case choose the largest such factor `p`, prove
`omegaUpTo y n = omegaUpTo p n`, and transfer the new prime-jump cap using
`log (log p) ≤ log (log y)`.  In the no-jump case identify/bound `omegaUpTo y n` by the early-grid
small-prime count.  Package this as a pointwise implication into the coordinatewise FDEK closed set;
then formalize that set and its closedness.
