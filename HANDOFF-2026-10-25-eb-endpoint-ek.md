# HANDOFF: EB endpoint Step 2, EK lap 1

Branch `research/eb-endpoint` is local only.  Never push it.  The scoped host predicate is
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointEK.lean`.  Do not change any existing
statement in that file, and keep `ErdosKacFiniteDim` as the named hypothesis exactly as planted.

## Concrete advance

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

Auditing the two downstream headlines currently reports `sorryAx`, as expected, solely because
they transitively call the one open Step-2 theorem.  Once that theorem closes, rerun the headline
audits required by `EB-ENDPOINT-EK-NEXT.md`.

## Current blocker

Exactly one `sorry` remains: `divisorVariance_diverges_at_ln2`.  Its combinatorial chain lower
bound is no longer part of the blocker.  The remaining layers are:

1. turn `W ≤ T` plus the chain inequality into a cap on
   `omegaUpTo p (n+a₀) - log (log p)` at every prime jump above `collisionCutoff N`;
2. cover a fixed FDEK grid point by the jump case or the no-prime-since-an-early-grid-point case,
   using extra grid points `s₀` and `1` to control small primes and total omega;
3. apply `ErdosKacFiniteDim` to the closed coordinatewise upper set;
4. prove the elementary `brownianFDD` Gaussian recursion/grid probability tends to zero, then
   finish the density limit.

The main formalization risk is layer 4: `brownianFDD` is a mapped finite product of Gaussian
increments, and the needed rectangle probability/factorization API has not yet been developed in
this repository.  The Lean reference corpus search found no existing implementation to reuse.

## Next highest-value attack

Prove the walk-cap lemma first, directly from
`divisorVarianceMass_ge_primeChain_endpoint`.  Keep it finite and pointwise: assume a prime
`p | n`, `P < p`, `W ≤ T`, and an a priori bound `omegaUpTo p n ≤ 2L`; derive an explicit upper
bound for `omegaUpTo p n - log (log p)` of the form `C(c,T) + log (2L)`.  This isolates all real
log/rpow rearrangement before introducing FDEK or measures.  Then formalize the finite-grid set and
its closedness.
