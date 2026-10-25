# HANDOFF: EB endpoint Kubilius route, lap 1

Branch `research/eb-endpoint` is local only. Never push it. The scoped host predicate is
`sorry-free:src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`. Read
`EB-ENDPOINT-KUB-NEXT.md` first. Do not change any statement in the target file, and keep
`KubiliusTV` as the named hypothesis exactly as planted: never prove, weaken, or axiomatize it.

## Concrete advance

The target now has one remaining proof debt rather than two. The downstream assembly theorem
`ebPowerCandidateNormal_of_kubilius` is proved by combining
`exists_powerDelta_variance_lower`, the growing-moment criterion
`ebRandom_ae_normal_of_divisorVariance_diverges`, and the still-open Kubilius Step 2 theorem.
Its statement was not changed.

The new module `CoefmassErdosBorweinEndpointKubAux.lean` supplies the finite probability algebra
needed for Step 2 without introducing a measure-space encoding:

- `sum_subsetChoiceWeight` is the finite product/sum distributivity identity over all subsets;
- `sum_bernoulliSubsetWeight` proves that the Bernoulli subset weights total one;
- `bernoulliSubsetWeight_nonneg`, `bernoulliSubsetMass_nonneg`,
  `bernoulliSubsetMass_mono`, and `bernoulliSubsetMass_le_one` make the event mass a genuine
  probability mass;
- `bernoulliSubset_expectation_prod` is the full independence identity for products of arbitrary
  local two-valued observables;
- `bernoulliSubset_membership_expectation` and `bernoulliSubset_card_expectation` give the exact
  coordinate and cardinality means.

The target specializes this layer to `q(p)=1/p`:
`kubiliusMass_eq_bernoulliSubsetMass`, `kubiliusMass_univ`, `kubiliusMass_nonneg`,
`kubiliusMass_mono`, `kubiliusMass_le_one`, and `kubilius_card_expectation`. Thus later tail and
crossing estimates can work with proved probability identities instead of repeatedly expanding
the raw powerset sum.

No pre-existing statement in `CoefmassErdosBorweinEndpointKub.lean` was changed. No axiom,
`native_decide`, or new hypothesis was added.

## Verification

Narrow build:

```text
lake build NormalNumbers.CoefmassErdosBorweinEndpointKubAux \
  NormalNumbers.CoefmassErdosBorweinEndpointKub
```

Completed successfully. The sole target-file proof-debt warning is
`divisorVariance_diverges_at_ln2_of_kubilius`.

Repository gate and axiom audits:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --import NormalNumbers.CoefmassErdosBorweinEndpointKub \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubset_expectation_prod \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.bernoulliSubset_card_expectation \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_univ \
  --axioms NormalNumbers.ErdosBorweinEndpointKub.kubiliusMass_mono
```

Verdict: `FORMALIZE-TIER GREEN`. Every audited theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`.

The commit hook also ran the repository-wide `lake build`: `Build completed successfully
(10847 jobs)`.

An explicit audit of `ebPowerCandidateNormal_of_kubilius` still reports `sorryAx`, exactly through
the one remaining Step 2 theorem; there is no additional proof debt in the assembly.

## Current blocker

The only scoped sorry is `divisorVariance_diverges_at_ln2_of_kubilius`. Its hard core remains the
model crossing estimate from `EB-ENDPOINT-KUB-NEXT.md`: uniformly positive one-sided crossing
probability for each of finitely many independent prime blocks, followed by the shift/TV transfer.

## Next highest-value attack

Continue in `CoefmassErdosBorweinEndpointKubAux.lean` from
`bernoulliSubset_expectation_prod`:

1. Define the centered local increment `1_{p∈S}-q(p)` and prove the exact second-moment identity
   for a finite weighted sum. This directly supplies the Chebyshev bounds for the running value
   and for `#S > 2L`.
2. Prove the fourth-moment bound for a centered Bernoulli sum,
   `E X^4 ≤ 3(Σ q(1-q))^2 + Σ q(1-q)`. The existing arbitrary-product identity is designed to
   discharge every mixed monomial.
3. Package the one-sided Paley--Zygmund consequence with an absolute uniform constant. Only after
   this block lemma is green should the next lap formalize the geometric prime blocks and Mertens
   comparisons in the target theorem.

The constant order from the operator plan is load-bearing: choose fixed block count `K`, then
`M`, then `r ≥ 64 M²`; do not return to a growing-number-of-blocks union bound.
