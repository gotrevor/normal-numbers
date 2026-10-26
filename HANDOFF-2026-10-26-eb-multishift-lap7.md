# Erdős–Borwein multishift — grind lap 7

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

Closed Step 4 all the way from the abstract product law to the packet-verbatim `multiShiftMass`.

- `finiteProductMass_reindex` in `CoefmassErdosBorweinMultiShiftAux.lean` proves invariance of a
  finite product event mass under an arbitrary equivalence from `Fin n` to a finite coordinate
  type.
- `primeIndexEquiv` enumerates the subtype `primesIoc P y`; `indexedMultiShiftPattern` reconstructs
  every shift's prime finset from an indexed categorical configuration.
- `multiShiftMass_eq_finiteProductMass` identifies the exact packet model with
  `finiteProductMass` at `q_i = 1/p_i`. The proof reindexes both the outer configuration sum and
  the inner prime product, and checks the `none` and `some` weights exactly.
- `card_indexedMultiShiftPattern` transports each column cardinality. This specializes lap 6's
  `categoricalShiftProduct_noHeavy_le_independent` in
  `multiShiftMass_noHeavy_le_independent` under the packet-side hypothesis `J ≤ P`.
- `sum_primeIndex_inv_sq_le` uses Mathlib's `sum_Ioc_inv_sq_le_sub` to prove
  `∑_{P<p≤y} p⁻² ≤ P⁻¹` without a new analytic input.
- `multiShiftMass_noHeavy_le_prod_one_sub` is the completed concrete Step 4 theorem:

  ```text
  multiShiftMass P y J {all columns below threshold}
    ≤ ∏_j (1 - BernoulliMass(column j heavy)) + 2 J (J-1) / P.
  ```

No statement named in the operator's frozen list changed. No `native_decide`, axiom, heartbeat
increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShiftAux.lean
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed; the target emitted only the expected warning for its original headline `sorry`.

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShift
```

Passed: 8883 jobs; only existing publish-tier warnings and the target's original headline
`sorry` were reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.multiShiftMass_noHeavy_le_prod_one_sub
```

Passed: `FORMALIZE-TIER GREEN`, 8883 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs. Existing repository proof debt was reported but is
not a gate failure at this tier.

## Current blocker

Steps 5 and 4 are complete. The headline still needs Steps 1, 2, 3 and the final asymptotic
assembly. The next route-decisive missing input is Step 1, the deterministic implication from a
large count of primes in `(collisionCutoff N, y₀]` dividing `n+j` (together with
`ω(n+j) ≤ 4 log log N`) to
`b⁻²ʲ * divisorVarianceMass ... (n+j) > T`.

This requires careful quantitative plumbing: choose the largest counted prime, apply
`divisorVarianceMass_ge_primeChain` and `card_primeChainDivisors`, convert the prime-count surplus
to a chain-cardinality exponent, use `hdelta` plus eventual monotonicity of `subpowerWeight`, and
absorb the Mertens comparison between the model mean and `log log y₀ - log log P₀`.

## Next highest-value attack

Search the existing endpoint/EK files for the strongest already-packaged deterministic chain
corollary and the repository's exact Mertens API. State one helper whose conclusion is precisely
the shifted-variance heaviness needed by Step 1 (with all threshold constants explicit), then
prove it from the chain bound. Avoid starting Step 2 or transfer bookkeeping until this
quantitative implication is kernel-checked.
