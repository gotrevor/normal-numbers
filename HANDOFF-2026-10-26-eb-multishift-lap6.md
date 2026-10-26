# Erdős–Borwein multishift — grind lap 6

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

Closed Step 4 at the abstract finite-model level in
`CoefmassErdosBorweinMultiShiftAux.lean`.

- `finiteProductMass_nonneg`, `finiteProductMass_mono`, `finiteProductMass_union_le`,
  `finiteProductMass_exists_mem_le_sum`, and `finiteProductMass_coordinate_eq` supply the generic
  finite-product probability API that the collision argument needed.
- `independentShiftProductCollisionMass_le` tensorizes lap 5's one-prime estimate and proves that
  the probability of any collision is at most
  `∑_i J (J-1) q_i²`.
- `singletonClearing_column_eq` proves that clearing preserves every shift's selected-prime count
  off the collision event.
- `shiftArrayEquiv` transposes a prime-indexed family of shift subsets into a subset of
  `Fin n × Fin J`. `finiteProductMass_independentShift_eq_bernoulliArray` proves exact equality
  of event masses under this transposition.
- `independentShiftProduct_columns_factor` applies the existing Bernoulli cylinder theorem to
  disjoint shift columns. `independentShiftProduct_card_lt_eq_prod_one_sub` gives the paper's
  exact formula `P(no shift is heavy) = ∏_j (1-p_j)`.
- `categoricalShiftProduct_noHeavy_le_independent` combines the categorical/cleared TV bound,
  the exact clearing pushforward, preservation off collisions, and the global collision bound:
  the categorical no-heavy mass is at most the fully independent no-heavy mass plus twice
  `∑_i J (J-1) q_i²`.

No statement in `CoefmassErdosBorweinMultiShift.lean` changed. No `native_decide`, axiom,
heartbeat increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShiftAux.lean
```

Passed with no output.

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShiftAux
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed: 8707 jobs; the target emitted only the expected warning for its original headline
`sorry`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --import NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --axioms NormalNumbers.ErdosBorweinMultiShift.categoricalShiftProduct_noHeavy_le_independent
```

Passed: `FORMALIZE-TIER GREEN`, 8707 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs. Existing repository proof debt was reported but is
not a gate failure at this tier.

## Current blocker

The abstract comparison and exact independent-column factorization are complete. The remaining
Step 4 specialization is arithmetic/enumerative: identify packet-verbatim `multiShiftMass P y J`
with `finiteProductMass` for an enumeration of `primesIoc P y`, with
`q_i = 1 / p_i`; translate its Option-array column counts back to the `Finset ℕ` pattern; and
bound `∑_i J(J-1)/p_i²` by a reciprocal-square tail such as `O(J²/P)`.

After that specialization, Steps 1, 2, 3 and the final asymptotic assembly remain open. The
moderate-deviation theorem is already proved and can be applied directly on each finite column
`shiftArrayColumn n J j`; no further independence theorem is needed.

## Next highest-value attack

Choose the canonical equivalence between `Fin (primesIoc P y).card` and the subtype
`primesIoc P y`. Prove a single `multiShiftMass_eq_finiteProductMass` enumeration lemma, including
the exact reconstruction of each shift's prime finset. Then specialize
`categoricalShiftProduct_noHeavy_le_independent` at `q_i = 1/p_i` and discharge the collision
error with the repo's reciprocal-square prime tail bound (or first prove the elementary integer
tail bound if no suitable theorem exists).
