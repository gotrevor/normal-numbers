# Erdős–Borwein multishift — grind lap 5

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement.  `MultiShiftKubiliusTV` remains a named hypothesis.  The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Concrete advance

Closed the exact finite pushforward half of Step 4 in
`CoefmassErdosBorweinMultiShiftAux.lean`.

- `singletonClearing` keeps a singleton subset of `Fin J` as `some j` and sends the empty set and
  all collision subsets to `none`; its `some` and `none` fibers are characterized.
- `independentShiftSubsetWeight` is the one-prime law of `J` fully independent Bernoulli-`q`
  coordinates.  Its total mass, empty mass, and singleton mass are proved exactly.
- `independentShiftSubsetWeight_singletonClearing_fiber` proves that the pushforward of that law is
  exactly `clearedIndependentShiftWeight`, including the merged `none` fiber.
- `finiteProductWeight_pushforward_fiber` and `finiteProductMass_pushforward` prove generic finite
  coordinatewise pushforward identities.
- `clearedProductMass_eq_independentClearedMass` specializes the generic identity: for every event,
  the cleared product mass is exactly the fully independent shift-subset mass of its preimage under
  coordinatewise singleton clearing.
- `independentShiftCollisionMass_eq` computes the exact one-prime collision probability as
  `1 - (1-q)^J - Jq(1-q)^(J-1)`.
- `independentShiftCollisionMass_le` proves the route-level bound
  `P(collision at one prime) ≤ J(J-1)q²` using Bernoulli's inequality and the already-proved
  singleton-defect estimate.

No statement in `CoefmassErdosBorweinMultiShift.lean` changed.  No `native_decide`, axiom,
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

Passed: 8707 jobs; the target emitted only the expected warning for its original headline `sorry`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --import NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --axioms NormalNumbers.ErdosBorweinMultiShift.clearedProductMass_eq_independentClearedMass
```

Passed: `FORMALIZE-TIER GREEN`, 8707 jobs.  Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

The same targeted gate for
`NormalNumbers.ErdosBorweinMultiShift.independentShiftCollisionMass_le` passed with the same axiom
list.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs.  Existing repository proof debt was reported but is
not a gate failure at this tier.

## Current blocker

The fully independent law is now connected exactly to the cleared law, and its one-prime collision
cost is bounded.  The remaining Step 4 bridge is global: bound the finite-product event that some
prime coordinate collides by the sum of the local collision masses, then show that away from this
event clearing preserves every per-shift prime count.  The independent prime-by-shift array must
then be transposed (or encoded as a Bernoulli subset of `Fin n × Fin J`) so the per-shift no-heavy
events factor.

After that, Step 4 needs an enumeration lemma identifying the packet-verbatim `multiShiftMass` with
the categorical `finiteProductMass` on `primesIoc`.  Steps 1, 2, 3 and the final asymptotic assembly
remain open.

## Next highest-value attack

Prove a generic nonnegative normalized finite-product union bound

```text
P(∃ i, bad_i(σ_i)) ≤ Σ_i P_i(bad_i),
```

apply it with `bad_i(S) := 2 ≤ S.card` and `independentShiftCollisionMass_le`, and prove that
singleton clearing leaves all column counts unchanged off that event.  Then encode the array as a
Bernoulli subset of `Fin n × Fin J` and use `bernoulliSubsetMass_cylinders` on the disjoint shift
columns to derive the exact product formula for the no-heavy event.
