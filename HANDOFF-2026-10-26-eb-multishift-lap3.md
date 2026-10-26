# Erdős–Borwein multishift — review lap 3

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement.  `MultiShiftKubiliusTV` remains a named hypothesis.  The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Fresh review verdict

The target module differs from planting commit `b774314f` only by the import of
`CoefmassErdosBorweinMultiShiftAux`; every frozen definition, hypothesis, and headline is
character-identical.  The exact Step 1′ interface still asks for density-zero bounded shifted
variance mass, and the endpoint prime-chain lemmas still supply the advertised deterministic
lower bound.  Thus the route continues to reach the headline.

The review did find one real error in the prose route for Step 4.  The categorical per-prime law
used by `multiShiftMass` is **not** the product of `J` Bernoulli(`1/p`) variables conditioned on at
most one success: conditioning changes both the singleton and empty-state weights.
`conditionedIndependent_singleton_ne_categorical` records the counterexample `J=2`, `p=3` in
the kernel.  No frozen theorem statement was affected.  `EB-MULTISHIFT-NEXT.md` now prescribes
the correct direct comparison.  The independent law's total singleton deficit at one prime is

```text
J q (1 - (1-q)^(J-1)) <= J (J-1) q^2,
```

proved as `independentSingletonDefect_le`.  This is also the exact one-coordinate TV distance;
tensorization still gives the required `O(J²/P₀)` error, so the route survives unchanged after
the correction.

## Concrete advance

Closed Step 5's standalone finite probability input in
`CoefmassErdosBorweinMultiShiftAux.lean`.

- `sub_sq_le_one_sub_exp_neg` and `exp_sub_one_le_add_sq` provide the two small-tilt Taylor
  inequalities from Mathlib's certified exponential remainder.
- `sum_bernoulliVariance_eq_sub_squareMass` records `variance = mean - Σq²`.
- `bernoulliSubsetMass_card_ge_quadratic_lower` converts the lap-2 tilted-window theorem into a
  near-Gaussian lower bound with leading loss `μθ²/2` and explicit square-mass, cubic, and window
  errors.
- `bernoulliSubsetMass_card_ge_explicit_moderate_lower` chooses
  `θ = (1+4η)x/μ` and radius `ηx`, obtaining
  `(1/2) exp(-(1/2+20η)x²/μ)` under five transparent scalar inequalities.
- `bernoulliSubsetMass_card_ge_moderate_lower` absorbs the fixed `1/2` and proves the paper's
  required form
  `exp(-(1+ε)x²/(2μ)) <= P(S >= μ+x)`.

No statement in `CoefmassErdosBorweinMultiShift.lean` changed.  No `native_decide`, axiom,
heartbeat increase, or new `sorry` was introduced.

## Exact verification

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShiftAux.lean
```

Passed with no output.

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean
```

Passed, with only the expected warning for the frozen headline's original `sorry`.

```text
lake build NormalNumbers.CoefmassErdosBorweinMultiShiftAux
```

Passed: 8707 jobs.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --import NormalNumbers.CoefmassErdosBorweinMultiShiftAux \
  --axioms NormalNumbers.ErdosBorweinMultiShift.bernoulliSubsetMass_card_ge_moderate_lower
```

Passed: `FORMALIZE-TIER GREEN`, 8707 jobs.  The new endpoint theorem's axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10849 jobs.  Existing repository proof debt was reported but is
not a gate failure at this tier.

## Current blocker

Step 5 is no longer an open probability lemma.  Its application to `q(p)=1/p` will require the
scalar hypotheses already expected from Mertens and the reciprocal-square tail: positive growing
mean, `Σp⁻² = o(μ)`, `x/μ -> 0`, and `x²/μ -> ∞`.  These are schedule facts rather than a
probabilistic gap and can be discharged when the heavy-event thresholds are assembled.

The next genuine construction is Step 4: define the fully independent `J`-shift subset mass,
compare its one-prime categorical factor directly with `multiShiftMass`, tensorize the
per-coordinate TV costs, and derive independence of the heavy events across shifts.  Do not use
the refuted conditioned-product identity.

## Next highest-value attack

Build the direct categorical/product coupling above `ebRandom_ae_normal_subpower_of_multiShift`
(or in a new auxiliary module if avoiding an import cycle requires it).  Start with an exact
one-prime mass decomposition whose TV is the singleton deficit already bounded by
`independentSingletonDefect_le`; then prove the product/tensorization inequality and the
`P(no heavy) = ∏_j (1-p_j)` factorization.  Once Step 4 is green, proceed to the deterministic
heavy-prime bridge (Step 1), exceptional set, transfer, and final Step 1′ assembly.
