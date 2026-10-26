# Erdős–Borwein multishift — reflection lap 8

## Scoped objective

Make `src/NormalNumbers/CoefmassErdosBorweinMultiShift.lean` sorry-free without changing any
packet-verbatim statement. `MultiShiftKubiliusTV` remains a named hypothesis. The target still
has its original single `sorry`, in `ebRandom_ae_normal_subpower_of_multiShift`.

## Architectural reflection and route correction

The lap-7 baton prescribed the paper's Step 1 decomposition: cap `omega(n+j)` by `4 log log N`,
end the divisor chain at its largest selected prime, and then remove the large-omega exceptional
set. That cap is unnecessary.

Every member of `primeChainDivisors p (n+j)` divides `n+j`, hence is at most `n+j`. On the range
transferred from the multishift model, `n+j <= 2N` eventually. Since `subpowerWeight c` is
eventually antitone, every chain member therefore has weight at least `subpowerWeight c (2N)`.
Thus a column containing `r` selected primes directly gives

```text
divisorVarianceMass v P (n+j)
  >= 2^(r-1) * c0 * subpowerWeight c (2N).
```

This has the same asymptotic exponent required by the paper. Writing `L = log log N`,
`log log y0 = L - log u`, and using Mertens for the model mean, the logarithm of the right side
after the heavy threshold is imposed is

```text
log 2 * (B log L - log u - log log P +
  sqrt(c * log log y0 * log log log y0) - sqrt(c * L * log L)) + O(1)),
```

apart from the intended `2j log b` term. The square-root difference is `o(log L)`, while
`log u + log log P = O(log L)`, so a fixed large `B` still wins. Consequently the former Step 2
large-omega exceptional set can be deleted from this route rather than formalized.

There is one important case split for the later probability assembly. For `c > 0`, lap 5's
moderate-deviation lower bound applies to the `sqrt(c L log L)` displacement. For `c <= 0`, that
displacement vanishes and the remaining `O(log L + j)` threshold can be dominated by a fixed
large multiple of `sqrt L`; a fixed-probability central-tail lower bound should be used instead.
Trying to feed the `c <= 0` threshold directly to
`bernoulliSubsetMass_card_ge_moderate_lower` would fail its large-deviation hypothesis.

## Concrete advance

The corrected deterministic layer is now kernel-checked.

- `divisorVarianceMass_ge_primeDivisorSet` in
  `CoefmassErdosBorweinMultiShiftAux.lean` generalizes the existing prime-chain machinery to an
  arbitrary nonempty finite set `Q` of prime divisors above `P`. It chooses `max Q`, embeds `Q`
  into `primeFactorsUpTo`, obtains at least `2^(card Q - 1)` chain divisors, and only asks for a
  pointwise weight lower bound on `(P,M]`.
- `subpowerWeight_nonneg` and `subpowerWeight_antitone_of_log_log_one_le` prove the analytic facts
  needed to take the common lower bound at `M`. The antitonicity proof handles both `c >= 0` and
  `c <= 0`; in the latter case the square-root penalty is exactly zero on the eventual range.
- `divisorVarianceMass_ge_primeDivisorSet_subpower` specializes the generic chain theorem using
  the packet-verbatim `subpowerWeight` and `hdelta`-shaped pointwise input.
- `shiftedVarianceMass_gt_of_heavyColumn` is the concrete Step 1 bridge. A heavy
  `multiShiftPattern` column whose explicit chain lower bound beats `T * b^(2(j+1))` forces
  `shiftedVarianceMass ... n > T`. It also checks the zero-based model column / one-based shift
  alignment (`j : Fin J` corresponds to shift `j.val + 1`).

No packet-verbatim definition or theorem statement changed. No `native_decide`, axiom, heartbeat
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

Passed: 8885 jobs; only existing publish-tier warnings and the target's original headline `sorry`
were reported.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinMultiShift \
  --import NormalNumbers.CoefmassErdosBorweinMultiShift \
  --axioms NormalNumbers.ErdosBorweinMultiShift.shiftedVarianceMass_gt_of_heavyColumn
```

Passed: `FORMALIZE-TIER GREEN`, 8885 jobs. Axioms are exactly
`['Classical.choice', 'Quot.sound', 'propext']`.

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-eb-endpoint
```

Passed: `FORMALIZE-TIER GREEN`, 10854 jobs. Existing repository proof debt was reported but is
not a gate failure at this tier. As in the preceding multishift laps, the root module imports the
auxiliary file but not the still-open packet target, so the target-specific gate above is the check
that covers this campaign file.

## Current blocker

The deterministic implication is complete, and the old omega-exceptional-set obligation is gone.
The headline still needs the quantitative schedule and transfer assembly: define `J`, `y0`, the
prime-block mean and integer column thresholds; prove that the explicit scalar premise of
`shiftedVarianceMass_gt_of_heavyColumn` holds eventually; transfer no-heavy density with `hM`; and
show the independent product tends to zero using Step 4 plus the moderate-deviation theorem.

## Next highest-value attack

Formalize the scalar/schedule adapter before the sieve transfer. In particular:

1. package Mertens for `primesIoc P y` (both sides of `mean = log log y - log log P + O(1)`);
2. choose `M = 2N` and prove the eventual cutoff facts needed by the deterministic theorem,
   including `log log (collisionCutoff N + 1) >= 1`;
3. define the integer heavy threshold so its cardinal lower bound implies the explicit scalar
   premise, with the `2(j+1) log b / log 2` term;
4. split `c > 0` from `c <= 0` when supplying model-column probabilities, as described above.

Do not reintroduce an `omega(n+j)` cap or its exceptional-set estimate.
