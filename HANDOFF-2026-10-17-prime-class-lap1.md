# Prime class lap 1 (2026-10-17): pair algebra and L2 wiring

## Concrete advance

- Added `StonehamPrimeClassAlgebra.lean`.  Its kernel proofs identify doubled exponent
  divisibility with equality of squared primitive-root powers and prove
  `linearIndependent_two_powers_iff`:
  `LinearIndependent ℚ ![ζ^m₁, ζ^m₂] ↔ ¬ (d : ℤ) ∣ 2(m₂-m₁)`.
- Replaced the direct sorry in `isRationallyJointNormal_pair_iff` by specialization of
  `isRationallyJointNormal_iff_linearIndependent` at a canonical primitive complex root and the
  new algebraic criterion.
- Replaced the direct sorry in `stonehamThreeSevenPairwiseNormal_holds` by the three pair
  instances.  The proof kernel-checks `orderOf (3 : ZMod 7) = 6` with finite cases and unfolds all
  six ordered pairs with arbitrary rational coefficients.
- The scoped target now has exactly two direct sorries, the non-normal and normal halves of T-B′.
  The pair and L2 direct-sorry BarrierAudit waivers were removed; only the two core waivers remain.

## Verification

- `lake build NormalNumbers.StonehamPrimeClassAlgebra` — success, 8,774 jobs.
- `lake env lean src/NormalNumbers/StonehamPrimeClass.lean` — success; only the two core T-B′
  declarations report sorry.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target NormalNumbers.StonehamPrimeClass` —
  8,957 jobs, final verdict `FORMALIZE-TIER GREEN`.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClassAlgebra --axioms
  NormalNumbers.StonehamPrimeClass.linearIndependent_two_powers_iff` — 8,774 jobs,
  `[Classical.choice, Quot.sound, propext]`, `FORMALIZE-TIER GREEN`.
- The first full `lean-green` run exposed the two now-stale pair/L2 BarrierAudit waivers; they were
  removed before the final gate.
- Final `~/personal/bin/lean-green ~/src/nn-prime-class` — 10,882 jobs, BarrierAudit reports
  79 waivers / 106 open sorries scanned, final verdict `FORMALIZE-TIER GREEN`.

## Current blocker

The route-decisive open core is now purely the arbitrary-finite-family theorem.  The non-normal
half needs the prime-class coefficient/Mahler reduction and positive-density bounded-denominator
contradiction.  The normal half needs a general one-class finite-Teichmüller cancellation bound
feeding `stonehamCombination_mean_tendsto_of_powerLower`.  Existing literal-pair machinery is
not general enough because it only handles coefficients ±1 and special aligned tails.

## Next highest-value attack

Continue kickoff step 1 before the analytic halves: formalize the finite-level cyclotomic
vanishing bridge for an arbitrary cleared polynomial `Σ qᵢ X^{mᵢ}`.  First isolate the mathlib
side (vanishing at a primitive complex root iff divisibility by `cyclotomic d ℚ`), then connect
that polynomial to the finite Teichmüller representative `b^(p^K) mod p^(K+1)`.  This is the
shared arithmetic input to both remaining halves.
