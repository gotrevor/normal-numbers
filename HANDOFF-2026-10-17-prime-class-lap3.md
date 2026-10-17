# Prime class lap 3 REVIEW (2026-10-17): finite cyclotomic lift

## Concrete advance

- The adversarial review rechecked the scoped theorem headers and `primeClassFamily` against the
  scaffold commit `e6dca38d`: they are unchanged.  The pair and L2 proofs are structurally sound
  but still depend transitively on the two general T-B′ halves, so their Maze row and the two core
  BarrierAudit waivers correctly remain unchanged.
- The review found a real seam in kickoff step 1: dependence produced a rational cyclotomic
  relation, while the finite arithmetic layer needed one fixed nonzero integral coefficient
  vector.  `not_linearIndependent_powers_iff_exists_integer_cyclotomic` now clears the finite set
  of rational denominators and proves the exact integral criterion in both directions.
- Added `StonehamPrimeClassFinite.lean`.  For `d = orderOf (b : ZMod p)`, every proper-divisor
  cyclotomic factor at `b^(p^K)` is a unit modulo `p`; evaluating the factorization of `X^d - 1`
  therefore puts all available `p`-power into `Φ_d(b^(p^K))`.
- `prime_pow_dvd_cyclotomic_eval_teichmuller` proves the uniform `p^K` bound.  The LTE
  specializations prove the paper's sharper `p^(K+1)` bound for odd primes and the dyadic
  `2^(K+3)` bound at `b^(2^(K+1))`.  Each bound transfers to every cleared relation polynomial.
- `exists_integerRelation_prime_pow_dvd_teichmuller_of_not_linearIndependent` closes the dependent
  direction of the finite bridge end-to-end: one nonzero integral vector works at every depth K.
  The new module is imported by both the scoped target and the root library.
- The scoped file still has exactly its two ratified analytic sorries; no frozen statement was
  altered and no new sorry, axiom, or `native_decide` was introduced.

## Verification

- `lake env lean src/NormalNumbers/StonehamPrimeClassCyclotomic.lean` — success.
- `lake build NormalNumbers.StonehamPrimeClassCyclotomic && lake env lean
  src/NormalNumbers/StonehamPrimeClassFinite.lean` — success.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClassFinite --import NormalNumbers.StonehamPrimeClassFinite` with
  axiom checks for the integral clearing theorem, uniform/odd/dyadic cyclotomic lifts, and the
  final dependent-family bridge — 8,776 jobs, every declaration exactly
  `[Classical.choice, Quot.sound, propext]`, final verdict `FORMALIZE-TIER GREEN`.
- `~/personal/bin/lean-green ~/src/nn-prime-class --target
  NormalNumbers.StonehamPrimeClass` — 8,959 jobs, final verdict `FORMALIZE-TIER GREEN`.
- `~/personal/bin/lean-green ~/src/nn-prime-class` — 10,884 jobs; BarrierAudit reports 79 waivers
  / 106 open sorries scanned, final verdict `FORMALIZE-TIER GREEN`.

## Current blocker

Kickoff step 2 must connect the fixed integral relation now supplied by the finite bridge to the
actual common-denominator Stoneham state for the mixed subseries `p^(s i)`.  The `s i` change
which prime-class kicks occur, so the proof must implement the paper's periodic coefficient
rescaling/Mahler shift before the cyclotomic congruence yields bounded-denominator pieces on a
positive-density set.  The existing L1/L2 zero-window arguments prove the final digit-frequency
contradiction once that general state congruence and tail estimate are available.

The normal half will later need the complementary bounded-loss statement for a relation
polynomial not divisible by `Φ_d` (most naturally a fixed nonzero resultant), but kickoff order
puts the dependent/non-normal state bridge first.

## Next highest-value attack

Stay in kickoff step 2.  In a new `StonehamPrimeClass*.lean` module, express the cleared numerator
of `∑ i a i * α_(b^(m i),p^(s i))` at a common prime depth, absorb the `s i`-dependent residue
classes using the Mahler identity from the paper, and prove that the resulting newest coefficient
is the finite relation evaluated at `b^(p^K)`.  Apply
`exists_integerRelation_prime_pow_dvd_teichmuller_of_not_linearIndependent` to obtain the growing
divisibility, then generalize the L1 positive-density zero-window/counting contradiction to close
`not_isRationallyJointNormal_of_not_linearIndependent`.
