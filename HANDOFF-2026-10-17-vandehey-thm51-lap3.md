# Vandehey Theorem 5.1 lap 3: equation (5) proved; sparse Parseval interface repaired

## Concrete advance

- Proved kickoff rung 1, Vandehey Lemma 2.1 in its consumed equation-(5) form:
  `NormalNumbers.VandeheyKorobov.div_bigM_le_orderOf` is now sorry-free.
- Added the divisibility-strength local statements
  `prime_pow_excess_dvd_exponent_of_odd` and
  `two_pow_excess_dvd_exponent`.  For
  `q = 2 * orderOf (b : ZMod (primeProd P))` and
  `n = orderOf (b : ZMod m)`, they show that each excess factor
  `p^(v_p(m) - v_p(b^q - 1))` divides `n`.
- Aggregated those local factors without multiplying one copy of `n` per
  prime: distinct excess prime powers are pairwise coprime, so their product
  divides `n`; the complementary fixed factors form a subproduct of `bigM b P`.
  This proves `m <= bigM b P * n`, hence `m / bigM b P <= n`.
- Removed the discharged `div_bigM_le_orderOf` waiver from `BarrierAudit.lean`.
- Reflection found and repaired a rung-2 interface mismatch.  The earlier
  `norm_blockFourier_le_sqrt_of_orbit` is a valid dense lemma, but its
  coordinates are the initial interval `0, ..., H-1`; a multiplicative
  subgroup occupies arbitrary residues modulo `m`.  The new axiom-clean
  `norm_blockFourier_le_sqrt_of_orbit_l2` accepts a length-`K` vector with
  total squared mass `H`.  Taking `K = m` and extending a subgroup character
  by zero off the subgroup gives exactly the Parseval input needed by rung 2.

## Reflection audit

- Re-read the mounted primary source: Vandehey, Lemma 2.1 and equations
  (3)--(5), Proposition 4.1, and Theorem 5.1 with its page-14 recursion.
  The frozen `VandeheyThm51`, `alpha`, `expPair`, and `constPair` still match
  the published theorem.  Proposition 4.1 writes a `max(..., 1)` in its
  one-step `B'`; Theorem 5.1 publishes the displayed recursion without the
  max, as transcribed.  This is not a target discrepancy.
- The headline remains exactly
  `VandeheyProof.vandeheyThm51_holds : Literature.VandeheyDiff.VandeheyThm51`.
  Its three unconditional consumers are unchanged.  The only active sorry in
  the scoped target remains that headline proof.
- The repeated-route risk was now concrete: treating the cyclic powers of
  `b` as consecutive Fourier coordinates would not prove the subgroup sum.
  Future work should instantiate the sparse theorem, not return to the dense
  initial-interval lemma.

## Verification actually run

- `taskset -c 0-3 lake env lean -j 1 src/NormalNumbers/VandeheyKorobov.lean`
  -- passed after both the order proof and sparse Parseval theorem landed.
- `taskset -c 0-3 ~/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey \
    --target NormalNumbers.VandeheyProof \
    --axioms NormalNumbers.VandeheyKorobov.div_bigM_le_orderOf`
  -- `Build completed successfully (8924 jobs)`; the axiom list was exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- The first BarrierAudit gate attempt reached its last target and then hit the
  known rotating environment error `Too many open files`.  The required
  cached replay was run:
  `taskset -c 0-3 ~/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey \
    --target NormalNumbers.BarrierAudit \
    --axioms NormalNumbers.VandeheyKorobov.norm_blockFourier_le_sqrt_of_orbit_l2`
  -- `Build completed successfully (10365 jobs)`; BarrierAudit reported
  `34 barriers (26 proved, 6 cited, 2 frozen); 25 cruxes linked, 78 waived,
  105 open sorries scanned`; the sparse theorem's axiom list was exactly
  `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.

## Current blocker

Kickoff rung 2 is not yet a theorem about the actual cyclic subgroup.  One
must define the sparse coefficient vector on all `m` residues, prove its
squared mass is `tau = orderOf (b : ZMod m)`, and establish the eigen-relation
under multiplying the frequency by a power of `b`.  The old dense helper must
not be used for this instantiation.

## Next highest-value attack

State the twisted subgroup bound consumed by completion, then instantiate
`norm_blockFourier_le_sqrt_of_orbit_l2` as follows:

1. Enumerate the subgroup by `j : Fin tau` and the residue
   `(b^j : ZMod m).val`; prove injectivity from `j,k < tau` and minimality of
   `orderOf`.
2. Extend the character values by zero to a vector `Fin m -> C`; uniqueness of
   the power representative gives well-definedness and squared mass `tau`.
3. Use the `tau` frequencies `a * b^h (mod m)`.  They are distinct because
   both `a` and `b` are units; cyclic reindexing gives the constant-norm
   eigen-relation.
4. Apply the sparse Parseval lemma to obtain the `sqrt m` completed-sum bound,
   then prove the elementary Dirichlet-kernel L1 estimate needed for Vandehey
   Lemma 2.2.

Do not call `box done`: `VandeheyProof.lean` still contains its headline
`sorry`, so the host completion predicate is not met.
