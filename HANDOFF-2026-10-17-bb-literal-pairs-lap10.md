# Literal Bailey--Borwein pairs lap 10 -- global class slope separation (2026-10-17)

## Binding objective

Execute `KICKOFF-2026-10-17-bb-literal-pairs.md` in order. The host gate remains
`sorry-free:src/NormalNumbers/StonehamPairsNormal.lean`. Neither headline statement,
`VandeheyThm51`, nor any Theorem A statement in `StonehamSumsNormal.lean` changed. A diff from the
ratification commit `d590955e` still shows imports only in the target file. Its two original
headline sorries remain.

## Concrete crux advance

New module `StonehamPairsClasses.lean` proves the global normalized-slope separation requested by
lap 9 and Lemma 3' of the source.

- `StonehamPairMulDep` freezes the relevant class relation: positive powers of the bases agree.
- `stonehamPairMulDep_of_factorization_cross_eq` proves by unique factorization that, at a common
  prime, cross-proportionality of every factorization coordinate forces multiplicative dependence.
- `exists_prime_factorization_cross_ne_of_not_stonehamPairMulDep` gives a prime-support witness to
  the failure of proportionality for independent bases with overlapping support.
- `factorization_logSlope_ne_or_of_cross_ne` converts such a finite cross-product witness into an
  unequal logarithmic slope at one of the two primes.
- `exists_prime_logSlope_ne_of_not_stonehamPairMulDep` combines overlapping and exclusive prime
  support. For every independent pair `c1,c2 >= 2`, it produces `p | c1*c2` with
  `factorization(c1,p) * log c2 != factorization(c2,p) * log c1`. This is exactly the global
  normalized-slope lemma left open by lap 9.
- `natLog_mul_log_base_error` proves the quantitative floor bridge
  `0 <= log n - Nat.log c n * log c < log c`. Thus each integral entered depth differs from its
  real logarithmic model by a fixed one-digit error.

The target imports the new module. No new `sorry`, axiom, native computation, statement change, or
heartbeat override was introduced.

## Verification

Narrow checks:

```text
lake env lean src/NormalNumbers/StonehamPairsClasses.lean
lake build NormalNumbers.StonehamPairsClasses
lake env lean src/NormalNumbers/StonehamPairsNormal.lean
```

All passed. The new module's direct Lean check has no warnings; the target reports only its two
unchanged headline sorries.

Real target/axiom gate:

```text
~/personal/bin/lean-green /Users/gotrevor/src/nn-bb-pairs \
  --target NormalNumbers.StonehamPairsNormal \
  --import NormalNumbers.StonehamPairsClasses \
  --axioms NormalNumbers.StonehamPairsNormal.stonehamPairMulDep_of_factorization_cross_eq \
  --axioms NormalNumbers.StonehamPairsNormal.exists_prime_factorization_cross_ne_of_not_stonehamPairMulDep \
  --axioms NormalNumbers.StonehamPairsNormal.exists_prime_logSlope_ne_of_not_stonehamPairMulDep \
  --axioms NormalNumbers.StonehamPairsNormal.natLog_mul_log_base_error
```

It completed 8,778 jobs and ended `FORMALIZE-TIER GREEN`. All four audited declarations print
exactly `[Classical.choice, Quot.sound, propext]`.

## Current blocker

The distinct-class arithmetic now lacks only packaging, not a class-theory idea. For the prime
returned by `exists_prime_logSlope_ne_of_not_stonehamPairMulDep`, combine the two instances of
`natLog_mul_log_base_error` with the nonzero slope to prove an eventual estimate

```text
rho * log n <= |factorization(c1,p) * Nat.log c1 n
                    - factorization(c2,p) * Nat.log c2 n|
```

for some fixed `rho > 0`. Exponentiating gives a positive power of `p` in the uncancelled part of
the common denominator. Use lap 9's exact minimum-valuation theorem and
`stonehamPairFamilies_eq_cleared_div` to turn that into `StonehamStateDenPowerLower` for the
distinct-class branch.

The same-class branch is unchanged: align `c_i = g^s_i` at primitive `g`-depth, compress the
eventually periodic combined tail, and use the already-proved never-silent/resultant machinery.

## Next highest-value attack

Prove the explicit eventual integral-depth gap described above, preferably first as a standalone
absolute-value inequality with a fixed error `(factorization c1 p + factorization c2 p) *
log c1 * log c2`. Immediately feed it through `padicValInt_pairCleared_*_eq_min_of_depth_ne` and
the rational denominator bridge, so the entire distinct-class branch becomes a
`StonehamStateDenPowerLower` theorem before returning to same-class compression.
