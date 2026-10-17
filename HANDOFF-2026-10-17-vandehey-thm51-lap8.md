# Vandehey Theorem 5.1 lap 8: Lemma 4.3 proved

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovCounting` and wired it into
  `VandeheyProof.lean`.
- `coprime_Ico_count_le` proves the one-shift Legendre estimate for integers in `[1,X)`:

  `#{i in [1,X) : gcd(i,q)=1} <= (X/q) * phi(q) + 2^omega(q)`.

- `gcd_Ico_count_le` reduces the general gcd class to coprimality after dividing by `d`,
  while retaining the paper's exact main term `(X/n) * phi(n/d)` rather than losing a
  boundary block.
- `gcd_Ico_count_le_two_pow` is Vandehey's Lemma 4.3 in the stated form: if `d | n` and
  `n` has at most `s` distinct prime factors, then

  `#{i in [1,X) : gcd(i,n)=d} <= (X/n) * phi(n/d) + 2^s`.

- The proof is self-contained over the existing Korobov imports.  A first attempt to reuse
  `PrimeModelRadicalCRT.legendre_sieve_count` was rejected because importing that large,
  unrelated application module crossed Lean's import-server file limit in the direct harness.
  The production proof instead specializes the same finite inclusion-exclusion argument:
  each squarefree-divisor count is exactly `floor(X/e)`, each floor contributes at most one,
  and the errors sum over the powerset to `2^omega(q)`.
- The frozen `VandeheyThm51` definition and all consumer statements remain unchanged.  The
  scoped file still has exactly its single headline `sorry`.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 ScratchLemma43.lean` (before promotion): passed; the
  scratch file was moved into the production module.
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovCounting
  NormalNumbers.VandeheyProof`: `Build completed successfully (8928 jobs)`.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.gcd_Ico_count_le_two_pow`:
  axiom list `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
  src/NormalNumbers/VandeheyKorobovCounting.lean`: exactly the headline `sorry` in
  `VandeheyProof.lean`.
- `git diff -- src/NormalNumbers/LiteratureVandeheyDifferencing.lean
  src/NormalNumbers/VandeheyProof.lean`: only the new proof-module import differs; the
  frozen declarations are intact.

## Current blocker

Kickoff rung 5 still needs the rest of Proposition 4.1.  Lemmas 3.1, 4.2, and 4.3 are now
available.  The immediate missing construction is the supported rounded divisor `m'` from
equations (12)--(13): it must divide `m`, have the same prime support, preserve the exceptional
`4 | m` condition, and satisfy the two-sided real-power bounds with the exact factor `2Q`.
After that come Claims 4.4--4.6 and the analytic divisor-sum assembly.

## Next highest-value attack

Formalize equations (12)--(13) in a new imported module.  Define the rounded exponent of each
`p in m.primeFactors` as `floor (x * factorization m p)`, with the paper's `max(_,1)` correction
at `p=2` when `4 | m`, and multiply by the radical `Q`.  First prove support equality,
divisibility, and preservation of `4 | m`; then prove

`m^x <= m' <= 2 * Q * m^x`

for `0 < x < 1`.  This is the route-decisive input to Claim 4.4 and the exact Proposition 4.1
constants.  Do not call `box done`: the scoped `VandeheyProof.lean` headline remains open.
