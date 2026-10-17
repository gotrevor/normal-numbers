# Vandehey Theorem 5.1 lap 11: Claim 4.5 gcd identity proved

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovGcd` and imported it from
  `VandeheyProof.lean`, without changing the frozen `VandeheyThm51` definition or any consumer
  statement.
- Proved `gcd_pow_mul_sub_one_eq`, the local valuation engine for Vandehey's Claim 4.5:
  `gcd(b^(τ i)-1,m) = mbar * gcd(i,m/mbar)` whenever
  `mbar = gcd(b^τ-1,m)`, `mbar` and `m` have the same prime support, and the construction
  preserves `4`.
- Proved `gcd_pow_orderOf_sub_one_eq`, the paper-facing Claim 4.5 package with
  `τ = ord(b,m')`, and `gcd_pow_rounded_orderOf_sub_one_eq`, its exact specialization to the
  rounded divisor from equations (12)--(13).
- The scoped file still has exactly its single headline `sorry`; this lap advances the ordered
  Proposition 4.1 route and does not claim completion.

## Reflection audit

- **Source fidelity:** the production corollary states the exact gcd identity in Claim 4.5.  Its
  hypotheses are precisely the properties established for the paper's rounded divisor: divisibility,
  full prime support, and preservation of `4`.
- **Key simplification:** no separate proof of
  `v_p(b^τ-1) = v_p(mbar)` is needed.  Primewise, both saturated and unsaturated cases follow
  from `min(A+I,M) = min(A,M) + min(I,M-min(A,M))` after exact LTE.
- **Exceptional prime:** when `p=2` and `4 | m`, the rounded divisor supplies `4 | b^τ-1`, so
  the exact two-adic LTE theorem applies.  When `v₂(m)=1`, both sides' truncated valuations are
  forced directly to one.  Thus there is no hidden odd-modulus assumption.
- **Dependency graph:** rungs 1--4 are proved.  Within rung 5, Lemma 3.1, Lemmas 4.2--4.3,
  equations (12)--(13), and Claims 4.4--4.5 are proved.  The next unproved source statement is
  Claim 4.6.
- All three new declarations have exactly the standard trust-base axioms.  There is no new axiom,
  `native_decide`, heartbeat override, or hidden proof debt.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovGcd.lean`: passed.
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovGcd
  NormalNumbers.VandeheyProof`: `Build completed successfully (8931 jobs)`.
- A temporary axiom-check file importing the new module printed
  `[propext, Classical.choice, Quot.sound]` for `gcd_pow_mul_sub_one_eq`,
  `gcd_pow_orderOf_sub_one_eq`, and `gcd_pow_rounded_orderOf_sub_one_eq`.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.gcd_pow_rounded_orderOf_sub_one_eq`:
  axiom list `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
  src/NormalNumbers/VandeheyKorobovGcd.lean`: exactly the headline `sorry` in
  `VandeheyProof.lean`.

## Current blocker

Claim 4.6 remains: for `m'` the rounded divisor and
`mbar = gcd(b^ord(b,m')-1,m)`, prove `m / mbar | bigM b P`, hence
`m ≤ bigM b P * mbar`.  The local valuation machinery and Claim 4.4 maximality are now in
place; what remains is to relate the order-lifting threshold at each supported prime to the
definition of `bigM`, including the paper's doubled ambient order in equation (3).

## Next highest-value attack

Prove Claim 4.6 prime by prime.  For each `p | m/mbar`, use
`padicValNat_pow_sub_one_eq_add` and `m' | mbar` to bound the missing exponent by
`v_p(b^(2*ord(b,Q))-1)`, then assemble with `Nat.factorization_le_iff_dvd`.  Immediately feed
Claims 4.5--4.6 into the already-proved differencing inequality and the Lemmas 4.2--4.3 divisor
count to state and prove Proposition 4.1.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
