# Vandehey Theorem 5.1 lap 10: Claim 4.4 and exact local LTE proved

## Concrete advance

- Added the sorry-free module `NormalNumbers.VandeheyKorobovOrders` and imported it from
  `VandeheyProof.lean` without changing the frozen `VandeheyThm51` definition or any consumer
  statement.
- Proved `orderOf_gcd_pow_sub_one_eq_and_maximal`, Vandehey's Claim 4.4.  If
  `τ = ord(b,m')` and `mbar = gcd(b^τ - 1,m)`, then `ord(b,mbar) = τ`; moreover every
  divisor `D | m` on which `b` has order `τ` divides `mbar`.  This is the paper's "largest
  divisor" conclusion in the divisibility form needed by Claim 4.5.
- Proved `padicValNat_pow_sub_one_eq_add`, the exact local order-lifting interface exposed by
  lap 9.  For prime `p | x-1`, `p ∤ x`, and `n > 0`, it gives
  `v_p(x^n-1) = v_p(x-1) + v_p(n)`.  The theorem includes `p=2` under the precise extra
  condition `4 | x-1`; its proof uses mathlib's all-exponents two-adic LTE theorem.  This is
  exactly why equation (12)'s rounded divisor preserves `4 | m`.
- The scoped file still has exactly its single headline `sorry`; this lap advances the ordered
  Proposition 4.1 route and does not claim completion.

## Reflection audit

- **Source fidelity:** Claim 4.4 is rendered literally, except that "largest" is strengthened
  from a numerical comparison to the source-equivalent divisibility property.  No hypothesis
  or constant in the frozen Theorem 5.1 statement changed.
- **Why the LTE lemma is load-bearing:** Claim 4.5 needs to turn
  `mbar*d | b^(iτ)-1` into `d | i` prime by prime.  Taking `x=b^τ`, the new lemma gives the
  exact valuation increment.  The preserved factor `4` handles the sole exceptional branch.
- **Dependency graph:** rungs 1--4 are proved.  Within rung 5, Lemma 3.1, Lemmas 4.2--4.3,
  equations (12)--(13), Claim 4.4, and the exact local LTE engine for Claims 4.5--4.6 are proved.
  The next unproved source statement is Claim 4.5.
- Both new declarations have exactly the standard trust-base axioms.  There is no new axiom,
  `native_decide`, heartbeat override, or hidden proof debt.

## Verification actually run

- `taskset -c 0 lake env lean -j 1 src/NormalNumbers/VandeheyKorobovOrders.lean`: passed during
  iteration.
- `taskset -c 0-3 lake build NormalNumbers.VandeheyKorobovOrders
  NormalNumbers.VandeheyProof`: `Build completed successfully (8930 jobs)`.
- A temporary axiom-check file importing the new module printed
  `[propext, Classical.choice, Quot.sound]` for both
  `padicValNat_pow_sub_one_eq_add` and `orderOf_gcd_pow_sub_one_eq_and_maximal`.
- `taskset -c 0-3 /Users/gotrevor/personal/bin/lean-green
  /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof
  --axioms NormalNumbers.VandeheyKorobov.orderOf_gcd_pow_sub_one_eq_and_maximal`:
  axiom list `[Classical.choice, Quot.sound, propext]`; final verdict
  `FORMALIZE-TIER GREEN`.
- `git diff --check`: passed.
- `rg -n '\bsorry\b' src/NormalNumbers/VandeheyProof.lean
  src/NormalNumbers/VandeheyKorobovOrders.lean`: exactly the headline `sorry` in
  `VandeheyProof.lean`.

## Current blocker

Claim 4.5 remains to be packaged globally.  The mathematical core is now present, but the proof
must do careful factorization bookkeeping: for each prime in `d | m/mbar`, show
`v_p(b^τ-1) = v_p(mbar)` from the gcd definition and the fact that `mbar*d | m`, then apply
`padicValNat_pow_sub_one_eq_add` to obtain
`mbar*d | b^(iτ)-1 ↔ d | i`.  The `p=2` premise must be discharged from
`four_dvd_roundedDivisor` and `m' | mbar`, not assumed globally when the modulus is only even.

## Next highest-value attack

Prove the factorization lemma for `mbar = gcd(b^τ-1,m)` at primes dividing `m/mbar`, then
assemble the prime-power divisibility equivalence above as Claim 4.5.  Immediately derive the
paper's gcd identity
`gcd(b^(iτ)-1,m) = mbar * gcd(i,m/mbar)`.  With that exact interface in hand, use Claim 4.4
and the already-proved equation-(5) machinery to discharge Claim 4.6.

Do not call `box done`: `src/NormalNumbers/VandeheyProof.lean` is not yet sorry-free.
