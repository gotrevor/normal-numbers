# Vandehey Theorem 5.1 lap 1: order interface and Parseval--orbit core

## Concrete advance

- Added `src/NormalNumbers/VandeheyKorobov.lean`, imported by the scoped target
  `VandeheyProof.lean`.
- Froze kickoff rung 1 as
  `NormalNumbers.VandeheyKorobov.div_bigM_le_orderOf`, faithfully stating Vandehey's equation (5)
  with the prime-support and coprimality hypotheses.  Its prime-power lifting proof remains an
  explicit `sorry`.
- Proved the analytic core of kickoff rung 2 as
  `NormalNumbers.VandeheyKorobov.norm_blockFourier_le_sqrt_of_orbit`.  It derives the sharp
  `sqrt T` bound from exact finite Parseval, an injective orbit of `H` frequencies, unit-modulus
  coefficients, and constancy of the Fourier norm on that orbit.  This is the
  Parseval--orbit step needed for the twisted subgroup sum; no Gauss-sum input is used.

## Verification actually run

- `lake env lean src/NormalNumbers/VandeheyKorobov.lean` — passed, with only the disclosed rung-1
  `sorry` warning.
- `~/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof`
  — `Build completed successfully (8924 jobs)` and final verdict `FORMALIZE-TIER GREEN`.
- `~/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target NormalNumbers.BarrierAudit`
  — `Build completed successfully (10365 jobs)`, the audit scanned 106 open sorries, and the final
  verdict was `FORMALIZE-TIER GREEN`.  The new rung-1 leaf has an explicit waiver in
  `BarrierAudit.lean`.

## Current blocker

The primary target `VandeheyProof.vandeheyThm51_holds` is still open.  Per the kickoff's required
order, the immediate blocker is rung 1: prove `div_bigM_le_orderOf`.  The missing arithmetic is a
simultaneous prime-power order lower bound.  For odd primes, the useful local model is
`GrowingLocalizedLog.factor_two_le`, which already demonstrates the repository's working API for
`padicValNat.pow_sub_pow`; the general-base result must also isolate and prove the exceptional
2-adic branch from Vandehey Lemma 2.1 rather than silently applying odd-prime LTE.

## Next highest-value attack

1. Factor `m` over `P` and prove the local prime-power inequality
   `p^t / p^beta' <= orderOf (b : ZMod (p^t))`, splitting odd `p` from `p = 2`.
2. Combine local orders through the CRT/lcm description of `orderOf` modulo `m` to finish
   `div_bigM_le_orderOf`.
3. Only then continue rung 2: enumerate `H = <b>` by powers, instantiate
   `norm_blockFourier_le_sqrt_of_orbit`, and prove the character eigen-relation
   `T(a h) = conj(psi h) T(a)` plus injectivity of the unit orbit.

Do not call `box done`: the scoped file still contains its original `sorry`, and the required
headline axiom checks therefore cannot yet pass.
