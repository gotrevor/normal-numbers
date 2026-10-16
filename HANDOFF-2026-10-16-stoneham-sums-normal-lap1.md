# Stoneham sums normal — lap 1 (2026-10-16)

## Concrete advance

The target `src/NormalNumbers/StonehamSumsNormal.lean` is reduced from three sorries to one,
without changing any ratified statement.

- Proved `vandeheyCor12_of_thm51`.  The proof follows Vandehey §6.1 exactly:
  - for `m ≤ N`, use the `k = 0` instance of `VandeheyThm51`;
  - for `m^ε ≤ N < m`, use `GrowingLocalizedLog.vandehey_window_bound`;
  - bound all possible differencing depths by `K = ⌈1/ε + 2⌉₊`, dominate their constants by a
    finite sum, and take `δ = min (1/2) (ε·2^{-(K+4)})`.
  This closes the only uncertain analytic derivation from the allowed cited input.
- Proved `isNormal_two_stoneham_three_add_five` as the explicit `r = 2`, `c = ![3,5]`,
  `m = ![1,1]`, `q = ![1,1]` specialization of Theorem A.
- Removed the two now-stale direct-sorry waivers for these declarations from `BarrierAudit.lean`;
  the audit retains only the waiver for the still-open Theorem A declaration.

## Verification

Run in this lap:

```text
lake env lean src/NormalNumbers/StonehamSumsNormal.lean
```

Result: success; the sole warning is the one remaining disclosed sorry in
`isNormal_stonehamCombination`.

Repository gate run:

```text
~/personal/bin/lean-green ~/src/nn-stoneham-sums --target NormalNumbers.StonehamSumsNormal
```

Result: `✅ FORMALIZE-TIER GREEN` (8762 jobs); the target module has exactly the one disclosed
Theorem A sorry.

An axiom scratch check printed:

```text
vandeheyCor12_of_thm51: [propext, Classical.choice, Quot.sound]
isNormal_two_stoneham_three_add_five: [propext, sorryAx, Classical.choice, Quot.sound]
```

The headline's `sorryAx` is precisely inherited from the remaining Theorem A obligation.

## Current blocker

The only remaining target obligation is `isNormal_stonehamCombination`.  It is not an external
or operator blocker; it is the elementary formalization bulk from paper §§3–5.  Corollary 1.2 is
now available in exactly the form needed for every long kick-free interval.

## Next highest-value attack

Formalize the proof engine below Theorem A, preferably as public namespaced helpers:

1. clear rational denominators and the part supported on primes dividing `b`, reducing every
   nonzero Weyl frequency to integer coefficients and a denominator coprime to `b`;
2. define `K_i(n)` and the rational truncated orbit state `S_n`;
3. prove the tail estimate and kick-free recurrence `S_{s+j}=b^jS_s`;
4. prove the reduced-denominator lower bound by the unique minimum `ℓ`-adic valuation of the newest
   term (pairwise coprimality is used only here);
5. cut `[⌈√N⌉,N)` at the at-most `r log₂ N` kicks, apply `VandeheyCor12` to long pieces, and finish
   via `equidistributed_of_weyl` plus `isNormal_iff_equidistributed_orbit`.

Do not revisit the analytic derivation unless its theorem fails an axiom audit; the narrow kernel
check is green.
