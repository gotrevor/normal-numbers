# HANDOFF twopoint — laps 57–59, 2026-09-25: **`DelangeMean (1/2)` is UNCONDITIONAL**

Branch `wip/twopoint-avg`.  Working tree clean; every lap committed green (pre-commit `lake build`,
9296 jobs).  All new declarations `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
**No `sorry` introduced.**

## The headline

The previous wrap recorded the regime `‖t‖_{ℝ/ℤ} ≥ 1/6` as "not a technical gap": at `t = 1/2` the
Dirichlet series of `(−1)^{ω(n)}` is `ζ(s)·∏(1−2p^{-s}) ≈ 1/ζ(s)`, so `DelangeMean (1/2)` is of
Möbius/PNT strength, and Selberg–Delange or Halász was named as the route.  That was too pessimistic:

    delangeMean_half : DelangeMean (1 / 2)            -- TwoPointMoebiusPNT.lean, unconditional
    moebiusMeanZero  : MoebiusMeanZero                -- M(N) = o(N), in fact O(N / log N)

both proved from the *quantitative* PNT already in this tree, with NO contour integral written this
run.  `DelangeMean` is now a theorem on `‖t‖_{ℝ/ℤ} < 1/6` **and** at `t = 1/2`.

## The structural insight (the reason this worked)

For `z` on the unit circle, `z^ω` and the completely multiplicative `z^Ω` differ by a convolution
supported on POWERFUL numbers: `z^ω = z^Ω * k_z`, `k_z(p) = 0`, `k_z(p^j) = −z(z−1)` (`j ≥ 2`).  And
`z^Ω` reduces to Möbius by a FINITE convolution **exactly when `z = −1`**, because the exponent `w`
in `(1 − zX)^{-1}(1 − X)^w` is an integer only there:

    λ = 1_{squares} * μ  (ζ(2s)/ζ(s)),    λ^{-1} = 1_{squarefree},    (−1)^ω = λ * k .

So `t = 1/2` is the unique `t` outside `‖t‖ < 1/6` reachable by finite convolution from `μ`;
`b ≥ 3` genuinely needs `ζ(s)^z`.  **Recording that dichotomy is half the value of these laps.**

## Lap by lap

| lap | commit | result |
|---|---|---|
| 57 | `31a9ebe` | `TwoPointDelangeParity.lean`: `sum_conv_eq` (general hyperbola), **`kernelSum_tendsto_zero`** (the transfer engine: `∑‖k d‖/d < ∞`, `‖A n‖ ≤ n`, `A n = o(n)` ⟹ `∑_{d≤N} k d·A(N/d) = o(N)`), `sqIndA` + `isMultiplicative_sqIndA`, `liouville_mul_zeta`, **`sqIndA_mul_moebius`** (`λ = 1_{sq} * μ`), `MoebiusMeanZero`, `summable_sqIndA`, **`liouvilleMean_of_moebius`** (stage A). |
| 58a | `9304c89` | `omegaSignA`, `sqfreeIndA`, `mul_apply_prime_pow`, **`liouville_mul_sqfreeInd`** (`λ * 1_{sqfree} = 1`); toolbox `two_pow_omega_le_self`, `two_pow_omega_le_card_divisors`, **`summable_divisorCard`** (`∑ d(c)/c² < ∞`, via the hyperbola identity, no L-series). |
| 58b | `ad55d4c` | `kA`, **`liouville_mul_kA`** (`(−1)^ω = λ * k`), `kA_prime_pow`, `norm_kA_le`, `kA_eq_zero_of_not_powerful`; `IsPowerfulN`, **`exists_cube_sq_of_powerful`** (`n = a³c²`), `cubeSqParam`, **`summable_kA`**, `sum_omegaSign_eq`, **`omegaSignMean_of_moebius`** (stage B), `phase_half`, **`delangeMean_half_of_moebius`**. |
| 59 | (this) | `TwoPointMoebiusPNT.lean`: `moebiusLogA`, `moebiusLogA_mul_zeta`, **`moebiusLogA_eq`** (`μ(n)log n = −(μ*Λ)(n)`), `sum_moebius_mul_natDiv` (`∑_{d≤N} μ(d)⌊N/d⌋ = 1`), **`exists_sum_moebiusLog_le`**, `sum_log_div_le`, **`exists_abs_moebiusSum_log_le`** (`|M(N)| log N ≤ 1 + C·N`), **`moebiusMeanZero`**, **`delangeMean_half`**. |

Lap 59's three inputs, all already in tree and axiom-clean:
`ArithmeticFunction.sum_moebius_mul_log_eq` (mathlib), `DelangeSlot.exists_sum_abs_deltaN_le`
(`∑_{k≤N}|ψ(⌊N/k⌋)−⌊N/k⌋| ≤ C·N`, on `PNTPort.MediumPNT`), `log_factorial_ge`.

## NEXT SESSION — start here

1. **`DelangeMean (m/b)` for `b ≥ 3`, `‖m/b‖ ≥ 1/6`** (e.g. `t = 1/3, 2/5, 1/4`).  The finite-
   convolution route is now *provably* exhausted (see the dichotomy above), so the options are:
   (a) Selberg–Delange: `∑ z^{ω(n)}n^{-s} = ζ(s)^z G(s)`, needs `ζ^z` and a contour — `PNTPort`
       has the zero-free region (`ZetaZeroFree9`) and a Perron/Mellin toolkit
       (`MellinCalculus.lean`, `ResidueCalcOnRectangles.lean`), so this is a *long but mapped* road.
   (b) Halász over the same toolkit.
   (c) **Cheapest probe first**: the transfer engine now in `TwoPointDelangeParity.lean` reduces
       `DelangeMean t` to *any* summable-kernel factorisation of `z^ω` over a function whose
       partial sums are known `o(N)`.  For `z = e(m/b)` try `z^ω = f * k` with
       `f = ` the `b`-th-root twist `λ_b(n) := z^{Ω(n)}` and note
       `∏_{j=0}^{b−1} (z^{jΩ}) = 1_{b-th powers} * μ`-side identity `∏_j F_j = ζ(bs)`; a *single*
       `F_j` is not pinned by that product, but the identity may still yield a usable bound for the
       symmetrised sum.  Record the outcome either way.
2. **Reuse:** `kernelSum_tendsto_zero`, `summable_divisorCard`, `exists_cube_sq_of_powerful` and
   `moebiusMeanZero` are all general-purpose and should be cited, not re-derived.

## Confidence at wrap
- `DelangeMean t` on `‖t‖ < 1/6`: **DONE** (laps 53–56).  At `t = 1/2`: **DONE** (laps 57–59).
- `M(N) = o(N)` in this repo: **DONE** (lap 59), with the quantitative `O(N/log N)`.
- `DelangeMean t` for all `t ∉ ℤ`: **25%** (was 20%); the remaining cases are `b ≥ 3` with
  `‖m/b‖ ≥ 1/6` and they need `ζ(s)^z`, i.e. route (a)/(b) above.
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%** (untouched; the
  directive pins it as an equivalence with a named open problem).
