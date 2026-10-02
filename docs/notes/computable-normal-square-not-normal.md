# A computable normal number whose square is not normal

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Manai ([arXiv:2506.15422](https://arxiv.org/abs/2506.15422), §1) writes that "it would be very interesting to determine a normal number `x` such that `x²` is not normal".  In [arXiv:2508.09319](https://arxiv.org/abs/2508.09319) he asks for an explicit `x` in each of the classes `Ω_k`.  Existence of a normal `x` with `x²` not normal follows from Manai's [arXiv:2609.24665](https://arxiv.org/abs/2609.24665) Theorem 2, through a measure-theoretic argument that names no particular `x`.

This note records a **computable** example, proved in Lean at commit [`5b94540`](https://github.com/gotrevor/normal-numbers/tree/5b945408f75d251a6a238ce8b372fe32d9a124ad).  It rests on one cited theorem, stated as a hypothesis.

## The result

Let `e : ℕ → {0,1}` be a coin sequence, and let `y_e ∈ [1/2, 2/3]` have binary digits `1 0 e₀ 0 e₁ 0 e₂ 0 …`, i.e. a leading `1`, a `0` in every odd place, and the coins in the remaining even places ([`cantorDigits`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L57), [`cantorReal`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L61)).

**Theorem.**  Assume the Baker–Banaji decay theorem below.  Then there is a computable `e` such that `x = √(y_e)` is normal in base 2 while `x² = y_e` is not.

- [`exists_computable_normal_sq_not_normal`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L286).  "Computable" is Mathlib's `Computable` predicate on the coin sequence, the sense of Becher–Figueira's computable normal numbers.

**Why `x²` is not normal.**  No `y_e` contains the block `11`, since every other digit is `0` ([`not_isNormal_cantorReal`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L102)).  This holds for every coin sequence, so nothing needs to survive the derandomization.

## How `x` is made normal

1. **Fourier decay.**  Let `μ` be the law of `y_e` for fair coins, a self-similar measure.  By Baker–Banaji, the pushforward of `μ` under `√` has polynomial Fourier decay; `√` qualifies because it is `C²` with nonzero second derivative on `[1/2, 1]`.
2. **Almost every `√y` is normal.**  Polynomial decay bounds the second moment of the Weyl sums of `2ⁿ√y`.  Borel–Cantelli along squares then gives normality for `μ`-almost every coin sequence ([`ae_isNormal_of_polyDecay`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L209)).
3. **Derandomization.**  A conditional-expectation greedy algorithm chooses the coins one at a time.  It keeps the measure of the remaining good set positive against countably many explicit bad events, with summable measures ([`exists_computable_isNormal_sqrt_of_polyDecay`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L260)).  This follows the pattern of Becher–Figueira and Becher–Lew Deveali ([arXiv:2607.06773](https://arxiv.org/abs/2607.06773)).  Because the decay is uniform in the frequency, no residue counting is needed.

**Control.**  The same mechanism provably fails for affine maps: no rational affine map has polynomial decay here ([`not_polyDecay_rat_affine`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L224)).  So the argument uses the curvature of `√`, as it must, since rational affine images of normal numbers are normal.

## The cited input

[`BakerBanajiQuarterCantor`](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/src/NormalNumbers/ExplicitSquareNonNormal.lean#L168) specialises Baker–Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*, [arXiv:2401.01241](https://arxiv.org/abs/2401.01241) (Math. Ann. 392 (2025)), Corollary 1.5, to this measure.  The only non-verbatim step is an affine rescaling of the window from `[0,1]` to `[1/2, 1]`.  That step is needed because `√` is not `C²` at `0`.  A numeric check, averaging exactly over all `2²⁰` coin prefixes, shows the transform of the `√`-pushforward falling from about `0.18` at `ξ = 2⁸` to about `0.02` at `ξ = 2²⁰`.  The affine control `4t` stays at `0.6926` ([probe](https://github.com/gotrevor/normal-numbers/blob/5b945408f75d251a6a238ce8b372fe32d9a124ad/probes/bakerbanaji_sqrt_decay_probe.py)).

## What is not claimed

- A closed-form `x`.  The coins are computable, but Baker–Banaji's constants are not made explicit here.  Whether "computable" meets Manai's "determine" is his call.
- The other classes `Ω_k`, `k ≥ 3`, and their Hausdorff dimension.  These are under study here.
- Priority beyond our search.  We checked the newest versions of the papers above and their forward citations, and found no explicit example.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 5b945408f75d251a6a238ce8b372fe32d9a124ad
lake exe cache get
lake build NormalNumbers.ExplicitSquareNonNormal
```

Questions and corrections: please open an issue on this repository.
