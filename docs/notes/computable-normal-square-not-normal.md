# Manai's classes `Ω_k`: a computable normal `x` with `x²` not normal, and `Ω_k ≠ ∅` for every `k`

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Throughout, **normal** means absolutely normal: normal in every integer base `b ≥ 2`, as in Manai's papers.

Manai ([arXiv:2506.15422](https://arxiv.org/abs/2506.15422), §1) writes that "it would be very interesting to determine a normal number `x` such that `x²` is not normal".  In [arXiv:2508.09319](https://arxiv.org/abs/2508.09319) he defines `deg_an(x)`, the least degree `k ≥ 1` of an integer polynomial `p` with `p(x)` not normal.  He sets `Ω_k = {x : deg_an(x) = k}`, notes that it "is not even known whether `Ω_k ≠ ∅`", and asks for explicit points of `Ω_k` and for the Hausdorff dimension of `Ω_k`.

This note records two results, proved in Lean at commit [`74227a3`](https://github.com/gotrevor/normal-numbers/tree/74227a3f12abad4a83bbeb17d96163dac3398a02).  Each rests on one cited theorem of Baker–Banaji, stated as a hypothesis.

## The construction

Let `e : ℕ → {0,1}` be a coin sequence, and let `y_e ∈ [1/2, 2/3]` have binary digits `1 0 e₀ 0 e₁ 0 e₂ 0 …`, i.e. a leading `1`, a `0` in every odd place, and the coins in the remaining even places ([`cantorReal`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitSquareNonNormal.lean#L61)).  No `y_e` contains the block `11`, so no `y_e` is normal, for any choice of coins ([`not_isNormal_cantorReal`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitSquareNonNormal.lean#L102)).  The candidate points of `Ω_k` are `x = y_e^{1/k}`, whose `k`-th power `y_e` is not normal.

## 1. A computable point of `Ω₂`

**Theorem.**  Assume Baker–Banaji's decay theorem (Corollary 1.5).  Then there is a computable coin sequence `e` such that `x = √(y_e)` is absolutely normal and lies in `Ω₂`.  That is, `qx + r` is normal for every rational `q ≠ 0` and every `r`, while `x² = y_e` is not normal.

- [`exists_computable_mem_Omega_two`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L171).  "Computable" is Mathlib's `Computable` predicate on the coin sequence, the sense of Becher–Figueira's computable absolutely normal number.  The definitions [`degAn`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L83) and [`Omega`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L88) transcribe Manai's Definition `def:deg`.

**How.**
1. **Fourier decay.**  By Baker–Banaji, the pushforward under `√` of the coin measure `μ` (a self-similar measure) has polynomial Fourier decay.
2. **Almost every `√y` is normal.**  The decay bounds the second moment of Weyl sums of `bⁿ√y` in each base `b`, and Borel–Cantelli does the rest.
3. **Derandomization.**  A conditional-expectation greedy algorithm picks the coins one at a time, avoiding countably many explicit bad events across all bases at once ([`exists_computable_isAbsNormal_sqrt_of_polyDecay`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L164)).  This follows the pattern of Becher–Figueira and Becher–Lew Deveali ([arXiv:2607.06773](https://arxiv.org/abs/2607.06773)).  Degree-1 images are then normal by Wall's theorem.

**Control.**  The decay step provably fails for rational affine maps ([`not_polyDecay_rat_affine`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitSquareNonNormal.lean#L224)).  So the argument uses the curvature of `√`, as it must.

## 2. `Ω_k ≠ ∅` for every `k ≥ 2`

**Theorem.**  Assume Baker–Banaji's corollary for analytic maps (Corollary 2.10 of arXiv v2).  Then for every `k ≥ 2` and almost every coin sequence, `y_e^{1/k} ∈ Ω_k`.  In particular, `Ω_k` is nonempty.

- [`ae_mem_Omega`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L279), [`Omega_nonempty`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L294).

**How.**  For an integer polynomial `p` with `1 ≤ deg p < k`, the map `G_p(t) = p(t^{1/k})` is analytic near `[1/2, 1]` and not affine: the exponents `0, 1/k, …, deg p/k` and `1` are distinct.  Baker–Banaji's analytic corollary then makes `G_p(y)` normal for almost every `y`.  There are countably many `p`, so almost every `y` works for all of them at once, while `(y^{1/k})^k = y` is not normal.

For `k ≥ 3` the inflection points of the `G_p` are dense, so no single cylinder avoids them all.  The analytic corollary handles this, but the `C²` version with `F'' ≠ 0` throughout, which Manai quotes, does not.

## The cited inputs

Both specialise Baker–Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*, [arXiv:2401.01241](https://arxiv.org/abs/2401.01241) (Math. Ann. 392 (2025)), to the law of `y_e`.

- [`BakerBanajiQuarterCantor`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitSquareNonNormal.lean#L168) is Corollary 1.5, used for result 1.
- [`BakerBanajiAnalyticQuarterCantor`](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/src/NormalNumbers/ExplicitOmegaK.lean#L261) is Corollary 2.10, Property (A) with `qₙ = bⁿ`, used for result 2.

The only non-verbatim step is an affine rescaling of the window from `[0,1]` to `[1/2, 1]`.  It is needed because `√` is not `C²` at `0`.

A numeric check, averaging exactly over all `2²⁰` coin prefixes, shows the transform of the `√`-pushforward falling from about `0.18` at `ξ = 2⁸` to about `0.02` at `ξ = 2²⁰`, while the affine control `4t` stays at `0.6926` ([probe](https://github.com/gotrevor/normal-numbers/blob/74227a3f12abad4a83bbeb17d96163dac3398a02/probes/bakerbanaji_sqrt_decay_probe.py)).  These transcriptions are the part most worth an expert's eye.

## What is not claimed

- A closed-form `x`.  The coins are computable, but Baker–Banaji's constants are not made explicit here.  Whether "computable" meets Manai's "determine" is his call.
- An explicit (computable) point of `Ω_k` for `k ≥ 3`, and the Hausdorff dimension of `Ω_k`.  Both are stated in the same file and under study.
- Priority beyond our search.  We checked the newest versions of the papers above and their forward citations, and found no explicit example and no statement that `Ω_k ≠ ∅`.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 74227a3f12abad4a83bbeb17d96163dac3398a02
lake exe cache get
lake build NormalNumbers.ExplicitOmegaK
```

Questions and corrections: please open an issue on this repository.
