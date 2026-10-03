# Manai's questions on normality under polynomials: a computable point of every `Ω_k`, `dim_H Ω_k = 1`, and one `x` for each `Q`

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Throughout, **normal** means absolutely normal: normal in every integer base `b ≥ 2`, as in Manai's papers.

Manai ([arXiv:2506.15422](https://arxiv.org/abs/2506.15422), §1) writes that "it would be very interesting to determine a normal number `x` such that `x²` is not normal".  In [arXiv:2508.09319](https://arxiv.org/abs/2508.09319) he defines `deg_an(x)`, the least degree `k ≥ 1` of an integer polynomial `p` with `p(x)` not normal.  He sets `Ω_k = {x : deg_an(x) = k}`, notes that it "is not even known whether `Ω_k ≠ ∅`", and asks for explicit points of `Ω_k` and for the Hausdorff dimension of `Ω_k`.  In [arXiv:2606.08325](https://arxiv.org/abs/2606.08325) §1.1 he asks for an algorithm producing `x` with `P(x)` normal and `Q(x)` not normal, for given polynomials `P` and `Q`.

This note records three results, proved in Lean at commit [`c37faa2`](https://github.com/gotrevor/normal-numbers/tree/c37faa26c53a74069cfcf577ce3a85cc425ae44c).  Each rests on one cited theorem of Baker–Banaji, stated as a hypothesis.

## The construction

Let `e : ℕ → {0,1}` be a coin sequence, and let `y_e ∈ [1/2, 2/3]` have binary digits `1 0 e₀ 0 e₁ 0 e₂ 0 …`, i.e. a leading `1`, a `0` in every odd place, and the coins in the remaining even places ([`cantorReal`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitSquareNonNormal.lean#L63)).  No `y_e` contains the block `11`, so no `y_e` is normal, for any choice of coins ([`not_isNormal_cantorReal`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitSquareNonNormal.lean#L104)).  The candidate points of `Ω_k` are `x = y_e^{1/k}`, whose `k`-th power `y_e` is not normal.

## 1. A computable point of `Ω_k`, for every `k ≥ 2`

**Theorem.**  Assume Baker–Banaji's decay theorem with its explicit constant (Corollary 1.5).  Then for every `k ≥ 2` there is a computable coin sequence `e` with `y_e^{1/k} ∈ Ω_k`.  That is, `p(y_e^{1/k})` is normal for every integer polynomial `p` with `1 ≤ deg p < k`, while `(y_e^{1/k})^k = y_e` is not normal.

- [`exists_computable_mem_Omega`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L1884).  "Computable" is Mathlib's `Computable` predicate on the coin sequence, the sense of Becher–Figueira's computable absolutely normal number.  The definitions [`degAn`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L87) and [`Omega`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L92) transcribe Manai's Definition `def:deg`.
- The case `k = 2`, `x = √(y_e)`, answers the question from 2506.15422 quoted above, and needs only a weaker form of the cited input ([`exists_computable_mem_Omega_two`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L175)).

**How.**
1. **Fourier decay.**  For each `p`, the map `G_p(t) = p(t^{1/k})` pushes the coin measure `μ` (a self-similar measure) forward to a measure with polynomial Fourier decay, with constants computable from `p` ([`polyDecay_Gk`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L1157)).  For `k = 2` Baker–Banaji apply directly.  For `k ≥ 3`, `G_p''` can vanish inside the window, and the inflection points of the various `G_p` are dense, so no single interval avoids them all.  We cut the measure into cylinders of depth `m`.  On the cylinders far from the at most `k − 2` near-zeros of `G_p''`, Baker–Banaji's explicit constant gives decay; the cylinders near them carry little mass ([`pushFourier_le_of_deriv2_lower`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L1061)).  The cut uses only a lower bound `|G_p''(t)| ≥ c_k ∏|t − z_i|` ([`deriv2_Gk_lower`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L417)), so the zeros never need to be located.
2. **Almost every point works.**  The decay bounds the second moment of the Weyl sums of `bⁿ G_p(y)` in each base `b`, and Borel–Cantelli does the rest.
3. **Derandomization.**  A conditional-expectation greedy algorithm picks the coins one at a time, avoiding countably many explicit bad events across all `p` and all bases at once ([`exists_computable_absNormal_family`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L1237)).  This follows the pattern of Becher–Figueira and Becher–Lew Deveali ([arXiv:2607.06773](https://arxiv.org/abs/2607.06773)).

**Controls.**  The decay step provably fails for rational affine maps ([`not_polyDecay_rat_affine`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitSquareNonNormal.lean#L226)), and the hypothesis of the cut provably fails for affine maps and for `G_{X^k}(t) = t` ([`not_deriv2_lower_of_deriv2_eq_zero`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L578), [`not_deriv2_lower_Gk_X_pow`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L596)).  So the argument uses curvature, as it must.

## 2. `dim_H Ω_k = 1` for every `k ≥ 2`

**Theorem.**  Assume Baker–Banaji's corollary for analytic maps and self-similar measures (Corollary 2.10 of arXiv v2).  Then `Ω_k` has Hausdorff dimension `1` for every `k ≥ 2`.

- [`dimH_Omega_eq_one`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L2100), with the measures and the mass distribution principle in [`DigitCantor`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/DigitCantor.lean).

**How.**  For a base `b ≥ 3`, let `z` have independent base-`b` digits uniform on `{0, …, b − 2}`, and let `ν_b` be the law of `y = 1/2 + z/2`, a self-similar measure on the window `[1/2, 1]`.  Every such `z` omits the digit `b − 1`, so `y` is not normal in base `b`.  For an integer polynomial `p` with `1 ≤ deg p < k`, the map `G_p` is analytic near the window and not affine, so Baker–Banaji's analytic corollary makes `G_p(y)` normal for `ν_b`-almost every `y`.  There are countably many `p`, so `ν_b`-almost every `y` has `y^{1/k} ∈ Ω_k` (the same argument for the coin measure is [`ae_mem_Omega`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L283)).  A set of diameter below `b^{-(n+1)}/2` has `ν_b`-mass at most `(b − 1)^{-n}`, so by the mass distribution principle every `ν_b`-full set has dimension at least `log(b − 1)/log b`.  The map `t ↦ t^{1/k}` is bi-Lipschitz on the window, so `dim_H Ω_k ≥ log(b − 1)/log b`, which tends to `1`.

## 3. One computable `x` for each `Q`

**Theorem.**  Assume Baker–Banaji's decay theorem with its explicit constant (as in result 1).  Let `Q` be a nonconstant integer polynomial.  Then there is a computable real `x` such that `Q(x)` is not normal, and, for every integer polynomial `P`,

`P(x)` is absolutely normal  ⟺  `P` is not of the form `αQ + β` with `α, β ∈ ℚ`.

- [`exists_computable_PQ`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L2421), with [`AffineIn`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L71) for "`P = αQ + β`".  Both `x` and its coin sequence are computable.
- The implication ⇐ is the whole content.  ⇒ is Wall's theorem: a rational affine image of the non-normal `Q(x)` is not normal ([`not_isAbsNormal_of_affineIn`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L122)).  So the answer is sharp, and one `x` serves every admissible `P` at once.
- The almost-everywhere form, from the analytic corollary, is [`exists_PQ_of_analytic`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L2451).

**How.**  Pick a natural `u` with `|Q'| ≥ 1` on `[u, ∞)`, so `Q` is invertible on the window `[u+1, u+2]`.  Set `x = Q⁻¹(a + c·y_e)` with integers `a, c ≠ 0` chosen so that `a + c·y` runs over `Q([u+1, u+2])` as `y` runs over `[1/2, 1]`.  Then `Q(x) = a + c·y_e` is not normal, and `P(x) = G_P(y_e)` with `G_P = P ∘ Q⁻¹ ∘ (a + c·)`.  The curvature of `G_P` is controlled by the Wronskian-type polynomial `W_P = P''Q' − P'Q''` ([`wPoly`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L75)), which vanishes identically exactly when `P = αQ + β`.  Otherwise `|G_P''| ≥ c_P ∏|t − z_i|` on the window ([`deriv2_GP_lower`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L684)), and the cylinder cut of result 1 gives decay ([`pushFourier_le_of_deriv2_lower_unif`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L950)).

The degree of `W_P` is unbounded as `P` varies, so the decay exponent shrinks with `P` and no single exponent serves the whole family.  The derandomizer is therefore run with a separate exponent for each `P` ([`exists_computable_absNormal_family_var`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/FamilyDerandomizeVar.lean#L26)).

**A refuted step.**  The first plan approximated `G_P` to precision `2^{-D}` from `D` coin digits.  That is false: for `Q = X + 512(X−1)⁹` and `P = X` it fails at `D = 4` ([`not_approxGPfamClaim`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L1200)).  The proof uses a renormalized family instead ([`approx_GPfam2`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitPQ.lean#L2054)).

**Prior work.**  For a single pair `(P, Q)`, the mechanism appears in Manai, [arXiv:2609.24665](https://arxiv.org/abs/2609.24665), in the proof of Thm. 1.3 (§4.1, the local inverse `g(r + sY)`).  Run with `f = Q ∘ P⁻¹`, that argument gives, almost surely along a Bernoulli measure, an `x` with `P(x)` absolutely normal and `Q(x)` not normal.  Manai does not state this consequence.  New here are a computable `x`, and a single `x` for all `P` at once, with the exact characterization above.

## The cited inputs

All specialise Baker–Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*, [arXiv:2401.01241](https://arxiv.org/abs/2401.01241) (Math. Ann. 392 (2025)).

- [`BakerBanajiUniformQuarterCantor`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L318) is Corollary 1.5 with its explicit constant `C(1 + max|F'| + (max|F'|)^{-κ} + max|F''|)(1 + (min|F''|)^{-κ})`, for the law of `y_e`; used for results 1 and 3.  The case `k = 2` needs only [`BakerBanajiQuarterCantor`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitSquareNonNormal.lean#L170), the same corollary for `F = √` alone.
- [`BakerBanajiAnalytic`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L1910) is Corollary 2.10, Property (A) with `qₙ = bⁿ`, for any finite self-similar measure on the window ([`IsSelfSimilarOnWindow`](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/src/NormalNumbers/ExplicitOmegaK.lean#L1897)); used for result 2.

The only non-verbatim step is an affine rescaling of the window from `[0,1]` to `[1/2, 1]`.  It is needed because `t^{1/k}` is not `C²` at `0`.

Numeric checks average the Fourier transform exactly over all coin or digit prefixes.  For the `√`-pushforward of the coin measure it falls from about `0.18` at `ξ = 2⁸` to about `0.02` at `ξ = 2²⁰`, while the affine control `4t` stays at `0.6926` ([probe](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/probes/bakerbanaji_sqrt_decay_probe.py)).  For `ν_4` it falls from `2.3·10⁻²` at `ξ = 4⁴` to `6.2·10⁻⁴` at `ξ = 4¹⁰`, while the affine control stays at `0.31533` ([probe](https://github.com/gotrevor/normal-numbers/blob/c37faa26c53a74069cfcf577ce3a85cc425ae44c/probes/bakerbanaji_nuL_probe.py)).  These transcriptions are the part most worth an expert's eye.

## What is not claimed

- A closed-form `x`.  The coins are computable, but Baker–Banaji's constants `C, η, κ` are not made explicit here, so no running time is given.  Whether "computable" meets Manai's "determine" is his call.
- Positive Hausdorff measure, or anything finer than dimension, for `Ω_k`.
- Priority beyond our search.  We checked the newest versions of the papers above and their forward citations, and found no explicit point of any `Ω_k`, no statement that `Ω_k ≠ ∅`, no dimension result, and no computable or all-`P` form of result 3.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout c37faa26c53a74069cfcf577ce3a85cc425ae44c
lake exe cache get
lake build NormalNumbers.ExplicitOmegaK NormalNumbers.ExplicitPQ
```

Questions and corrections: please open an issue on this repository.
