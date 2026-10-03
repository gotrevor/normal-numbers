# Bergelson–Downarowicz's questions on deterministic numbers: two answers

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Bergelson and Downarowicz, *On preservation of normality and determinism under arithmetic operations* ([arXiv:2506.12929](https://arxiv.org/abs/2506.12929)), call a real number **deterministic** in base `r` if its digit sequence has zero entropy (their Def. 3.5).  Equivalently, for every `ε > 0` there is a block length `m` such that, outside a set of positions of upper density at most `ε`, every length-`m` block of the digits comes from a family of fewer than `2^{εm}` blocks (Def. 3.6 and 3.8, equivalence by Thm. 3.9).  Their §8.6 lists open problems, including:

> 2. Is the reciprocal of a nonzero deterministic number always deterministic?
>
> 4. Can any nonzero real number be represented as (i) the product, (ii) the ratio, or (iii) the product of reciprocals, of two deterministic numbers?

This note records that the answer to both is no, with Lean proofs at commit [`8de7b8a`](https://github.com/gotrevor/normal-numbers/tree/8de7b8a43e44ff8df87c27071058a51b36636289).  The answer to question 4 is unconditional.  The answer to question 2 uses two results from the same paper, stated as hypotheses.  The definition is transcribed as [`IsDeterministic`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L72) (via [`IsDeterministicSeq`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L65)), in any base `b ≥ 2`.

## Question 4: no, for products, ratios and reciprocal products (unconditional)

**Theorem.**  For every base `b ≥ 2`, the set of products `xy` of two numbers deterministic in base `b` has Hausdorff dimension `0`, and so has Lebesgue measure `0`.  The same holds for ratios `x/y` and for products of reciprocals `1/(xy)`.  In particular, almost every nonzero real is none of these.

- [`not_productQuestion`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L867), [`not_ratioQuestion`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L873), [`not_recipProductQuestion`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L879).
- The dimension statements: [`dimH_detProducts`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L790) and its two siblings.  The measure statements: [`volume_detProducts`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L855) and its siblings.

**How.**
1. **Deterministic numbers have packing dimension `0`.**  For each `ε > 0` they form a countable union of sets that, at every sufficiently fine scale `b^{-N}`, meet at most `b^{εN}` of the `b`-adic intervals of length `b^{-N}` ([`deterministic_subexp_cover`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L627)).  The count is the definition at work.  A length-`N` prefix is fixed by the at most `(ε + δ)N` exceptional positions, whose choice costs a binomial-entropy factor, and by the blocks from the small family everywhere else.
2. **A product of two such sets is small.**  At scale `b^{-N}`, `A × B` is covered by at most `b^{2εN}` squares, so `dim_H(A × B) ≤ 2ε` ([`dimH_prod_le_of_subexp`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L685)).
3. **Assembly.**  Multiplication and division are locally Lipschitz away from `0`, so they do not raise Hausdorff dimension.  Take a countable union and let `ε → 0`.

**Why the count matters.**  Hausdorff dimension `0` alone would not be enough.  The Liouville numbers have Hausdorff dimension `0`, yet every nonzero real is a product of two of them (Erdős 1962).  This is recorded as [`not_dimH_prod_zero_of_dimH_zero`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L891), from [`Erdos1962Product`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L212) and [`DimHZero`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L219).  The proof uses the every-scale (packing-type) count, which Liouville numbers lack.

## Question 2: no (from two results of the same paper)

**Theorem.**  Assume (a) the base-2 deterministic numbers are closed under subtraction (B-D Cor. 4.11(2)), and (b) some base-2 deterministic `s` has `s²` not deterministic (B-D Cor. 8.15).  Then some nonzero deterministic `y` has `1/y` not deterministic.

- [`exists_deterministic_inv_not_deterministic`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L267), [`not_reciprocalQuestion`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L274); the inputs are [`DetSub`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L156) and [`DetSqNotDet`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L161).

**How.**  `s² + s` is not deterministic, since otherwise `s² = (s² + s) − s` would be.  If `1/s` and `1/(s+1)` were both deterministic, then so would be their difference `1/(s(s+1))`, whose reciprocal `s² + s` is not.  So one of `s`, `s + 1`, `1/(s(s+1))` is a deterministic number with a non-deterministic reciprocal ([`hua_witness`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L233)).

Fact (b) also follows from Manai ([arXiv:2606.08325](https://arxiv.org/abs/2606.08325), Cor. 1.4), by a route recorded as [`detSqNotDet_of_manai`](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/src/NormalNumbers/DeterministicBD.lean#L338).  One probabilistic step of that route is still open in Lean.  It is not needed for the theorem above.

Given B-D's own results, the argument is short.  We record it because the question is listed as open.

## What is not claimed

- That the representable sets are empty or countable.  Only dimension `0`, hence measure `0`, is proved.
- Priority beyond our search.  We checked the paper (still at v1) and the papers citing it, and found neither question answered.  Corrections are welcome.

The transcriptions of B-D's definitions and of the two cited results are the part most worth an expert's eye ([referee notes](https://github.com/gotrevor/normal-numbers/blob/8de7b8a43e44ff8df87c27071058a51b36636289/docs/BERGELSON-DOWNAROWICZ-REFEREE-2026-10-03.md)).

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 8de7b8a43e44ff8df87c27071058a51b36636289
lake exe cache get
lake build NormalNumbers.DeterministicBD
```

Questions and corrections: please open an issue on this repository.
