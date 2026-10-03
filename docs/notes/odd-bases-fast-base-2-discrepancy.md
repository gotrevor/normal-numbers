# Normal in base 2 and every odd base, with base-2 discrepancy O((log N)²/N)

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

For a real `x` and base `b`, let `D*_N` be the star discrepancy of `{x}, {bx}, …, {b^{N−1}x}`.  A number normal in one base can have `D*_N = O((log N)²/N)` (Levin 1999).  For numbers normal in many bases at once, the known constructions give much worse rates.  Aistleitner, Becher, Scheerer and Slaman ([arXiv:1707.02628](https://arxiv.org/abs/1707.02628)) describe `N^{−1/2}` as a barrier for absolutely normal numbers, and quote Bugeaud's question on how small the discrepancy of an absolutely normal number can be.

This note records a partial step, proved in Lean at commit [`519325e`](https://github.com/gotrevor/normal-numbers/tree/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4) from two cited results.

## Statement

**Theorem.**  Assume Levin's theorem and a lemma of Becher–Lew Deveali, both cited below.  Then there is a real `x` that is normal in every odd base `b ≥ 3` and in every power of `2`, and whose base-2 discrepancy satisfies `D*_N ≤ C (log N)² / N` for all `N ≥ 2`.

- [`exists_levinRate_oddNormal`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L1707), with discrepancy as in [`DiscLe`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L260).

So in base 2 this `x` has the best known rate for a single base, while also being normal in infinitely many other bases.

**What it is not.**  `x` is not shown to be absolutely normal: bases such as 6, 10 and 12 are out of reach of this construction.  Only base 2 carries a rate, and the odd bases are normal without one.  So this does not beat the `N^{−1/2}` barrier in the sense of 1707.02628, which asks for a rate in every base.  That stronger statement is recorded as an open target ([`exists_absNormal_base2_fast`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L1815), not proved).

## Construction

`x = α + y`, where `α` is Levin's number and `y` is a point of the sparse Cantor set of Becher–Lew Deveali ([arXiv:2607.06773](https://arxiv.org/abs/2607.06773)), with free binary digits only at the positions `⌈e^{j/100}⌉` ([`expSet`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L295), [`bldPoint`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L284)).

- **Base 2.**  Up to `N` the set `y` has `O(log N)` nonzero binary digits.  Since `{2ⁿ(α+y)}` is `{2ⁿα}` shifted mod 1 by `{2ⁿy}`, and that shift is tiny except near those few positions, the discrepancy changes by `O((log N)²/N)` ([`discLe_fract_add`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L350)).  Carries cause no trouble.
- **Odd bases.**  Becher–Lew Deveali bound the relevant cosine products for the law of `y` in odd bases.  Their bound uses only absolute values, so it survives translation by `α`.  A second-moment argument then makes `α + y` normal in every odd base for almost every `y` ([`bld_doubleSum_le`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L1278), [`ae_isNormal_odd_add`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L1469)).
- **Powers of 2** follow from base 2.

**Computable choice.**  For computable `α` (Levin's is), a derandomization picks a computable `y` with `α + y` normal in every odd base ([`exists_computable_bld_odd_add`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L4153)).

**Control.**  The base-2 estimate is useless for a dense perturbation ([`perturbBudget_dense_ge_one`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L1753)), and some dense `y` makes `α + y` an integer ([`exists_not_isNormal_two_dense`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L1778)).  So the sparsity is doing the work.

## Cited inputs

- [`Levin1999`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L309): M. B. Levin, *On the discrepancy estimate of normal numbers*, Acta Arith. 88 (1999), Theorem 2, with `q = 2`.
- [`BLDLemma5`](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/src/NormalNumbers/LevinSparse.lean#L321): Becher–Lew Deveali, arXiv:2607.06773, Lemma 5, with the thresholds from their Lemmas 1, 3 and 4.  It covers odd bases.  The step taken from the proof of their Lemma 7 (the cosine double sum) is proved in Lean, not cited.

Both were compared with the sources quantifier by quantifier ([referee notes](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/docs/LEVIN-SPARSE-REFEREE-2026-10-03.md)).  A numeric check up to `N = 2²⁰` ([probe](https://github.com/gotrevor/normal-numbers/blob/519325e9e5ee392eedaf7f4fc5e3f70de7847ec4/probes/levin_sparse_probe.py)) uses Levin's exact `α`.  It shows `N·D*_N/(log N)²` staying between `0.1` and `0.25` for `α` and between `0.5` and `1.1` for `α + y`.  A dense perturbation drives it to `4.4`, and the Champernowne control grows to `193`.

## Prior work

We found no statement of this result.  We checked forward citations of 1707.02628, 1510.02004, 1511.03582 and 2607.06773, Levin's papers, Becher's and Scheerer's work, and web searches.  The closest is a qualitative sparse-perturbation argument in Manai [arXiv:2609.24665](https://arxiv.org/abs/2609.24665), with no rates.  The method is simple once the two inputs are in hand, so it may be known to experts.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 519325e9e5ee392eedaf7f4fc5e3f70de7847ec4
lake exe cache get
lake build NormalNumbers.LevinSparse
```

Questions and corrections: please open an issue on this repository.
