# Two explicit normal numbers: bounded partial quotients, and a reciprocal that is not normal

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Throughout, **normal** means absolutely normal (normal in every integer base `b ≥ 2`) unless a base is named, and **computable** means Mathlib's `Computable` predicate on a coin sequence `e : ℕ → Bool` that determines the number.  Both results are proved in Lean at commit [`89c88f7`](https://github.com/gotrevor/normal-numbers/tree/89c88f73eb6c54913d0d45eef2111afd730bdea4), and each rests on one cited Fourier-decay theorem stated as a hypothesis.

## 1. A computable normal number with all partial quotients in `{1, 2}`

Montgomery (*Ten Lectures on the Interface between Analytic Number Theory and Harmonic Analysis*, 1994, p. 203) asks for a normal number whose continued-fraction coefficients are bounded.  Existence is classical (Kaufman 1980; Queffélec–Ramaré 2003 for coefficients in `{1, 2}`), but Bugeaud (*Distribution modulo one and Diophantine approximation*, 2012, §7.7) writes that "no explicit example of such a number has been exhibited yet", and Queffélec ([math/0608249](https://arxiv.org/abs/math/0608249), §4) that "no explicit normal numbers in BAD have been constructed yet".

**Theorem.**  Assume the Fourier-decay theorem of Sahlsten–Stevens cited below.  Then there is a computable `e` such that `x = [0; 1+e₀, 1+e₁, 1+e₂, …]` is absolutely normal.  Every partial quotient of `x` is `1` or `2`, so `x` is badly approximable.

- [`exists_computable_absNormal_bad`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/BadNormal.lean#L504), with `x` = [`cfCoin`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/BadNormal.lean#L54).

**How.**  Under fair coins, `cfCoin` has the Bernoulli(1/2) law on the continued-fraction Cantor set `E_{1,2}`, which has polynomial Fourier decay (cited).  Decay bounds the second moments of Weyl sums in every base, so almost every point is normal.  A conditional-expectation greedy algorithm picks the coins one at a time and avoids countably many explicit bad events in all bases at once.  The rational convergents bracket each cylinder and give the exact approximations the algorithm needs ([`Abad_bounds`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/BadNormal.lean#L429)).  As a control, no point mass has polynomial decay ([`not_decay_const`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/BadNormal.lean#L519)), so the pipeline cannot be fed a single periodic continued fraction.

**Cited input.**  [`SahlstenStevensBernoulli12`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/BadNormal.lean#L490): T. Sahlsten, C. Stevens, *Fourier transform and expanding maps on Cantor sets*, Amer. J. Math. 146 (2024), Thm 1.1(2) ([arXiv:2009.01703](https://arxiv.org/abs/2009.01703)), specialised to this measure.  Two independent routes give the same decay: Jordan–Sahlsten, Math. Ann. 364 (2016), Thm 1.3(2), which needs `dim μ > 1/2` (here `dim μ = log 2/λ = 0.51496`, `λ = 1.34602`); and Baker–Banaji, Math. Ann. 392 (2025), Thm 1.2.

## 2. A computable normal `ξ` with `1/ξ` not normal

Bugeaud (2012, Ch. 10) attributes these to Rivoal: Problem 10.17 asks, for each base `b ≥ 2`, for an explicit `ξ > 0` that is simply normal (resp. normal) to base `b` with `1/ξ` not simply normal (resp. not normal) to base `b`.  Problem 10.18 asks for an explicit absolutely normal `ξ` with `1/ξ` not absolutely normal.  Existence follows from Manai ([arXiv:2609.24665](https://arxiv.org/abs/2609.24665), Thm 1.2).  Bergelson–Downarowicz ([arXiv:2506.12929](https://arxiv.org/abs/2506.12929), §8.6, Q1) ask whether the reciprocal of a normal number is always normal.

**Theorem A (10.18; 10.17 for `b = 2`).**  Assume Baker–Banaji's decay theorem (Cor. 1.5).  Then there is a computable `e` such that `ξ = 1/y_e` is absolutely normal, while `1/ξ = y_e` is not normal in base 2.  Here `y_e` has binary digits `1 0 e₀ 0 e₁ 0 …` and never contains the block `11`.

- [`exists_computable_absNormal_recip_not_normal`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/ReciprocalNormal.lean#L169).

**Theorem B (10.17, every base, both versions).**  Assume the same Baker–Banaji corollary for a sparse Cantor measure.  Then for every `b ≥ 2` there is a computable `e` such that `ξ` is absolutely normal while `1/ξ` is not even simply normal to base `b`.

- [`exists_computable_absNormal_recip_not_simplyNormal`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/ReciprocalNormal.lean#L460).  Here `1/ξ` = [`ySparse`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/ReciprocalNormal.lean#L199), whose base-`b` digit `0` has frequency at least `2/3` ([`not_isSimplyNormal_ySparse`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/ReciprocalNormal.lean#L241)).

**How.**  The same pipeline as result 1, with the map `t ↦ 1/t` on `[1/2, 1]` pushing forward a self-similar Cantor measure.  It is `C²` with second derivative between `2` and `16` ([`inv_bakerBanaji_hyp`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/ReciprocalNormal.lean#L52)), so Baker–Banaji give polynomial decay.  Theorem B is needed for simple normality at `b = 2`, because the derandomized coins in Theorem A could make some digit frequency degenerate.

**Cited inputs.**  Baker–Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*, Math. Ann. 392 (2025), Cor. 1.5 ([arXiv:2401.01241](https://arxiv.org/abs/2401.01241)), for the quarter-Cantor law (`BakerBanajiQuarterCantor`, shared with [our note on Manai's questions](computable-normal-square-not-normal.md)) and for the sparse law ([`BakerBanajiSparse`](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/src/NormalNumbers/ReciprocalNormal.lean#L227)).

## Checks on the cited inputs

Each cited input was compared with its source, quantifier by quantifier ([referee notes](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/docs/BAD-NORMAL-REFEREE-2026-10-03.md)).  A numeric check averages the Fourier transform of the `E_{1,2}` measure exactly over all `2²⁴` depth-24 cylinders.  Its maximum over each frequency band falls from `0.340` to `0.058` as `ξ` runs from `2⁶` to `2¹⁶`.  A point mass at `1/φ` stays at `1`, and the middle-third Cantor measure stays at `0.3714` along `ξ = 3^k` ([probe](https://github.com/gotrevor/normal-numbers/blob/89c88f73eb6c54913d0d45eef2111afd730bdea4/probes/sahlsten_stevens_cf12_probe.py)).  The transcriptions are the part most worth an expert's eye.

## What is not claimed

- Closed forms.  The coin sequences are computable, but the cited decay constants are not made explicit, so no running time is given.  Whether "computable" meets "explicit" is the askers' call.
- Novelty of the method.  Becher, Heiber and Slaman (2015) derandomize a decay measure in the same way to get a computable absolutely normal Liouville number; result 1 applies that approach to a different set.  It may be regarded as folklore.
- Priority beyond our search.  We checked forward citations of Jordan–Sahlsten, Sahlsten–Stevens, Hochman–Shmerkin and Manai's papers, Becher's publication list, two surveys, and web searches, and found neither construction.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 89c88f73eb6c54913d0d45eef2111afd730bdea4
lake exe cache get
lake build NormalNumbers.BadNormal NormalNumbers.ReciprocalNormal
```

Questions and corrections: please open an issue on this repository.
