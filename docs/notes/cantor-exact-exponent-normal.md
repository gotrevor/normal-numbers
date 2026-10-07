# Points of the middle-third Cantor set with prescribed irrationality exponent that are normal to every base prime to 3

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

**Abstract.**  For every rational `μ₀ > 2` there is a computable real `x` in the middle-third Cantor set `K` with irrationality exponent exactly `μ₀`.  This `x` is normal to every base `b ≥ 2` with `3 ∤ b`, and it is not normal to base 3.  Points of `K` with a prescribed exponent were already known (Bugeaud 2008), and so were points of `K` normal to bases prime to 3 (Cassels 1959, Schmidt 1960).  However, the known points with prescribed exponent are lacunary, and the known normal points have exponent 2.  The new ingredient is an elementary 3-adic counting step for the exponent upper bound, which avoids any count of rationals near `K`.  Everything is checked in Lean at commit [`9b3f636`](https://github.com/gotrevor/normal-numbers/tree/9b3f63619eb52dfae151618bbc0b728432064800), and the main theorem uses no cited results.

## Statement

**Theorem.**  Let `μ₀ > 2` be rational.  There is a computable `e : ℕ → Bool` such that `x = cantorExpReal μ₀ e` satisfies all of the following:

- `x` lies in `K` (Mathlib's `cantorSet`);
- `x` has irrationality exponent exactly `μ₀`;
- `x` is normal to every base `b ≥ 2` with `3 ∤ b`;
- `x` is not normal to base 3.

- [`exists_computable_mem_cantorSet_irrExponent_normal_all`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L1589).
- The irrationality exponent is [`HasIrrExponent`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponent.lean#L98) `x μ₀`: `LiouvilleWith p x` for every `p < μ₀` and for no `p > μ₀`, using Mathlib's `LiouvilleWith`.
- Normality is full block normality in base `b`.
- The almost-everywhere form of the exponent upper bound is [`ae_not_liouvilleWith_all`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L1560).

Bases divisible by 3 are settled below, given one cited theorem: the exponent decides which of them `x` is normal to.

## The construction

The ternary digits of `x` are `0` on forced runs `[a_k, ⌈μ₀ a_k⌉)`, where `a_0 = 4` and `a_{k+1} = (k+2)⌈μ₀ a_k⌉` ([`expRunStart`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponent.lean#L114)).  Every other digit is `2ω_i` for fair coins `ω`.  The digits are therefore all `0` or `2`, so `x ∈ K` ([`mem_cantorSet`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponent.lean#L136)).  Truncating `x` just before the `k`-th run gives `p/3^{a_k}` within about `3^{−μ₀ a_k}`, which makes the exponent at least `μ₀`.

## The upper bound

The exponent is at most `μ₀` provided that, for every `τ > μ₀`, only finitely many scales `m` have a rational `p/q` with `q ∈ [3ᵐ, 3^{m+1})` within `q^{−τ}` of `x`.  This follows from Borel–Cantelli once each scale-`m` event has coin mass decaying geometrically in `m`.  There are two kinds of window `(m, τm]` of ternary places.

- **Windows that do not enter a forced run: real Farey separation.**  Distinct fractions with denominators below `3^{m+1}` are more than `3^{−(2m+2)}` apart.  So all hitting points sharing their first `2m+3` digits approximate the *same* fraction, and their coins agree for a long stretch after that ([`hit_mass_farey`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L942)).
- **Windows that enter a run at place `b`: 3-adic Farey separation.**
  - Here the truncation is `P/3^b` followed by zeros, so a hit means `P q ≡ r (mod 3^b)` with `|r|` small.
  - Write `q = 3^v q₀` with `3 ∤ q₀`.  Two hits `(P, q, r)` and `(P', q', r')` whose numerators agree modulo `3^j` have a cross product `r₀q₀' − r₀'q₀` divisible by `3^j`.
  - Once `3^j` exceeds the size of that cross product, the cross product is 0 and `P ≡ P' (mod 3^c)` ([`padic_sep`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L1021)).
  - So within each class `v`, a hitting numerator is determined by about `2m + b − L − 2v` low digits and `v` top digits.
  - This bounds the **union** of bad numerators over all `(q, r)` at once, not the number of incidences.  The resulting mass is a power saving for every `τ > 2` ([`hit_mass_padic`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L1211)).

The case split ([`expTest_mass_le_all`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L1284)) uses the fact that the run lengths `E_k` are eventually at most `(μ₀−2)m/2` on the relevant windows.  Each window then costs at most `2^{12}·2^{−(μ₀−2)m/2}`.

**Normality and computability.**  Normality to bases prime to 3 is a Cassels-style second-moment bound for this coin measure; it is the same machinery as the repo's [Liouville note](bugeaud-10-37-cantor-liouville.md).  A conditional-expectation greedy algorithm then picks coins that satisfy the normality tests and avoid every scale test beyond a threshold ([`exists_computable_normal_avoid`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponent.lean#L1778)).  Non-normality to base 3 holds for every coin sequence, since the digit 1 never occurs ([`not_isNormal_three_cantorExpReal`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponent.lean#L255)).

## Why the simple count stops at `2 + log₂ 3`

Counting numerators one denominator at a time gives at most `O(2^{F})` Cantor numerators near each `p/q`, where `F` is the number of free places.  In a window that enters a run, only `≈ (τ−2)m` places are free.  The block cost `3ᵐ·2^{−(τ−2)m}` then decays only for `τ > 2 + log₂ 3 ≈ 3.585`.  That range is proved separately ([`CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponent.lean#L1800)).  Measure-level counts of rationals near `K` (Bugeaud–Durand; He–Liao, arXiv:2602.01307, Cor. 6.5) do not reach below `μ₀ = 3` either, because the relevant events lie below the cylinder scale.  The 3-adic step is what closes the range `2 < μ₀ ≤ 3.585`.

## The exponent decides the bases divisible by 3

**Theorem (given Baker's theorem).**  Let `μ₀ > 2` be rational.  There is a computable `e` such that `x = cantorExpReal μ₀ e` lies in `K`, has irrationality exponent exactly `μ₀`, and for every base `b = 3ˢt` with `3 ∤ t`:

`x` is normal to base `b`  ⟺  `t > 3^{s(μ₀−1)}`.

- [`exists_computable_normalProfile_of_baker`](https://github.com/gotrevor/normal-numbers/blob/8fd03703fbd6a516276391d4cd4ce3ec45623533/src/NormalNumbers/CantorExactExponentProfile.lean#L2480), with the condition [`ProfileOK`](https://github.com/gotrevor/normal-numbers/blob/8fd03703fbd6a516276391d4cd4ce3ec45623533/src/NormalNumbers/CantorExactExponentProfile.lean#L51).
- The case `s = 0` gives every base prime to 3, and the case `t = 1` excludes every power of 3, so the theorem above is contained in this one.
- Examples: for `μ₀ ∈ (2, 2.26)`, `x` is normal to bases 12, 15 and 21, and not to 6, 18 or 36.  Base 12 switches off at `μ₀ = 1 + log₃ 4`.
- The threshold is unchanged when `b` is replaced by a power of `b`, as it must be.  It is never attained for rational `μ₀`.

**Cited input.**  [`Literature.BakerLogDiscrepancyEff`](https://github.com/gotrevor/normal-numbers/blob/8fd03703fbd6a516276391d4cd4ce3ec45623533/src/NormalNumbers/CantorExactExponentProfile.lean#L1654) is a power-saving discrepancy bound for `{m log₃ t + β}`, uniform in the shift `β`.  It follows from Baker–Wüstholz (1993) for two logarithms together with the Erdős–Turán inequality.  The Lean statement asks for less than the literature gives; checking that transcription is the step most worth an expert's eye.

**Why the threshold.**  Both directions turn on the same window.
- *Not normal above the threshold, with no citation.*  Along a forced run, `x` is within `3^{−μ₀a}` of `P/3^a`, and `bʲP/3^a` is an integer once `sj ≥ a`.  So `x` has a base-`b` block of zeros of length proportional to `a`, which rules out normality.  This is [`not_isNormal_of_not_profileOK`](https://github.com/gotrevor/normal-numbers/blob/8fd03703fbd6a516276391d4cd4ce3ec45623533/src/NormalNumbers/CantorExactExponentProfile.lean#L142).
- *Normal below the threshold.*  The Fourier coefficient of the coin law at `h·bⁿ` sees only the ternary places `[sn, (s+log₃t)n]`.  A forced run can cover that window only above the threshold ([`window_covered_imp`](https://github.com/gotrevor/normal-numbers/blob/8fd03703fbd6a516276391d4cd4ce3ec45623533/src/NormalNumbers/CantorExactExponentProfile.lean#L283)).
  - Just past a run, the low digits of the frequency are hidden, and the visible top digits are governed by `{m log₃ t}`.  That is where the discrepancy input enters.
  - The case analysis ([`pair_classify_expl`](https://github.com/gotrevor/normal-numbers/blob/8fd03703fbd6a516276391d4cd4ce3ec45623533/src/NormalNumbers/CantorExactExponentProfile.lean#L776)) shows that in every pair term, either a free low window or a free top window survives.
- An elementary rate, from `tᵏ ≠ 3ʲ` alone, is too weak in those shadows.  A much weaker two-logarithm bound than Baker's would plausibly suffice, but this is not proved.

## A base-5 sibling, and open nodes

- **Base 5.**  Let `K₅` be the set of numbers whose base-5 digits lie in `{0,1,3,4}`.  For rational `μ₀ > 2 + log₄ 5 ≈ 3.161` there is a computable `x ∈ K₅` with exponent exactly `μ₀`, normal to every base prime to 5 and not normal to base 5 ([`exists_computable_mem_cantorFive_irrExponent_normal`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentFive.lean#L172)).
- **Open: the base-5 range `2 < μ₀ ≤ 3.161`** ([`StretchFive`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentFive.lean#L195)).  The 3-adic argument should port to 5-adic, but this has not been done.
- **Not a count of rationals near `K`.**  The 3-adic step gives a clean restricted-digit modular-hyperbola bound.  The number of `P ∈ C_b` with `P q ≡ r (mod 3^b)` for some `q ≤ Q` prime to 3 and `|r| ≤ R` is at most `2^j` whenever `2RQ < 3^j` ([`card_cantor_hyperbola_le`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/StretchBFR.lean#L192)).  Translated back, this is the trivial covering bound for rationals near `K`.  A power saving over that bound ([`NKPowerSaving`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/StretchBFR.lean#L220)) needs a Fourier-analytic input of Chow–Varjú–Yu type (arXiv:2402.18395) that this argument does not contain.

## Prior work and what is not claimed

- **In `K` with exact exponent.**  This part is known, and computably so.  Bugeaud (Math. Ann. 341, 2008) gives lacunary points `2Σ3^{−n_j}` of `K` with every exponent `μ ≥ 2`, and Becher–Bugeaud–Slaman (Proc. AMS 144, 2016, Thm 1) make them computable for computable limsup data.  Those points have digit density 0, so they are not normal in base 3, and their normality in other bases is not addressed.  The Lean file records that the exponent half of our theorem is the rational case of Bugeaud's ([`bugeaud2008_rational_of_stretch`](https://github.com/gotrevor/normal-numbers/blob/9b3f63619eb52dfae151618bbc0b728432064800/src/NormalNumbers/CantorExactExponentStretch.lean#L1618)).  Levesley–Salp–Velani (Math. Ann. 338, 2007) give explicit points of exact order `τ ≥ (3+√5)/2`.
- **Normal with exact exponent, outside `K`.**  Known: Bugeaud 2002 and Becher–Heiber–Slaman 2015 give absolutely normal Liouville numbers, and Kaufman's measures give exact-exponent sets of positive Fourier dimension.  These routes do not reach `K`, which supports no Rajchman measure.
- **In `K` and normal.**  Known only at exponent 2, for measure-typical points (Cassels, Schmidt, Hochman–Shmerkin, Dayan–Ganguly–Weiss, with Weiss 2001 for the exponent), and at exponent ∞ (the repo's [answer to Bugeaud's Problem 10.37](bugeaud-10-37-cantor-liouville.md)).
- **The separation principle itself is classical.**  The real case is the one-dimensional simplex lemma (Kristensen–Thorn–Velani 2006).  The 3-adic case is the non-archimedean gap principle (e.g. Bugeaud, INTEGERS 18 (2018), Lemma 1).  What we did not find in the literature is its use to bound the union of Cantor numerators at forced-run windows.
- **Limits of the search.**  We checked forward citations of Levesley–Salp–Velani, Becher–Bugeaud–Slaman, Allen–Chow–Yu, Dayan–Ganguly–Weiss, Hochman–Shmerkin, Fraser–Wheeler, Tan–Wang–Wu, Fishman–Simmons and Li–Velani–Wang, plus 2025–26 abstracts (He–Liao, Bandi, Lai–Xie, Manai).  Citer lists were screened by title and abstract only.  Slaman's 2019 lecture slides state a Becher–Slaman theorem combining simple normality to a prescribed set of bases with any exponent, but we could not locate its source paper or check whether it reaches `K`.  Corrections are welcome.
- **Not claimed:** irrational `μ₀`, the endpoint `μ₀ = 2`, the profile for bases divisible by 3 without the cited Baker input, a discrepancy rate, or an explicit program for `e` (the threshold is extracted non-constructively, though the witness is computable).

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 8fd03703fbd6a516276391d4cd4ce3ec45623533
lake exe cache get
lake build NormalNumbers.CantorExactExponentStretch NormalNumbers.CantorExactExponentFive NormalNumbers.StretchBFR NormalNumbers.CantorExactExponentProfile
```

Questions and corrections: please open an issue on this repository.
