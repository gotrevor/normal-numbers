# A Liouville number in the middle-third Cantor set that is normal to base 2 (Bugeaud, Problem 10.37)

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

Bugeaud, *Distribution modulo one and Diophantine approximation* (Cambridge Tracts 193, 2012), p. 219, Problem 10.37, asks to prove that the middle-third Cantor set `K` contains a Liouville number that is normal to base 2.

This note records a proof, checked in Lean at commit [`569bfdf`](https://github.com/gotrevor/normal-numbers/tree/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12).  It uses **no cited results**: the statement is in Mathlib's own vocabulary (`cantorSet`, `Liouville`) plus a definition of base-2 normality, and the proof depends only on Lean's standard axioms.  The number can moreover be taken computable, and normal to exactly the bases not divisible by 3.

## Statement

**Theorem.**  There is a computable `e : ℕ → Bool` such that `x = cantorLiouvilleReal e` lies in the middle-third Cantor set, is a Liouville number, and is normal to base 2.

- [`exists_computable_liouville_mem_cantorSet_isNormal_two`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L2371).
- The plain existence form is [`exists_liouville_mem_cantorSet_isNormal_two`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L1862), and the almost-everywhere form is [`ae_isNormal_two`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L1844).

## The construction

Take fair coins `ω`.  The ternary digit of `x` in place `i` is `2ω_i` at *free* places and `0` on the forced runs `[a_k, (k+2)a_k)`, where `a_0 = 4` and `a_{k+1} = 2(k+2)a_k` ([`cantorLiouvilleReal`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L122)).  The digits are `0` or `2`, so `x ∈ K`.  Truncating `x` just before the `k`-th run gives a rational `p/3^{a_k}` with `|x − p/3^{a_k}| < 3^{−(k+2)a_k}`, so `x` is Liouville as soon as infinitely many free digits are `2` ([`liouville_cantorLiouvilleReal`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L299)).

## Why base 2 works

The content is a second-moment bound in the style of Cassels (1959), proved for this measure with its long runs of forced zeros ([`secondMoment_le`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L1450)).  Let `F(N)` count the free places below `M = ⌊log₃ N⌋/2`.  Then for every nonzero integer `h`,

`𝔼 |Σ_{k<N} e(h 2ᵏ x)|² ≤ C N² (exp(−c F(N)) + N^{−1/2})`.

- **Fourier side.**  The Fourier transform of the law of `x` at a frequency `ξ` is bounded by a product of `|cos(2πξ/3^{p+1})|` over free places `p`.  A factor is at most `cos(π/9)` wherever consecutive ternary digits of `ξ` differ.
- **Arithmetic side.**  `2` is a primitive root modulo every power of `3` ([`orderOf_two_zmod_three_pow`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L464)).  So over a full period, the ternary digit changes of `c·2ʲ` are independent with probability `2/3` each.  This is an exact identity ([`sum_pow_changes`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L1237)).
- **Counting.**  The forced runs still leave `F(N) ≥ M/(2(log₂ M + 2))` free places.  The bound is therefore summable along the slowly growing sequence `⌊exp √j⌋ + j`, whose consecutive ratios tend to `1`.  A Davenport–Erdős–LeVeque argument along that sequence gives normality to base 2 for almost every `ω`.

**Computability.**  A conditional-expectation greedy algorithm picks the coins one at a time, driven directly by the second-moment bound along the slow sequence ([`exists_computable_normal_sched`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/SchedDerandomize.lean#L626)).

**Control.**  The same points are never normal to base 3, since they omit the digit `1` ([`not_isNormal_three_cantorLiouvilleReal`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L190)).  The proof sees this: the arithmetic step uses that `2` is a unit modulo `3`, and multiplication by `3` merely shifts ternary digits ([`tdig_mul_three_pow`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouville.lean#L432)).

## Every base at once

**Theorem.**  The same construction gives a computable `e` with `x = cantorLiouvilleReal e` in the Cantor set and Liouville, such that for every base `b ≥ 2`:

`x` is normal to base `b`  ⟺  `3 ∤ b`.

- [`exists_computable_liouville_mem_cantorSet_normalProfile`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L940); the almost-everywhere form is [`ae_normalProfile`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L854).  No cited results.
- **Bases prime to 3.**  The second-moment bound holds in base `b` with `t = v₃(b² − 1)` in place of the primitive-root fact ([`secondMoment_le_b`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L573)).  The powers of `b²` fill whole residue classes mod `3^t`, and lifting the exponent bounds the bad pairs ([`padicValNat_pow_sub_one_le`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L101)).  Only the constant changes.
- **Multiples of 3.**  Along each forced run, `x` is within `3^{−(k+2)a_k}` of a rational with denominator `3^{a_k}`.  So for most `j` in a long range, `{bʲx} < 1/b`, and `x` is not normal to any base divisible by 3 ([`not_isNormal_of_three_dvd`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L804)).

This differs from the typical Cantor point.  By Cassels (1959) and Schmidt (1960), almost every point for the Cantor measure is normal to every base that is not a power of 3, base 6 included ([`Cassels1959`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L72), cited only for contrast).  Our Liouville points are never normal to base 6 ([`not_isNormal_six`](https://github.com/gotrevor/normal-numbers/blob/569bfdf86ac6d012afec1b7fa34ad3a9925bfb12/src/NormalNumbers/CantorLiouvilleAll.lean#L850)).

## Every base that is not a power of 3

The zero runs above are what cost base 6.  A different construction recovers every base the Cantor measure allows.

**Theorem.**  There is a Liouville number `x` in the middle-third Cantor set such that for every base `b ≥ 2`:

`x` is normal to base `b`  ⟺  `b` is not a power of 3.

- [`liouvilleCantorFullProfile`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/CantorRepetition.lean#L7446), statement [`LiouvilleCantorFullProfile`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/CantorRepetition.lean#L68).  No cited results: `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.
- This is the most a point of `K` can do: its ternary digits avoid 1, so it is never normal to a power of 3.  It matches the Cassels–Schmidt profile of a typical Cantor point, now at exponent ∞.
- The witness comes from an almost-everywhere statement over coin sequences, so unlike the theorems above it is not claimed computable.

**Repetitions instead of zero runs.**  Instead of forcing a block of zeros, copy a free block `W` of length `ℓ` many times.  Then `x` is within `3^{−Mℓ}` of `W/(3^ℓ − 1)`, the digits stay in `{0, 2}`, and letting the copy count grow makes `x` Liouville.  The approximants have denominators prime to 3, so the base-`3ˢt` obstruction of the zero runs does not arise.

**The bases divisible by 3.**  Let `b = 3ˢt` with `t > 1` and `3 ∤ t`; base 6 is the first case.
- *Bases prime to 3 and powers of 3.*  These go as before ([`ae_isNormal_rep_of_coprime_three`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/CantorRepetition.lean#L536), [`not_isNormal_rep_three_pow`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/CantorRepetition.lean#L557)).
- *The second moment.*  In a copy region, a pair term is large only if a certain integer is cyclically sparse modulo `3^A − 1`, that is, if it has few nonzero ternary digits up to rotation.
- *Two sparse points of one orbit force an exact identity.*  Two such sparse points `y` and `tᵈy` give an identity `tᵈU = V` between sparse integers ([`cyclic_pair_identity`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/SparseIdentity.lean#L235)).
- *A 3-adic two-logarithm bound.*  The bound `v₃(tᵟa − b) ≤ C(t)(1 + log(δ+1))²(1 + log max(|a|,|b|))` ([`padicTwoLogs`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/PadicTwoLogsAssembly.lean#L295)) caps `d` in those identities ([`sparseIdentityBound_of_padic`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/SparseIdentity.lean#L1099)).  Sparse orbit points therefore cluster and are few.
  - The bound is of Bugeaud–Laurent type.  It is proved in Lean by Laurent's interpolation-determinant method, including the two-variable zero lemma ([`laurentZeroLemma`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/ZeroLemma.lean#L74)), so no linear-forms result is cited.
- *The shadow just past a copy region* needs no Baker input either ([`repPairArith_of_sparse`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/CantorRepetition.lean#L7283)).  The free digits and the copied digits there cannot both be large unless the same sparsity holds.

**Open.**  The finite-exponent version, a point of `K` with exponent exactly `μ₀` and the same profile ([`ExponentCantorFullProfile`](https://github.com/gotrevor/normal-numbers/blob/11b085cebae95c1d050361cd9d732092c216c261/src/NormalNumbers/CantorRepetition.lean#L73)), is stated but not proved.  Its upper bound on the exponent needs a count of approximants `p/(3^ℓ − 1)`, and the 3-adic count used for zero runs does not apply to them.

## Prior work and what is not claimed

- The method is Cassels's (1959), who showed that almost every point of `K` for the Cantor measure is normal to base 2.  What is new here is that the long forced zero-runs needed for the Liouville property leave enough free digits for the second moment, and that the result is checked in Lean.
- A Fourier-decay route is closed: `K` carries no measure whose Fourier transform tends to zero (Pramanik–Zhang, [arXiv:2408.03473](https://arxiv.org/abs/2408.03473)).  The sparse Cantor sets of Becher–Lew Deveali ([arXiv:2607.06773](https://arxiv.org/abs/2607.06773)) require free digits in every window, which excludes the runs.
- Priority beyond our search.  We checked forward citations of the papers above, Bluhm, Levesley–Salp–Velani, Bugeaud–Durand, Allen–Chow–Yu and Becher–Heiber–Slaman, plus web searches, and found no answer to Problem 10.37.  We could not full-text search all citers of the book.  Corrections are welcome.
- No discrepancy rate.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 569bfdf86ac6d012afec1b7fa34ad3a9925bfb12
lake exe cache get
lake build NormalNumbers.CantorLiouville NormalNumbers.CantorLiouvilleAll
```

For the theorem on every base that is not a power of 3:

```sh
git checkout 11b085cebae95c1d050361cd9d732092c216c261
lake exe cache get
lake build NormalNumbers.CantorRepetition
```

Questions and corrections: please open an issue on this repository.
