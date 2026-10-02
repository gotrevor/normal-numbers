# Erdős Problem #257: new cases, checked in Lean

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

[Erdős Problem #257](https://www.erdosproblems.com/257) asks: for an infinite set `A ⊆ ℕ`, is

$$\sum_{n \in A} \frac{1}{2^n - 1}$$

irrational?  Known cases include `A = ℕ` (Erdős 1948), pairwise coprime `A` with `Σ 1/a < ∞` (Erdős 1968), and the primes (Tao–Teräväinen, [arXiv:2512.01739](https://arxiv.org/abs/2512.01739)); the problem page has the full list.

This note records three results from this repository.  Each is a Lean theorem, linked below at commit [`3ca852b`](https://github.com/gotrevor/normal-numbers/tree/3ca852ba99210294b9d3c8b8aec171afd00a67ed).  Two are unconditional; one rests on a single cited input, stated as a hypothesis, which is the part we would most like checked.

## The identity behind all three

For a set `S` of primes, let `ω_S(n)` count the prime divisors of `n` that lie in `S`.  Then

$$\sum_{n \ge 1} \frac{\omega_S(n)}{b^n} = \sum_{p \in S} \frac{1}{b^p - 1},$$

and at `b = 2^k` the right side is the #257 sum over `A = k·S = {kp : p ∈ S}`.  So #257 for `k·S` is a question about the base-`2^k` digits of the left side ([`subsetLambert_two_pow_eq`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257.lean#L52)).

**Mertens rate.**  `S` has a Mertens rate if there are `c > 0` and `C` with `Σ_{p<N, p∈S} 1/p ≥ c·log log N − C` for all `N ≥ 2` ([`MertensRate`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/G4MertensAP.lean#L59)).  All primes qualify, and so do the primes in any residue class `a mod q` with `gcd(a, q) = 1`.

## 1. `A = k·S` with `k ≥ 2` (unconditional)

**Theorem.**  Let `k ≥ 2` and let `S` be a set of primes with a Mertens rate.  Then `Σ_{n∈k·S} 1/(2ⁿ − 1)` is irrational.  In fact its base-`2^k` expansion contains every finite word (it is disjunctive).

- [`erdos257_kMul`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257.lean#L224): the general statement.
- [`erdos257_kMul_primes`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257.lean#L232): `A = {kp : p prime}`.
- [`erdos257_kMul_residueClass`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257.lean#L237): `A = {kp : p ≡ a mod q}`.

The engine is [`isDisjunctive_subsetLambert`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/G4SubsetAssembly.lean#L136): `Σ ω_S(n)/bⁿ` is disjunctive in every base `b ≥ 3`.  The dilation `k ≥ 2` is exactly what moves the #257 sum into a base `2^k ≥ 4`.

**Normality at `k = 2`.**  If `Σ_{p∈S} 1/p` diverges while `Σ_{√N<p≤N, p∈S} 1/p → 0`, then `Σ_{n∈2·S} 1/(2ⁿ − 1)` is normal in base 2 ([`erdos257_twoMul_normal`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257.lean#L245)).

## 2. `A = S`, a set of primes, at base 2 (conditional on one cited input)

**Theorem.**  Assume the hypothesis `TTEquidistributedDyadic` below.  Let `S` be a set of primes with a Mertens rate.  Then `Σ_{p∈S} 1/(2ᵖ − 1)` is disjunctive in base 2, hence irrational.

- [`isDisjunctive_subsetLambert_two`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257Base2.lean#L529): disjunctivity.
- [`erdos257_primeSubset`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257Base2.lean#L544): #257 for `A = S`.
- [`erdos257_residueClass`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/Erdos257Base2.lean#L551): `A` = the primes `≡ a mod q`.

For `S` = all primes, irrationality is Tao–Teräväinen's theorem.  Disjunctivity is stronger, and we did not find it stated.  For proper subsets, Tao–Teräväinen §1 write that their arguments "can also treat other sets `A` that are sufficiently similar to the primes, but we do not pursue this question here."

**The cited input.**  [`TTEquidistributedDyadic`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/LiteratureTTEquidistributedDefect.lean#L62) is a form of Tao–Teräväinen Theorem 3.1(i), their two-point correlation estimate in the equidistributed case.  It is **not** a verbatim transcription.  We restate their conclusion as a bound on the number of exceptional dyadic scales, and that step replaces their exponent `c` by `c/4`; the derivation is in the docstring.  This is the step most worth an expert's eye.  (An earlier, more literal transcription turned out to be vacuous; that is recorded as the theorem `ttEquidistributedCorrelation_trivially_true` in the same file.)

## 3. `A = ℕ`: the binary digits of `E` (unconditional)

**Theorem.**  Every binary word appears infinitely often in the binary expansion of the Erdős–Borwein constant `E = Σ_{n≥1} 1/(2ⁿ − 1)`.  This answers the question in Campbell, [arXiv:2605.24160](https://arxiv.org/abs/2605.24160) §4.

- [`campbellEQuestion_holds`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/CampbellAnswer.lean#L132), for the statement [`CampbellEQuestion`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/LiteratureCampbell.lean#L33).
- Quantitatively, for each `ε > 0` a fixed word starts at `≥ N^{1−ε}` of the first `N` positions once `N` is large ([`jointWords_power_count`](https://github.com/gotrevor/normal-numbers/blob/3ca852ba99210294b9d3c8b8aec171afd00a67ed/src/NormalNumbers/JointLambertQuantitative.lean#L180)).

The same statement appears, conditionally on two analytic inputs, in [CaptainSude/erdos-borwein-disjunctivity](https://github.com/CaptainSude/erdos-borwein-disjunctivity) by a different method.

## What is not claimed

- #257 for an arbitrary infinite `A`, or for every infinite set of primes.  The second is in progress here.
- Priority beyond our search.  We checked the problem page and its forum thread, `google-deepmind/formal-conjectures` with its open PRs, and recent arXiv, and found none of the above stated.  Corrections are welcome.

## Checking it

```sh
git clone https://github.com/gotrevor/normal-numbers && cd normal-numbers
git checkout 3ca852ba99210294b9d3c8b8aec171afd00a67ed
lake exe cache get
lake build NormalNumbers.Erdos257 NormalNumbers.Erdos257Base2 NormalNumbers.CampbellAnswer
```

Questions and corrections: please open an issue on this repository.
