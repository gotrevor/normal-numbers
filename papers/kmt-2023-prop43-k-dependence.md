# KMT 2023 Prop 4.3: the k-dependence of its constant, leg by leg (2026-09-20)

Source: Klurman–Mangerel–Teräväinen, *On Elliott's conjecture and applications*, arXiv 2304.05344,
§4 (Props 4.3, 4.4, eqs (4.6)–(4.25)).  Companion to KB verdict §4e; this note is the re-run the
block construction needs.  Shifts `a_j = 1, h_j = j` (j = 1..k), `χ_j = 1`, `t_j = 0`.

## What the sparse-𝒫 theorem needs

`G4WiringSparse.lean`: `exists_sparse_normal_of_KMT_quant' (C) (hgrow : log C k / 4^k → 0) (hKMT : KMT_quant C)`.
`KMT_quant C` is Prop 4.3 with one constant `C J` in front of all three terms
`√log(1/ε)·√(2 S_𝒫(x^ε,x)) + exp(−S_𝒫(x^ε)) + exp(−1/(8J²ε))`.  So the *Lean* shape demands
`log C(k) = o(4^k)` for the constant multiplying **every** leg, including the sieve leg.

## The legs of the proof and what each costs

| leg | where | multiplies | constant |
|---|---|---|---|
| Step 1 (t_j = 0) | (4.4)–(4.5) | all | absolute (t = 0) |
| Step 2 e-tuple truncation | (4.7): `z^{−9/(10k)}·(∏_{p|A}(1−p^{−1/(10k)})^{−1})^k`, z = (log x)^{1/(3k)} | third term (absorbed via ε ≥ 1/log log x into exp(−1/(4k²ε)); this is where the k² in the exponent comes from) | `exp(k Σ_{p<k} −log(1−p^{−1/(10k)})) = exp(O(k²))` |
| Step 2 main-term tuple sum | (4.6): `Σ_{e_j | A^∞} 1/[e_1..e_k]` | first two terms | lcm-tuple sum ≈ ∏_{p<k} Σ_m p^{−m}((m+1)^k − m^k) = exp(≈0.6 k²) (numerically, k = 4..64; KB §4e) |
| (4.16)–(4.18) Cauchy–Schwarz + Mertens on [x^ε, x] | first term | absolute |
| **(4.20) smooth-number truncation d_j ≤ x^{1/(4k)}** | third term | **O(k) after the re-run below** (the paper's literal `≪ exp(−1/(2ε))` costs `exp(≈e^{4k}/(2e))`) |
| (4.22) fundamental lemma, dimension κ = k | third term | **unverified**: IK Lemma 6.3's implied constant depends on κ (and on K in Ω(κ), K = exp(O(k/log k)) here) |
| Lemma 4.5 / (4.25) dimension-k Mertens | first two terms | exp(O(k/log k)) |

## The (4.20) re-run

The truncation error is `≪ x · u₀^{−u₀/2+5/2} · (log x/log y)` with `u₀ = 1/(4kε) − 5` (Dickman
`ρ(u) ≪ u^{−u/2}` at `u ≥ u₀`, then Selberg's sieve for the e-sum, `log x/log y = 1/ε`), valid when
the smooth-numbers-in-AP input applies, i.e. `x^{1/(4k)} ≥ y^{10}`, i.e. `ε ≤ 1/(40k)`.

*Literal reading.*  The paper says this is `≪ x exp(−1/(2ε))`, "say".  With `1/ε = 4k(u₀+5)` the
ratio of the two sides is `exp(2k u₀ + 10k − (u₀/2) log u₀ + (5/2) log u₀ + log(1/ε))`, maximised at
`log u₀ = 4k − 1` with value `≈ e^{4k−1}/2`.  So the implied constant, taken literally, is
`exp(≈ e^{4k}/(2e))`: doubly exponential in k, and `log C(k) = o(4^k)` fails.

*Re-run.*  We only need the truncation error `≤ C_tr(k) · exp(−1/(8k²ε))` (the exponent Prop 4.3
actually carries).  Write `R(k, u₀) := u₀^{−u₀/2+5/2} · 4k(u₀+5) · exp((u₀+5)/(2k)) / k`.  Then
`truncation ≤ k · R · exp(−1/(8k²ε))`, and a scan of `k ≤ 64`, `u₀ ∈ [1, 10⁴]` gives
`max log R = 8.78` (at k = 1, u₀ ≈ 4.2); for `u₀ → ∞` the `(u₀/2) log u₀` term dominates, for
`k → ∞` the exponential factor → 1.  So **`C_tr(k) ≤ e^{9} k`**.
Outside the range: for `ε > 1/(40k)` we have `1/(8k²ε) < 5/k ≤ 5`, so the *whole* bound is trivial
with constant `e^5` (the left side is ≤ 1).  The upper Dickman range `z ≤ y^{(log y)^{1/10}}` fails
for `z` near `x` when ε is small, but there `u ≥ (log y)^{1/10} − 5 = (ε log x)^{1/10} − 5 ≫ 1/ε`
(since ε ≥ 1/log log x), which beats `exp(−1/(8k²ε))` with an absolute constant for `x ≥ x₀`
absolute.  Net: **the (4.20) leg is O(k)**.

## Consequence for the Lean shape: the single constant is wrong, not the mathematics

After the re-run the constant on the first two terms is `exp(O(k²))` (tuple sum × Mertens), fine.
The constant on the third term is `exp(O(k²)) × C_FL(k)`, where `C_FL` is the fundamental lemma's
dependence on the sifting dimension.  KB §4e argued `C_FL` "has no bite" because in the block
construction it multiplies `exp(−s)` with `s = 3/(4ε_i)` huge.  That is true on paper and **false for
the frozen `KMT_quant C`**, which puts one `C J` in front of `exp(−1/(8J²ε))` for *every* ε up to 1/2,
where the exponential is ≥ e^{−1/(4J²)} and cannot absorb anything: the Lean hypothesis
`log C(k) = o(4^k)` silently demands `log C_FL(k) = o(4^k)`, which nobody has checked.

**Repair (re-freeze):** two constants.
```
KMT_quant₂ C₁ C₂ :  ‖W‖ ≤ C₁ J · (√log(1/ε)·√(2 S(x^ε,x)) + exp(−S(x^ε))) + C₂ J · exp(−1/(8J²ε))
exists_sparse_normal_of_KMT_quant₂ :  log C₁ k / 4^k → 0  →  log log C₂ k / 4^k → 0  →  KMT_quant₂ C₁ C₂  →  ∃ 𝒫 …
```
Schedule change: `Jᵢ := max{J ≤ i : ∀ J' ≤ J, |C₁ J'| ≤ i^{1/4} ∧ log|C₂ J'| ≤ i/2}`.  Then the third
term is `≤ exp(i/2 − (i+3)³/Jᵢ²) ≤ e^{−i/2}` (lap schedule `εᵢ = 1/(8(i+3)³)`, `Jᵢ ≤ i`), and by
maximality either `|C₁(Jᵢ+1)| > i^{1/4}` (so `log i = o(4^{Jᵢ})` from `h₁`) or `log|C₂(Jᵢ+1)| > i/2`
(so `log i < log 2 + log log C₂(Jᵢ+1) = o(4^{Jᵢ})` from `h₂`).  `h₂` is essentially sharp: the L¹ tail
forces `Jᵢ ≳ log₄ log i`, so `C₂(J) ≤ exp(exp(o(4^J)))` is what any schedule can tolerate.  Every
finite sieve constant satisfies it.  `KMT_quant C → KMT_quant₂ C C` keeps the old theorem as a corollary.

## Status after this note

- (4.20): re-run done, O(k).  ✅
- Tuple sums, Mertens: exp(O(k²)), exp(O(k/log k)).  ✅ (numerics in KB §4e)
- Fundamental lemma constant: any finite value is fine **once the Lean Prop has two constants**.  The
  re-freeze is the fix; without it the theorem quietly assumes an unverified bound.
