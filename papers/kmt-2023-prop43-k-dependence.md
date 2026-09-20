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
| **(4.20) smooth-number truncation d_j ≤ x^{1/(4k)}** | third term | **O(k) after the re-run below**: `e^{10} k` (referee-corrected from `e⁹ k`, Part IV.4) (the paper's literal `≪ exp(−1/(2ε))` costs `exp(≈e^{4k}/(2e))`) |
| (4.22) fundamental lemma, dimension κ = k | third term | **explicit (Part III)**: β-sieve with β = 9k+1 gives error `e^{9k−s}K^{10}` with no implied constant (Opera de Cribro Lemma 6.8, restated in Thorner–Zaman arXiv:1803.02823 Lemma 6.2); `K = exp(O(k))` here, so `C_FL(k) = exp(O(k))` |
| Lemma 4.5 / (4.25) dimension-k Mertens | first two terms | exp(O(k log k)) (referee-corrected from exp(O(k/log k)); the primes k < p < 2k, Part IV.6) |

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
`log C(k) = o(4^k)` silently demands `log C_FL(k) = o(4^k)`, which nobody had checked (Part III now does: it holds, `log C_FL(k) = O(k)`; the two-constant shape stays because it is the weaker hypothesis).

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

---

# Part II — Proof of `KMT_quant₂ C₁ C₂` from KMT §4, with the constants tracked (2026-09-20)

**Claim.**  There are `C₁(k) = exp(O(k²))` and a finite `C₂(k)` such that for every prime set 𝒫, every
`J = k ≥ 1`, every `h ∈ ℤ∖{0}` with `NontrivialWindow k h`, every `x ≥ 3` and every
`ε ∈ (1/log log x, 1/2)`,
```
|W| ≤ C₁(k)·( √log(1/ε) · √(2 S_𝒫(x^ε, x)) + exp(−S_𝒫(x^ε)) ) + C₂(k)·exp(−1/(8k²ε)),
```
where `W = (1/x) Σ_{n<x} ∏_{j≤k} z_j^{ω_𝒫(n+j)}`, `z_j = e(h/4^j)`, `S_𝒫(y) = Σ_{p≤y, p∈𝒫} 1/p`,
`S_𝒫(y,x) = Σ_{y<p≤x, p∈𝒫} 1/p`.  Moreover `log log C₂(k) = O(log k) + log log C_FL(k)`, where
`C_FL(k)` is the implied constant of the fundamental lemma of sieve theory in dimension `k`
(Iwaniec–Kowalski Lemma 6.3), so `h₂ : log log C₂(k) = o(4^k)` holds for any `C_FL(k) ≤ exp(exp(o(4^k)))`.
**Part III: `C_FL(k) = e^{9k}K^{10} = exp(O(k))`, so in fact `C₂(k) = exp(O(k²))` and even the one-constant `KMT_quant` hypothesis `log C = o(4^k)` is met.**

## II.0  Instance and three inherited uniformities

Take `f_j(n) := z_j^{ω_𝒫(n)}`, `a_j = 1`, `h_j = j` (so `a_i h_j ≠ a_j h_i` for `i ≠ j`), `χ_j = 1`, `t_j = 0`.
Each `f_j` is multiplicative, `|f_j| ≤ 1`, `f_j(p^ℓ) = z_j` for `p ∈ 𝒫` and `1` otherwise.
- **Uniform in 𝒫.**  Prop 4.3's constant is uniform over all 1-bounded multiplicative `f_j`; 𝒫 enters
  only through `f_j`.  So one `C(k)` serves every prime set, which is what the Lean `∀ S` needs.
- **Distances.**  `𝔻(f_j, 1; y, x)² = Σ_{y<p≤x} (1 − Re f_j(p))/p = (1 − cos 2πh/4^j)·S_𝒫(y, x) ≤ 2 S_𝒫(y, x)`.
  Let `j*` be the least `j ≤ k` with `4^j ∤ h` (exists by `NontrivialWindow`); then `h/4^{j*} ∈ ¼ℤ ∖ ℤ`, so
  `1 − cos ≥ 1` and `max_j 𝔻(f_j, 1; x^ε)² ≥ 𝔻(f_{j*}, 1; x^ε)² ≥ S_𝒫(x^ε)`.  Hence the two distance terms
  of Prop 4.3 are `≤ √(2 S_𝒫(x^ε,x))` and `≤ exp(−S_𝒫(x^ε))`: the Lean shape is a weakening.
- **`n < x` vs `n ≤ x`, and thresholds `x ≥ x₀`.**  Changing one summand moves `W` by `≤ 2/x ≤ (log x)^{−1/8}
  ≤ exp(−1/(8k²ε))` for `x ≥ 3` (using `ε > 1/log log x`).  Any step valid only for `x ≥ x₀` is
  covered below `x₀` by the trivial `|W| ≤ 1 ≤ exp(log log x₀/(8k²))·exp(−1/(8k²ε))`, i.e. a factor
  `exp(log log x₀/(8k²))` on `C₂`.  Every threshold below is either absolute or has
  `log log x₀(k) = O(log k)`, so this factor is `k^{O(1/k²)} = O(1)`.  The same trivial bound covers any
  ε-range where the sieve inputs are unavailable: if `ε > c/k` then `1/(8k²ε) < 1/(8ck)`, constant `e^{1/(8ck)}`.

Prop 4.3 with `t_j = 0` is proved with `exp(−1/(4k²ε))` in the third term (its Step 1 is void here);
we only use the weaker `exp(−1/(8k²ε))`.

## II.1  Step 2 of Prop 4.3 (small primes): the tuple sums, `T₁(k)` on everything, `T₂(k)` on the sieve term

Take `A := ∏_{p≤k} p` (any `A` divisible by the primes of `Δ = ∏_{i<j}(j−i)` works in Step 2; including
`p = k` also removes a formal division by `1 − k/p` at `p = k` in (4.25), see II.4).  Write
`f_j(n) = Σ_{e | n, e | A^∞} f_j(e) f̃_j(n/e)` with `f̃_j` vanishing on `p ≤ k`, and expand (4.6):
`W = Σ_{e_1..e_k | A^∞} f_1(e_1)⋯f_k(e_k)/[e_1,…,e_k] · S(x; e)`, `|f_j(e)| = 1`, `|S(x;e)| ≤ 2[e]/e_j` for each `j`.

*Large tuples* (`some e_j > z`, `z = (log x)^{1/(3k)}`), (4.7): contribution
`≤ 2 Σ_{e_1>z} (e_1⋯e_k)^{−1/k} ≤ 2 z^{−9/(10k)} T₂(k)`, `T₂(k) := (∏_{p≤k} (1 − p^{−1/(10k)})^{−1})^k`, and
`z^{−9/(10k)} = (log x)^{−3/(10k²)} ≤ exp(−3/(10k²ε)) ≤ exp(−1/(8k²ε))`.  Size: `1 − p^{−1/(10k)} ≥ log p/(20k)`
for `p ≤ k`, so `log T₂(k) ≤ k Σ_{p≤k} log(20k/log p) = k π(k) log(20k)(1 + o(1)) = O(k²)`.
→ **`T₂(k) = exp(O(k²))` on the sieve term.**

*Small tuples* (`all e_j ≤ z`): `[e] = M ≤ (log x)^{1/3}`, and (4.8)–(4.10) with `Q = 1` give
`S(x;e) = (M/x)·(main) + O(M/x)` where `main = Σ_{n ≤ X} ∏_j g_j(K_j n + B_j)`, `X = x/M ∈ [x^{1/2}, x]`,
`K_j = M/e_j`, `B_j = (b+j)/e_j`, `g_j = f̃_j`.  The `O(M/x)` errors total `≤ (#tuples)·(log x)^{1/3}/x ≤
(log x)^{2/3}/x ≤ exp(−1/(8k²ε))` for `x ≥ 3`.  The `main` terms are bounded by Prop 4.4 (II.2–II.5) with
`ε' ∈ [ε, 2ε]`, `X^{ε'} = x^ε =: y`; the tuple weights factor out:
`Σ_{e_j ≤ z} 1/[e_1,…,e_k] ≤ T₁(k) := Σ_{e_1..e_k | A^∞} 1/[e_1,…,e_k] = ∏_{p≤k} Σ_{m≥0} p^{−m}((m+1)^k − m^k)`.
Numerically `log T₁(k) ≈ 0.6 k²` for `k = 4..64` (KB verdict §4e); analytically `Σ_m p^{−m}(m+1)^k ≤
k!/(log p)^k · e^{O(k)}`, so `log T₁ ≤ π(k)(k log k) + O(k²/log k) = O(k²)`.
→ **`T₁(k) = exp(O(k²))` multiplies the whole Prop 4.4 bound, i.e. both `C₁` and `C₂`.**

Prop 4.4's hypotheses hold: `(K_j, B_j) = 1`, `K_j | A^∞`, `K_j, B_j ≤ (log X)^{1/2}` for `x ≥ x₀`
absolute, and `g_j(p^ℓ) = 0` for `p | ∏(K_i B_j − K_j B_i) | A^∞`.  Its distances are for `g_j`:
`𝔻(g_j,1;y,X) ≤ 𝔻(f_j,1;y,x)` (equal on `(y, X]` since `y > k`; `X ≤ x`), and
`𝔻(g_j,1;y)² ≥ 𝔻(f_j,1;y)² − 2 Σ_{p≤k} 1/p`, so `exp(−max_j 𝔻(g_j;y)²) ≤ e^{O(1)}(log k)²·exp(−max_j 𝔻(f_j;y)²)`.
Also `log(1/ε') ≤ log(1/ε)` and `exp(−1/(2ε')) ≤ exp(−1/(4ε)) ≤ exp(−1/(8k²ε))`.

## II.2  Prop 4.4, (4.14)–(4.18): removing the large primes — constant `O(k)` on the first term

Replace `g_j` by its `y`-truncation `g̃_j` (`= 1` on `p > y`).  By (4.14)–(4.15) the error is
`≤ Σ_{j≤k} Σ_{n≤X} Σ_{p^ℓ ‖ K_j n+B_j, p>y} |1 − g_j(p^ℓ)|` — a **sum** over `j`, which the paper writes as
"for some `j`"; this is the factor `k`.  Per `j`: prime powers `ℓ ≥ 2` contribute `≪ X(log X)^{3/2}/y`
(union bound + `Ω(n) ≪ log n`), and `X(log X)^{3/2}/y ≤ X exp(−1/(2ε))` for `x ≥ e^{30}` (absolute);
the `ℓ = 1` part is `≤ Σ_{y<p≤2X√log X} (X|1−g_j(p)|/p + 1)`, whose `+1` sum is `≪ X/(log X)^{1/2} ≤
X exp(−(1/2)log log X) ≤ X exp(−1/(2ε))`, and whose main part, after truncating to `p ≤ X` (Mertens,
error `≪ X log log X/log X`, absorbed the same way) and Cauchy–Schwarz with `Σ_{y<p≤X} 1/p = log(1/ε') + O(1/log y)`,
is `≤ X·√2·𝔻(g_j,1;y,X)·(log(1/ε) + O(1))^{1/2} ≤ A₀ X √log(1/ε)·𝔻(g_j,1;y,X)` with `A₀` absolute
(`log(1/ε) ≥ log 2`).
→ **first term: constant `A₀ k`; sieve term: `A₀ k` (absolute thresholds).**

## II.3  (4.19)–(4.21): the smooth-number truncation `d_j ≤ x^{1/(4k)}` — constant `e⁹ k` on the sieve term

This is Part I's re-run.  The error is `≤ A₁ X · u₀^{−u₀/2+5/2} · (1/ε)` with `u₀ = 1/(4kε) − 5` (Dickman
`ρ(u) ≤ u^{−u/2}`, `u ≥ 1`; smooth numbers in progressions to modulus `q = K_1 ≤ (log x)^{1/3} ≤ y`, whose
`−log q/log y ≥ −1/3` is inside the `−4`; Selberg's sieve for `Σ_{e≤Y,(e,P(y))=1} 1/e ≪ log x/log y = 1/ε`),
valid when `x^{1/(4k)} ≥ y^{10}`, i.e. `ε ≤ 1/(40k)`, and `z = (x+h)/e ≤ y^{(log y)^{1/10}}`.
Writing `1/ε = 4k(u₀+5)`: `u₀^{−u₀/2+5/2}·4k(u₀+5) ≤ e^{8.78}·k·exp(−(u₀+5)/(2k)) = e^{8.78} k·exp(−1/(8k²ε))`
(scan over `k ≤ 64`, `u₀ ∈ [1, 10⁴]`; both limits are monotone beyond the scan).  For `ε > 1/(40k)` the whole
bound is trivial with constant `e⁵`.  For `z > y^{(log y)^{1/10}}` drop the progression (factor `q ≤
exp((1/3)log log x)`) and use `ρ(u)` at `u ≥ (ε log x)^{1/10} − 5 ≥ (log x/log log x)^{1/10} − 5`, which
exceeds `3 log log x ≥ 3/ε` once `log x ≥ 10^{25}` (absolute; below it the trivial bound costs `e^{7.2}`).
→ **sieve term: `e⁹ k` (absolute thresholds).**

## II.4  (4.22)–(4.24): the fundamental lemma — constant `C_FL(k)·E₄₅(k)` on the sieve term

For `d_j ≤ x^{1/(4k)}` pairwise coprime and coprime to `A`, `Σ(x;d)` counts `n ≤ X/(d_1⋯d_k)` with the `k`
forms sifted by `P(y)`; `ρ(p) = k/p` if `p ∤ d_1⋯d_k`, `1/p` if `p | d_1⋯d_k` (4.23), for `p > k`.  The
fundamental lemma in dimension `κ = k` with `s = log(X/(d_1⋯d_k))/log y ≥ 3/(4ε)` gives
`Σ = (1 + O_k(e^{−s})) (X/d_1⋯d_k) ∏_{k<p≤y}(1 − ρ(p)) + O(X^{1/2})`; the implied constant is `C_FL(k)`
(depends on `κ = k` and on the `Ω(κ)` constant `K`; **Part III: `C_FL(k) = e^{9k}K^{10}` exactly, and `K = exp(O(k))`** - the earlier `exp(O(k/log k))` used `(1−k/p)^{−1} = e^{k/p}(1+O(k²/p²))`, valid only for `p ≥ 2k`; the primes `k < p < 2k` cost `Σ log(p/(p−k)) ≤ π(2k) log(k+1) = O(k)`).  The lemma
needs `s ≥ s₀(k)` (IK: `s ≥ 9κ+1` suffices), i.e. `ε ≤ 3/(4(9k+1))`; outside that range the bound is trivial
with constant `e^{2}`.  Summing the `O_k(e^{−s})` error over `d` with weights `∏_{p|d_j}(1−1/p)/d_j` and
the product `∏_{k<p≤y, p∤d}(1−k/p)` is Lemma 4.5 with `f_j = 1`: `≤ E₄₅(k)` (II.5).  The `O(X^{1/2})` terms:
`≤ x^{1/4}·x^{1/2} = x^{3/4}`.
→ **sieve term: `C_FL(k)·E₄₅(k)·e^{2}` = `exp(O(k))·E₄₅(k)` by Part III** (referee: `s = 1/(2ε)` not `3/(4ε)`, remainder `x^{3/4}(log x)^{k−1}` not `x^{3/4}`, ε-threshold `ε ≤ c/k`; Part IV.5).  (Before Part III this was the only leg whose growth in `k` was not written down; `KMT_quant₂` needs only `log log C_FL(k) = o(4^k)`.)

## II.5  (4.25) + Lemma 4.5: the main term — constant `E₄₅(k)·E_M(k)` on `exp(−S_𝒫(x^ε))`, and a completion error on the sieve term

*Completion* (`d_j ≤ x^{1/(4k)}` → all `d_j | P(y)`), (4.25) error:
`≤ X (log y)^{−k} (Σ_{d|P(y), d>x^{1/(4k)}} 1/d)(Σ_{d|P(y)} (1/d)∏_{p|d,p>k}(1−k/p)^{−1})^{k−1}`.  The last factor is
`(∏_{p≤y}(1 + 1/p + O(k/p²)))^{k−1} ≤ (A₂ log y)^{k−1}·exp(O(k/log k))`, so with `(log y)^{−k}` it leaves
`A₂^{k}/log y`.  The smooth-tail sum is `≤ Σ_{D=2^ℓ ≥ x^{1/(4k)}/2} [exp(−½(log D/log y) log log(D/log y…)) +
exp(−(log D)^{1/20})]` (Hildebrand–Tenenbaum).  The first summand is `≤ exp(−1/(2ε))` as in II.3; the second
needs `(log x/(4k))^{1/20} ≥ log log x`, i.e. `x ≥ x₀(k)` with `log log x₀(k) = O(log k)` — absorbed with
factor `k^{O(1/k²)}`.  → **sieve term: `exp(O(k))`.**  **Referee (Part IV.6): this exponent is wrong - the completion factor is `exp(O(k log k))` because the Euler factor at `k < p < 2k` is `1 + 1/(p−k)`, not `1 + 1/p + O(k/p²)`; `2^{k−1}` alone when `k+1` is prime.  Harmless for `exp(O(k²))`.**

*Main term*, Lemma 4.5 at `a_p = (k−1)/(1−k/p)` (`p > k`; here `A ∋ k` so `1 − k/p ≠ 0` throughout):
`∏_{k<p≤y}(1−k/p) |Σ_d ∏_j f_j(d_j)/d_j ∏_{p|d_j}(1+a_p/p)| = ∏_{k<p≤y} |(1−k/p)(1 + Σ_j f_j(p)(1+a_p/p)/p)|`
(exact: `d_j` squarefree, pairwise coprime, so each `p` sits in at most one `d_j`)
`= ∏_{k<p≤y} |1 + w_p|`, `w_p = Σ_j (f_j(p)−1)/p + O((k² + k a_p)/p²)`, and `|1+w| ≤ exp(Re w + |w|²/2)` gives
`≤ exp(−Σ_j 𝔻(g_j,1;y)²)·E₄₅(k) ≤ E₄₅(k) exp(−max_j 𝔻(g_j,1;y)²)`, with
`log E₄₅(k) = O(Σ_{p>k} (k² + k a_p)/p²) = O(k Σ_{k<p≤2k} 1/(p−k) + k/log k) = O(k log k)`.
The Mertens comparison `∏_{k<p≤y}(1−k/p) ≍ (log y)^{−k}` is not needed for the upper bound.
→ **second distance term: `E₄₅(k)·(log k)²·e^{O(1)}` (the `(log k)²` from II.1's `g_j → f_j`).**

## II.6  Assembly

Collecting, with `T₁ = exp(O(k²))` in front of everything from Prop 4.4:
```
C₁(k) = T₁(k) · max( A₀ k ,  E₄₅(k)(log k)² e^{O(1)} )               = exp(O(k²))
C₂(k) = T₁(k) · ( A₀ k + e^{10} k + e² C_FL(k) E₄₅(k) + e^{O(k log k)} ) · (threshold factors, O(1))  +  2 T₂(k)
      = exp(O(k²)) · (1 + C_FL(k))  = exp(O(k²))          (Part III: C_FL(k) = exp(O(k)))
```
so `log C₁(k) = O(k²) = o(4^k)` and `log log C₂(k) = O(log k) + log log(1 + C_FL(k))`.  With II.0's
translation of the distance terms and the `n<x` shift, this is `KMT_quant₂ C₁ C₂`, and
`exists_sparse_normal_of_KMT_quant₂` applies as soon as `log log C_FL(k) = o(4^k)`.

## II.7  What a referee should push on

1. **`C_FL(k)`.**  ~~The single unquantified input.~~  **CLOSED (Part III, 2026-09-20):** the β-sieve
   Fundamental Lemma with `β = 9κ+1` has the fully explicit error `e^{9κ−s}K^{10}` (Opera de Cribro
   Lemma 6.8; explicit restatement in Thorner–Zaman arXiv:1803.02823 Lemma 6.2), and `K = exp(O(k))` for
   `g(p) = k/p`, `p > k`.  So `C_FL(k) = exp(O(k))`, far inside the `exp(exp(o(4^k)))` needed.  What a
   referee should still check: that the `Ω(κ)` hypothesis is verified with the *same* `K` for both the
   `p ∤ d` density `k/p` and the `p | d` density `1/p` (it is - the second product is termwise smaller).
2. **`T₁(k)` and `T₂(k)`.**  Both `exp(O(k²))`; the numerics (§4e) say `log T₁ ≈ 0.6k²`.  If one wanted
   `log C₁ = o(4^k)` to fail one would need `k²` to beat `4^k`; it does not.
3. **The `A ∋ k` choice.**  Harmless and makes (4.25)'s `(1−k/p)^{−1}` well-defined when `k` is prime.
4. **Thresholds.**  Every `x ≥ x₀` used is absolute or has `log log x₀(k) = O(log k)`; the absorption
   factor `exp(log log x₀/(8k²))` is then `O(1)`.  The absurd absolute threshold in II.3 (`log x ≥ 10^{25}`)
   is an artefact of using Hildebrand–Tenenbaum's crude `(log D)^{1/20}` term rather than a
   smooth-numbers-in-progressions bound in a wider range; it costs a constant, nothing else.

---

# Part III — The fundamental-lemma constant is explicit: `C_FL(k) = e^{9k}K^{10} = exp(O(k))` (2026-09-20)

## III.1  The statement with an explicit constant

The β-sieve Fundamental Lemma (Friedlander–Iwaniec, *Opera de Cribro*, §6.5, Lemma 6.8) carries no
implied constant.  In the form given by Thorner–Zaman, arXiv:1803.02823, §6, Lemma 6.2 (their proof says
"this statement is essentially the Fundamental Lemma [Opera, Lemma 6.8]", with the same truncation
parameters): let `g` be multiplicative with `0 ≤ g(p) < 1` and satisfying `Ω(κ)` with constant `K > 1`,
```
∏_{w≤p<z} (1 − g(p))^{−1} ≤ K (log z / log w)^κ        for all 2 ≤ w ≤ z.
```
Let `λ^±_d` be the β-sieve weights of level `R` with `β = 9κ+1`, and `s = log R / log z ≥ β`.  Then
```
Σ_d λ^−_d g(d) ≥ (1 − e^{9κ−s} K^{10}) V(z),      Σ_d λ^+_d g(d) ≤ (1 + e^{9κ−s} K^{10}) V(z),
```
`V(z) = ∏_{p<z}(1 − g(p))`.  (Thorner–Zaman state it for the composed sums `Σ_b θ_b h̃(b)`, which is the
same inequality after the change of variables `θ = 1 ∗ λ`, `h̃(p) = g(p)/(1−g(p))`, cf. their (6.5)–(6.7).)
Iwaniec–Kowalski Lemma 6.3 is the same lemma with the constant hidden: `(1 + O(e^{−s} K^{10}))`,
"implied constant depending only on κ" - that constant is `e^{9κ}`.

So in II.4, with `κ = k` and `s ≥ 3/(4ε) ≥ 9k+1`:
```
C_FL(k) = e^{9k} K^{10}.
```

## III.2  The `Ω(k)` constant `K` for the KMT densities

In (4.23) the sifted density is `g(p) = k/p` for `p ∤ d_1⋯d_k` and `1/p` for `p | d_1⋯d_k`, both only for
`p > k` (the primes `≤ k` sit in `A`, II.0/II.7 item 3).  Since `1/p ≤ k/p`, the `Ω(k)` product for the
mixed density is termwise `≤` the one for `g(p) = k/p`, so one `K` serves both.  For `k < w ≤ p < z`:
```
log ∏_{w≤p<z} (1 − k/p)^{−1} = k Σ_{w≤p<z} 1/p  +  Σ_{w≤p<z} [ −log(1 − k/p) − k/p ].
```
- Mertens with an absolute error: `Σ_{w≤p<z} 1/p ≤ log log z − log log w + c₀/log w` (`c₀` absolute,
  e.g. Rosser–Schoenfeld), so the first sum contributes `(log z/log w)^k · e^{c₀ k / log w} ≤ (log z/log w)^k e^{c₀ k}`.
- The second sum, over `p > k`: for `k < p < 2k`, `−log(1−k/p) − k/p ≤ log(p/(p−k)) ≤ log(k+1)`, and there
  are at most `π(2k) ≤ 1.26·2k/log(2k)` such primes, total `≤ 2.52 k log(k+1)/log(2k) ≤ 2.52 k`; for
  `p ≥ 2k`, `−log(1−t) − t ≤ t²` at `t = k/p ≤ 1/2`, total `≤ k² Σ_{p≥2k} 1/p² ≤ k²·(2/(2k log 2k)) = k/log(2k)`.

Hence `K ≤ exp((c₀ + 2.52 + 1) k) = exp(O(k))` and
```
C_FL(k) = e^{9k} K^{10} ≤ exp((9 + 10 c₀ + 35.2) k) = exp(O(k)).
```
(Referee, Part IV.5: KMT sift by all of `P(y)`, so the primes `p ≤ k` *are* sifted; at those primes the density `ρ(p;d)` is `≤ 1` and can equal 1 (`k = 2`, `p = 2`: both forms cover both classes), a degenerate case in which sifted count and `∏(1−ρ)` both vanish.  The lemma's `0 ≤ g(p) < 1` hypothesis has to be discharged there separately, e.g. by sifting only by `p > k` and handling `p ≤ k` through the class of `n` mod `A` - which is what Step 2 already does.  Also `e^{c₀k/log w} ≤ e^{c₀k}` needs `log w ≥ 1`; at `w = 2` read `e^{1.45c₀k}`.)

## III.3  Consequence for II.6 and for the Lean node

```
C₂(k) = exp(O(k²)) · (1 + C_FL(k)) = exp(O(k²)).
```
So both constants of `KMT_quant₂` are `exp(O(k²))`: `h₁` and `h₂` of `exists_sparse_normal_of_KMT_quant₂`
hold outright, and the single-constant `KMT_quant C` with `log C(k) = o(4^k)` would also have been
satisfiable.  The two-constant shape is kept in Lean because it is the weaker hypothesis and already green
(`KMT_quant₂_of_KMT_quant` goes the other way for free).  Every constant in the chain from KMT §4 to
`KMT_quant₂` is now either absolute, numerically measured (`T₁`, §4e), or bounded by an explicit
expression in `k`; nothing is `O_k(1)` with an unnamed dependence.

## III.4  Provenance and what was not read

- Read this session: Thorner–Zaman arXiv:1803.02823 §6 (statement of Lemma 6.2, the proof's pointer to
  Opera de Cribro (6.40), (6.43)–(6.44), (5.38), Lemma 6.8), extracted with `pdftotext`.
- **Not read**: *Opera de Cribro* itself (not local, not open-access).  The claim "no implied constant" rests
  on Thorner–Zaman's restatement, a single origin.  A second, independent statement of the `e^{9κ−s}K^{10}`
  form turned up in a search summary but was not verified in a document, so it does not count.  Referee
  item: open Opera de Cribro Lemma 6.8 and confirm the `e^{9κ}` and the `K^{10}`.
- Iwaniec–Kowalski Lemma 6.3 (the version cited in Parts I–II) was likewise not re-read; only its table of
  contents (§6.4 "Fundamental Lemma of sieve theory", p. 158) was seen.
- **Referee (Part IV.5a): Thorner–Zaman's printed hypothesis (6.2) is `∏(1 − g'/(1−g'−g''))^{−1} ≤ K(log z/log w)^κ`,
  which for a single sieve (`g'' = 0`) is `∏((1−g)/(1−2g))`, not the `∏(1−g)^{−1}` used in III.1; with `g = k/p` it is
  negative at the least prime `> k`.  Their proof says (6.2) "corresponds to" Opera de Cribro (5.38), which is the
  `∏(1−g)^{−1}` form, so (6.2) is most likely a misprint for `∏(1 − g'/(1−g''))^{−1}` - but that is a guess until
  the book is opened.  Their Theorem 6.1 also needs `s > 9κ+1+10 log K`, harmless here.  **Item not closed.**

---

# Part IV — Referee corrections applied (2026-09-20 13:58 EDT)

An independent referee pass (fresh Opus agent, brief `REFEREE-REQUEST-2026-09-20-kmt-quant2-constants.md`,
report `REFEREE-REPORT-2026-09-20-kmt-quant2-constants.md`) recomputed `T₁`, `T₂` and the `R(k,u₀)` scan
from scratch and checked every leg against KMT lines 660–1290 and Thorner–Zaman §6.  Verdicts, and what
changed in the note:

| item | verdict | change |
|---|---|---|
| IV.1 II.0 uniformities | holds | `|W| ≤ 1 + 1/x`, so the absorption constant is `2 exp(log log x₀/(8k²))`; the ε-window is empty for `x ≤ e^{e²} = 1618` |
| IV.2 II.1 tuple sums | holds | `log T₁/k²` = 0.53…0.63 on k = 4..64 but 0.67 at k = 256, tending to 1 (`π(k)·k log k`); `log T₂/k²` ≈ 1.4–1.9; `A = ∏_{p≤k}p` legitimate (only `rad Δ` is needed) |
| IV.3 II.2 (4.16)–(4.18) | holds | factor `k` confirmed |
| IV.4 II.3 (4.20) | holds with two corrections | (a) the note double-booked `+5/2`: KMT's exponent `−1/(8kε)+5/2` *is* `−u₀/2`; (b) the leg sits inside Prop 4.4 whose parameter is `ε' ∈ [ε,2ε]`, so the target must be `exp(−1/(4k²ε'))`.  Rescanned max `log R` = 9.67 → constant `e^{10} k`.  `O(k)` stands |
| IV.5 II.4 + Part III | holds with corrections; **5(a) not closed** | TZ Lemma 6.2 verbatim as quoted, but TZ's printed Ω(κ) hypothesis (6.2) differs from III.1's form (see III.4); `s = 1/(2ε)` (level `≈ x^{1/2}`), remainder `Σ_{m<D} k^{ω(m)} ≍ D(log D)^{k−1}` so `x^{3/4}(log x)^{k−1}` total (absorbed, `log log x₀(k) = O(log k)`); `0 ≤ g(p) < 1` unverified at `p ≤ k` (degenerate) |
| IV.6 II.5 completion | **fails on one exponent** | completion factor is `exp(O(k log k))`, not `exp(O(k/log k))` (Euler factor `1 + 1/(p−k)` at `k<p<2k`; `2^{k−1}` when `k+1` prime).  `E₄₅ = exp(O(k log k))` holds but its derivation via `|1+w| ≤ exp(Re w + |w|²/2)` is unlicensed for `p ≲ 2k`; repaired exactly: local factor `≤ (p²−k)/p² ≤ 1` there, so that range costs only `exp(O(k/log k))` |
| IV.7 II.6 assembly | holds | one unbooked global slip: the `ε'`/`ε` factor 2 is bought once (II.0, from the `t=0` `exp(−1/(4k²ε))`) and spent twice; one line of bookkeeping |
| glitches A, B | both confirmed | plus two new ones in KMT: Prop 4.4's first term is squared in both in-proof applications but unsquared in both statements (statements are right, (4.18) is unsquared); the end of §4.1 names `𝔻(f_j,χ_j;·)` where Prop 4.4 delivers `𝔻(g_j,1;·)`, a factor `exp(Σ_{p|A}1/p) ≍ log k` KMT do not book |

**Net after corrections.**
```
C₁(k) = T₁ · max( A₀ k , E₄₅ (log k)² e^{O(1)} )                                      = exp(O(k²))
C₂(k) = T₁ · ( A₀ k + e^{10} k + e² C_FL E₄₅ + e^{O(k log k)} ) · O(1)  +  2 T₂        = exp(O(k²))
```
with `C_FL(k) = e^{9k}K^{10}`, `K = exp(O(k))`, conditional on IV.5(a): the single-sieve Ω(κ) form of the
Fundamental Lemma must be confirmed in *Opera de Cribro* Lemma 6.8 / (5.38) (or Iwaniec–Kowalski (6.13)),
which nobody in this chain has opened.  The Lean hypotheses `log C₁ = o(4^k)`, `log log C₂ = o(4^k)` hold
with enormous margin under every reading, including the discarded literal `exp(exp(e^{4k}/2e))` of Part I.

**Still open (one item).**  IV.5(a).  It is a book lookup, not mathematics.

**Addendum (15:45 EDT), a second origin for the *form* of the hypothesis.**  Iwaniec, *Rosser's sieve*, Acta
Arith. 36 (1980) 171–202, open access at `http://matwbn.icm.edu.pl/ksiazki/aa/aa36/aa36210.pdf` (scanned; OCR in
`papers/iwaniec-1980-rossers-sieve.ocr.txt`).  Its dimension hypothesis (1.3) is
`∏_{w≤p<z} (1 − ω(p)/p)^{−1} ≤ K (log z/log w)^κ` for all `z > w ≥ 2`, `K ≥ 2` - the form used in III.1, and the
one Thorner–Zaman's printed (6.2) fails to reduce to.  Its Fundamental Lemma (Theorem 4, (2.12)) has error
`Q(s) ≤ exp(−s log s + s log log 3s + O(s))` with "all constants implied … will at most depend on κ" - so the
1980 paper does **not** supply the explicit `e^{9κ}K^{10}`; that refinement is the β-sieve chapter of Opera de
Cribro.  Status of IV.5(a): hypothesis form confirmed by an independent primary source; the explicit constant
still rests on Thorner–Zaman's restatement alone.
