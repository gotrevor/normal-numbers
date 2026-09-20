# Referee request: the constant-tracked proof of `KMT_quant₂` (Parts I–III of `kmt-2023-prop43-k-dependence.md`)

Written 2026-09-20 13:35 EDT.  Self-contained brief for a reviewer who has not seen this repo.

## What is being claimed

`papers/kmt-2023-prop43-k-dependence.md` claims that Proposition 4.3 of Klurman–Mangerel–Teräväinen,
*On Elliott's conjecture and applications* (arXiv:2304.05344; local text `papers/kmt-2023-multiplicative-correlations.txt`),
specialised to `f_j(n) = z_j^{ω_𝒫(n)}` with `z_j = e(h/4^j)`, holds with constants that are explicit in the
window length `k`:

```
|W| ≤ C₁(k)·( √log(1/ε) · √(2 S_𝒫(x^ε, x)) + exp(−S_𝒫(x^ε)) ) + C₂(k)·exp(−1/(8k²ε)),
C₁(k) = exp(O(k²)),   C₂(k) = exp(O(k²)),
```
for every prime set 𝒫, every `h ≠ 0` with some site `j ≤ k` having `h/4^j ∉ ℤ`, every `x ≥ 3`, and every
`ε ∈ (1/log log x, 1/2)`.  Here `W = (1/x) Σ_{n<x} ∏_{j≤k} z_j^{ω_𝒫(n+j)}` and `S_𝒫(y) = Σ_{p≤y, p∈𝒫} 1/p`,
`S_𝒫(y,x) = Σ_{y<p≤x, p∈𝒫} 1/p`.  This is the Lean Prop `KMT_quant₂ C₁ C₂` in
`src/NormalNumbers/G4WiringSparse.lean`; the Lean side is done and needs only `log C₁(k)/4^k → 0` and
`log log C₂(k)/4^k → 0`, so the review question is whether the *paper-level* constants are right.

## What to check, leg by leg (the paper's Part II sections)

Report each item as **holds / holds with a correction / fails**, with the line of the KMT paper and the
line of the note it concerns.  Do not repair; locate.

1. **II.0 uniformities.**  Is the KMT constant really uniform in the 1-bounded `f_j` (hence in 𝒫)?  Is
   `exp(−max_j 𝔻(f_j,1;y,x)²) ≤ exp(−S_𝒫(x^ε))` correct at a site with `h/4^j ∉ ℤ`?  Is the absorption of
   every `x ≥ x₀(k)` threshold into the trivial bound at cost `exp(log log x₀/(8k²))` legitimate given
   `ε > 1/log log x`?
2. **II.1 Step 1 / Step 2 (tuple sums).**  `T₁ = Σ_{e_j | A^∞} 1/[e_1,…,e_k]` is claimed `exp(O(k²))`
   with `A = ∏_{p≤k} p` (numerically `log T₁ ≈ 0.6k²`).  Check the lcm-tuple sum bound analytically, and
   check that `T₂` (the `z^{−9/(10k)}` leg, (4.7)) is absorbed into `exp(−1/(4k²ε))` as stated.  ⚠️ least
   checked leg.
3. **II.2 (4.16)–(4.18).**  The Cauchy–Schwarz + Mertens step: is the "for some j" in (4.16) a sum over
   `j` (factor `k`) or a max?  Is the constant otherwise absolute?
4. **II.3 (4.20) smooth-number truncation.**  The note re-runs this leg and gets `e⁹ k · exp(−1/(8k²ε))`
   from `ρ(u) ≪ u^{−u/2}` with `u₀ = 1/(4kε) − 5`, plus trivial ranges `ε > 1/(40k)` (constant `e⁵`) and the
   large-`z` case.  Check the Dickman bound's range, the Selberg-sieve step for the `e`-sum, and the scan
   claim `max_{k,u₀} log R = 8.78`.
5. **II.4 (4.22)–(4.24) fundamental lemma.**  Part III claims the β-sieve Fundamental Lemma with
   `β = 9κ+1` has explicit error `e^{9κ−s}K^{10}` (Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.8, as
   restated in Thorner–Zaman arXiv:1803.02823 Lemma 6.2) and that `K = exp(O(k))` for `g(p) ∈ {k/p, 1/p}`,
   `p > k`.  Check (a) the restatement against the book if you have it, (b) the `Ω(κ)` computation in
   III.2, (c) that KMT's use of the lemma is the two-sided (upper and lower) form and that the
   `O(X^{1/2})` remainder is what the note says.  ⚠️ the book was not read by the author of the note.
6. **II.5 (4.25) + Lemma 4.5 completion and main term.**  `E₄₅ = exp(O(k log k))` with
   `a_p = (k−1)/(1−k/p)`; the completion error `exp(O(k))` with a threshold `log log x₀(k) = O(log k)` from
   Hildebrand–Tenenbaum's `(log D)^{1/20}`.  Check the exponent bookkeeping `(log y)^{−k} · (A₂ log y)^{k−1}`
   and whether `(1 − k/p)^{−1}` at `p | d_j` is well-defined once `A ∋ k`.  ⚠️ least checked leg.
7. **II.6 assembly.**  Do the per-leg constants multiply as written, and does every leg land on the term
   the table says it does?

## Two paper glitches the note already flags (confirm or deny)

- (4.16): "for some j" should read as a sum over `j`.
- (4.25): division by `1 − k/p` at `p = k` when `k` is prime; the note takes `A = ∏_{p≤k} p` to avoid it.

## Deliverable

A file `papers/REFEREE-REPORT-<date>-kmt-quant2-constants.md`: one entry per item above with the verdict,
the exact location, and for a failure the smallest counter-observation (a wrong exponent, a missing
range, a hypothesis not verified).  No prose beyond that; no fixes.
