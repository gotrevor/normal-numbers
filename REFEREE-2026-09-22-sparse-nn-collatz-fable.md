# Referee pass 2026-09-22 (Collatz-lane Fable, joining sparse-nn as a third reader)

Read-only pass over the end-to-end claim at `wip/g5-prime-subset` (paper
`papers/prime-model-assembly-2026-09-22.md` Parts I–VI, `HANDOFF-2026-09-22-kmt-quant2-PROVED.md`,
the sparse-nn mailbox to `20260922T191228Z`), with the brief "try to break frequency uniformity,
parameter regimes, and the final implication to normality".  Independent of the two agents in the
lane; I re-derived rather than re-read wherever a constant or a quantifier could hide a slip.

## Verdict

**No defect found.  Independently justified confirmation** of the chain

    window_bound_regime / KMT_quant₂  →  KMT_along + TailOK along the schedule
      →  Weyl on the orbit  →  IsNormal 4 (subsetLambert P 4),

for `DivergentRecip P` with `SparseL4o P` (and every stronger hypothesis in Parts II–V).
Everything below is a check I performed, not a summary of the lane's own audit.

## 1. Final implication to normality (the place a green build can still lie)

- `IsNormalSequence b s` (`SeqDefs.lean`) is **full** normality: every nonempty block `w` of
  digits `< b` has frequency `→ b^{−|w|}`.  Not simple normality.  ✔
- `IsNormal b x := IsNormalSequence b (digitOf b (Int.fract x))`, `digitOf b x i = ⌊x b^{i+1}⌋ mod b`
  - the standard digits.  ✔
- `isNormal_iff_equidistributed_orbit` (`Wall.lean`) and `equidistributed_of_weyl`
  (`WeylCriterion.lean`) are theorems; the final theorems print the base three axioms, so no
  citation axiom sits under the bridge.  ✔
- `orbit 4 x n = fract(x·4ⁿ)` and `subsetLambert S 4 = Σ ω_S(n)/4ⁿ` give
  `orbit n = fract(Σ_{i≥0} ω_S(n+i+1)/4^{i+1}) = fract(tailB n)`; the integer part drops under
  `e(h·)` for integer `h` (`prefix_fourier_tendsto_zero`).  Digits `ω_S` are unbounded, which is
  harmless because the number is defined as a real, not through its digits.  ✔
- Averaging is ordinary (`prefixMean F N = (1/N)Σ_{n<N}`), at **every** `N`, for **each** fixed
  `h ≠ 0` - exactly Weyl's quantifier order.  ✔

## 2. Frequency uniformity in Part I

- `A = Σ_{j<k}(z_j − 1)`, `z_j = e(h/4^{j+1})`.  At the least nontrivial site `h/4^{j₀} = m/4`
  with `4 ∤ m`, so `z ∈ {i, −1, −i}`, `Re(z−1) ≤ −1`; other terms `≤ 0`; `|A| ≤ 2k`.  The
  contraction `‖∏(1 + A/p)‖ ≤ exp(Re A Σ1/p + |A|²/2 Σ1/p²)` uses `|1+w|² = 1 + 2Re w + |w|²
  ≤ e^{2Re w + |w|²}` and `Σ_{p>k} 1/p² ≤ 1/k`, giving `e^{2k} exp(−Σ_{p∈P}1/p)`; `+k` for the
  primes `≤ k` gives `e^{3k}`.  No constant depends on `h` or `S`.  ✔
- `NontrivialWindow J h` along a schedule `J_N → ∞`: for fixed `h ≠ 0` it holds once
  `4^{J_N} > |h|`.  ✔
- The fixed-`h` variant (Part VI): `|e(hA) − e(hA_y)| ≤ 4π|h| Σ_j ω_{>y}(n+j+1)/4^{j+1}` (Lipschitz
  `2π`, coarse `4π`), averaged with `Σ_{n<x} ω_{>y}(n+j+1) ≤ 2xR + k` uniformly in `j < k` and
  `Σ 4^{−j−1} ≤ 1/3`: `(4π|h|/3)(2R + k/x)`.  The window length leaves the fresh-mass term.  The
  `|h|` factor is legitimate: `KMT_along` fixes `h` before `N → ∞`.  ✔

## 3. Parameter regimes in Part I

- R1 (`ε > 1/(7680k)`): `exp(−1/(8k²ε)) ≥ e^{−960/k} ≥ e^{−960}`, and `e^{960} ≤ C₂(k)`.  ✔
- R2: `1/L₂x < ε ≤ 1/(7680k)` forces `L₂x > 7680k`; F1–F5 re-derived, in particular
  F5 `exp(−1/(8k²ε)) ≥ (log x)^{−1/8} ≥ x^{−1/4} ≥ 1/x`.  ✔
- E2: `8 + 12 log(2/ε) ≤ 36 log(1/ε)` needs `log(1/ε) ≥ 0.68`, true from `ε ≤ 1/7680`.  ✔
- E4 absorptions: `T^{1/(2 log y)} = exp(log x/(8k log y)) ≥ exp(1/(8kε))`; `σ/2 ≥ 1/(8ε)`;
  `2·4^k x^{1/4} x^{1/2}/x = 2·4^k x^{−1/4}`.  ✔
- Rankin tail `2k e^{20}/T^{1/(2 log y)}`: with `α = 1/(2 log y)` and `p ≤ y`,
  `p^α − 1 ≤ e^{1/2} α log p`, so `Σ_p (p^α−1)/p ≤ 0.83·α·Σ_{p≤y} log p/p = O(1)`; a bounded
  constant such as `e^{20}` is the right shape.  ✔
- Lower-atom transfer constant: with `Σν = Σμ = 1`, `d = ν − μ`, `Σ_B|d| = (μ(Bᶜ) − ν(Bᶜ)) + 2Σ_B d⁻`
  and `Σ_{Bᶜ}|d| ≤ ν(Bᶜ) + μ(Bᶜ)`; the `ν(Bᶜ)` cancels, total `≤ 2μ(Bᶜ) + 2η + 2|B|e`.  The paper's
  constant is exactly right (a naive bound gives 3).  ✔
- `Total → C₁, C₂`: `24k + e^{3k} ≤ e^{4k}`; `2k² + 2ke^{20} + 4 + 2·4^k ≤ e^{1000+2k} ≤ e^{e^{k+7}}`
  (`e^8 > 1002`).  ✔
- Retained box `|B| ≤ Q⌊T⌋^k` is consistent with "every site's hitting product `≤ T`", the
  reading under which `T^k` counts states; the Rankin bound is per site, union over `k`.  ✔

## 4. Family schedule (Parts III–VI), re-derived at `x = N`, `k = J`, `ε = J₁^{−4}`, `J₁ = ⌊L₃N⌋₊`

- Regime: `J₁^{−4} > 1/L₂N` and `J₁^{−4} ≤ 1/(7680 J)` from `J ≤ J₁` and `J₁³ ≥ 7680`.  ✔
- Old term `e^{3J} e^{−S_P(y)} ≤ e^{−5J}` from `J ≤ S_P(y)/8`; `J → ∞` needs `J₁ → ∞` and
  `S_P(y_N) → ∞` (`DivergentRecip` + `y_N → ∞`).  ✔
- Sieve term `(… + 2·4^J) exp(−J₁⁴/(8J²)) ≤ e^{22+J₁ log 4 − J₁²/8} → 0`.  ✔
- Tail, cap branch: mean of `Σ_{j≥J} ω_P(n+j+1)/4^{j+1}` over `n < N` is
  `≤ (S_P(2N+1) + π(2N)/N + o(1))/(3·4^J) ≤ (12L₂N + 35)/(3·4^J)` (primes `≤ 2N+1` for `j ≤ N`;
  the `j > N` part is `4^{−N}`-small), and `4^J ≥ L₂^{log 4}/4` with `log 4 > 1`.  P-independent.  ✔
- Tail, mass branch: `S_P(2N) ≤ S_P(y) + fresh(y, 2N) ≤ 8J + 9` once fresh `≤ 1`; `(8J+9)/4^J → 0`.  ✔
- Transfer under `SparseL4o`: for `t > y`, `π_P(t) ≤ η π(t)/L₄(t)` with `L₄(t) ≥ L₄(N)/2`
  (from `L₂y ≥ L₂N/2`); Abel with `1/t`: `R ≤ π_P(N)/N + (2η/L₄N)·C·log(log N/log y) + boundary`,
  and `log(log N/log y) ≤ 4L₄N + O(1)`, so `R = O(η)`; `η` arbitrary.  ✔ (Astra's computation,
  independently repeated.)
- `k/x = J/N → 0`.  ✔

## 5. The two negative examples (refereed as a third party)

- Density-zero set `π_P = ⌊F(π(x))⌋ − ⌊F(n₀)⌋`, `F(u) = u/L₄(u)`: `F' ∈ (0,1)` so the floor
  differences are `0/1`; `L₄(π(x))/L₄(x) → 1` from Chebyshev; `S_P ≍ L₂/L₄`; fresh mass over
  `[y, N]` is `≍ ℓ/v` with `ℓ = log(1/ε) ≍ 4v` at the `J₁^{−4}` schedule, so bounded below.  Any
  schedule using the current tail/sieve majorants needs `J ≥ c log t` and `J²ε → 0`, hence
  `ℓ ≥ 2v − O(1)`, so the weighted transfer term cannot vanish.  Correct as a failure of these
  majorants, and correctly not stated as a theorem about normality.  ✔
- Burst set (all primes in `[a_n, b_n]`, `t`-length `1/n` at `t_n = e^{n²}`): block mass `≍ 1/n`,
  divergent; `π(a_n)/π(b_n+1) → 0` so limsup density `1`; the fresh window `[y_I(N), 2N]` has
  `t`-length `≈ 4 log log t = O(log n)` against block gaps `e^{(n+1)²} − e^{n²}`, so it meets at most
  one block and has mass `≤ C/n → 0`.  The abstract consumer (divergent + fresh mass to `2N → 0`)
  then gives normality.  Plausible mechanically: the contraction comes from the modelled mass
  `S_P(y) → ∞`, density zero was only KMT's way to keep the fresh mass small.  ✔

## 6. What I could not independently re-derive in this pass

The frozen Brun lower bound `brun_sifted_count_lower` (dimension `k`, level `x^{1/4}`, remainder
`R²`, relative error `2e^{−σ/2}`) and `primeRecipSum_le` (constants `8 + 12 log(·)`).  Both are
host-verified Lean theorems in frozen modules; I checked only that their hypotheses are met
(F1–F2, disjointness, `p > k`, `Q` coprime) and that the remainder `Σ_{d≤R} k^{ω(d)} ≪ R²` is the
right order.  A referee with more time should read `PrimeModelBrunCount.lean` once end to end.

## 7. One remark, not a defect

Part I's `C₂(k) = exp(exp(k+7))` exists only to make R1 and the sieve coefficient trivial; the
family theorems consume `window_bound_regime` directly.  The paper says this (Part III); a reader
who starts from the frozen statement alone will misjudge the reach by two logs, as the lane's own
"β > 2 frontier" episode shows.  Worth one sentence at the top of Part I.
