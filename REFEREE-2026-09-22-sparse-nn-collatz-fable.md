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

## Addendum (later 2026-09-22): the sieve layer's skeleton, re-derived

`brun_sifted_count_lower` is the standard lower-bound sieve assembly, and its skeleton I did
re-derive: with weights `λ` satisfying `Σ_{E⊆B} λ_E ≤ [B = ∅]` for every `B ⊆ U`
(`weighted_counts_le_sifted`, the minorant property, swap-sums proof), the sifted count is
`≥ Σ_E λ_E · #{n : SieveCond(E)}`; `radical_sieve_count` replaces each count by
`X·h^{|E|}/(Q∏A∏E) ± h^{|E|}` (for `p > h` the `h` shifted classes mod `p` are distinct, so
`SieveCond(E)` is `h^{|E|}` CRT-disjoint classes mod `Q∏A∏E`, each counted to within one);
`brun_remainder_le_square` bounds the remainder by `R²` because `h^{|E|} ≤ ∏_{p∈E} p ≤ R`
(every `p > h`) and at most `R` distinct squarefree products are `≤ R`; and
`prime_density_brun_lower` supplies the main-term inequality
`(1 − 2e^{−s/2}) ∏_U (1 − h/p) ≤ Σ_E λ_E ∏_E (h/p)`.  Hypothesis chain checked:
`s ≥ 1920h = 80·(24h)`, `K = 4^h e^{16h}`, `hsA` identical, `g = h/p ∈ [0,1)` from `p > h`,
`U ⊆ (h, y]`, `y ≥ e²`.  The dimension instance `24h`, `K = 4^h e^{16h}` is the crude-Mertens
shape consistent with `primeRecipSum_le`'s `8 + 12 log(·)`.

Not re-derived: `brun_lower_three` inside `PrimeModelBrunLower.lean` (the Brun cut
`brunCut k s y` with geometric cutoffs and the `2e^{−s/2}` relative error), about 1200 lines,
host-verified.  That single theorem is the only analytic input in the whole chain that no reader
re-derived today; its statement is the fundamental lemma of sieve theory in a crude-constant
form, and every consumer uses it with hypotheses that hold with room to spare.

## Addendum 2 (2026-09-22, at Trevor's direction): `brun_lower_three` re-derived by hand

Scope: the one analytic input no reader had re-derived, `Brun.brun_lower_three` in
`PrimeModelBrunLower.lean`, plus its dimension instance `prime_density_dimension` and the
Mertens-type input `primeRecipSum_le`.  Read-only; every inequality below is my own derivation,
checked afterwards against the Lean proof's steps.  **No defect.**

**Statement (exact).**  `k ≥ 1`, `K ≥ 1`, `y ≥ e²`, `40 log K + 4 ≤ s`, `U ⊆ [0, y]`,
`0 ≤ g < 1` on `U`, `Dimension U g y K k` (for all real `1 ≤ t ≤ y`:
`∏_{p∈U, p>t}(1−g_p)^{−1} ≤ K (log y/ log max(2,t))^k`).  Conclusion:
`(1 − 2e^{−s/2}) ∏_U(1−g) ≤ Σ_E λ_E ∏_E g`, with `λ_E = (−1)^{|E|}[Adm E]`, `Adm` = every
element at an even position from the top (rank `2j`) is `≤ Y_j`, `Y_j = y` for `j ≤ J = ⌊s/4⌋`
and `Y_j = ⌊y^{α^{j−J}}⌋` for `j > J`, `α = 1 − 1/(20k)`.  Note: **property (3) does not use
`s ≥ 80k`**; only the support bound (property (1)) does.  The assembly passes both.

**1. First-failure decomposition** (`sum_not_adm_eq`).  A non-admissible `E` has a largest
failing element `q₀`; let `F = {p ∈ E : p ≥ q₀}`.  Then `F` is a *first failed prefix*:
`q₀ = min F` fails its cutoff, no element of `F` above `q₀` fails, and `|F|` is even (the rank of
`q₀` in `F` is `|F| − 1`, odd).  Ranks inside `F` equal ranks inside `E` (rank counts elements
above), so `F` is determined by `E`, and `E = F ⊔ S` with `S ⊆ below(B, F)`.  Conversely
`F ⊔ S` for any `S` below `F` is non-admissible with the same `F` (its top failure is still `q₀`).
Hence for any `f`:
`Σ_{E⊆B, ¬Adm}(−1)^{|E|}∏_E f = Σ_{F FirstFail} (−1)^{|F|}∏_F f · Σ_{S⊆below}(−1)^{|S|}∏_S f
 = Σ_F ∏_F f · ∏_{p∈B, p<min F}(1 − f_p)` (`|F|` even).  With `f = 1` each block is
`[below = ∅] ≥ 0`, giving the minorant `Σ_{E⊆B} λ_E ≤ [B = ∅]` (property (2)); with `f = g`,
`V − M = Σ_F ∏_F g ∏_{p<min F}(1−g_p) ≥ 0` (`defect_eq`).

**2. Structure of a first failed prefix** (`firstFail_struct`).  `|F| = 2m`; failing at position
`m` needs `q₀ > Y_m`; for `m ≤ J`, `Y_m = y ≥ q₀`, impossible, so `m > J`, `ℓ := m − J ≥ 1`, and
`q₀ ≥ ⌊y^{α^ℓ}⌋ + 1 > t_ℓ := y^{α^ℓ}`.  **Cutoff floors go the right way**: the floor only
lowers the cutoff, so failure implies `q₀ > t_ℓ` (real), which is what the tail bound uses; for
property (1) the floor is `≤ y^{α^{j−J}}`, which is what the support bound uses.

**3. Dimension bound** (`dim_prod_le`, `dim_sum_le`).  At `t = t_ℓ ∈ [1, y]`:
`log y/log max(2, t_ℓ) ≤ log y/log t_ℓ = α^{−ℓ}`, so
`∏_{p>t_ℓ}(1−g)^{−1} ≤ K α^{−kℓ} = e^{A+Bℓ}`, `A = log K`, `B = −k log α ≤ 1/19`
(from `−log(1−u) ≤ u/(1−u)`, `u = 1/(20k)`); and `Σ_{p>t_ℓ} g ≤ log ∏(1−g)^{−1} ≤ A + Bℓ`.

**4. Per-block estimate** (`block_le`).  Fix `n = 2m`, `ℓ = m − J`.  For `F` in the block,
`∏_{p<min F}(1−g) = V / ∏_{p≥min F}(1−g) ≤ V ∏_{p>t_ℓ}(1−g)^{−1} ≤ V e^{T}`, `T := A + Bℓ`,
and `F ⊆ W_ℓ := U ∩ (t_ℓ, ∞)`.  So the block is `≤ V e^{T} e_n(W_ℓ; g)`.  Elementary symmetric
bound: `x^n e_n ≤ ∏_{W}(1 + x g) ≤ exp(x Σ_W g) ≤ e^{xT}`, `x = n/T`: `e_n ≤ (eT/n)^n`.
Constants: `40A + 4 ≤ s < 4J + 4` gives `A < J/10`; `Bℓ ≤ ℓ/19 < ℓ/10`; so
`T < (J + ℓ)/10 = n/20`.  Hence block `≤ V e^{n/20} (e/20)^n = V (e^{1/20} e/20)^n ≤ V (1/4)^n`
(`e^{1/20}e/20 = 0.143`; the Lean lemma `exp_const_le` certifies `≤ 1/4`, with margin `1.75×`).

**5. Geometric tail** (`geom_tail_le`, assembly).  Blocks exist only for `n ≥ 2J + 2`:
`Σ_{n≥2J+2}(1/4)^n = (1/4)^{2J+2}·(4/3) = (1/16)^J/12 ≤ e^{−2J}/12 ≤ e^{2}e^{−s/2}/12 ≤ (16/12)e^{−s/2}
< 2e^{−s/2}`, using `1/16 ≤ e^{−2}`, `2J > s/2 − 2`, `e² ≤ 16`.  So `V − M ≤ 2e^{−s/2}V`.  ∎

**6. Support level** (`prod_le_rpow_of_adm`, needs `s ≥ 80k`).  In an admissible `E`
(decreasing `p₁ > p₂ > …`), `p_{2j} ≤ Y_j ≤ y^{α^{j−J}}` and `p_{2j+1} < p_{2j}`, `p₁ ≤ y`, so
`log ∏E / log y ≤ 1 + 2Σ_{j≥1} expo_j ≤ 1 + 2(J + α/(1−α)) = 2J + 40k − 1 ≤ s/2 + 40k − 1 ≤ s`
iff `s ≥ 80k − 2`; the hypothesis `s ≥ 80k` covers it.  (`sum_expo_le`: `Σ expo ≤ J + 20k − 1`.)

**7. Dimension instance** (`prime_density_dimension`: `g = h/p`, `U ⊆` primes in `(h, y]`,
`K = 4^h e^{16h}`, `k = 24h`).  Split at `2h`.  Small primes: `∏_{h<p≤2h} p/(p−h) ≤
∏_{h<m≤2h} m/(m−h) = C(2h, h) ≤ 4^h` (each factor `≥ 1`, so restricting to primes only helps).
Large primes: `u = h/p ≤ 1/2` gives `(1−u)^{−1} ≤ e^{2u}`, so the product is
`≤ exp(2h Σ_{max(v,2h)<p≤y} 1/p) ≤ exp(2h(8 + 12 log(log y/log v))) = e^{16h} L^{24h}`,
`L = log y/log max(2,t)`, using `primeRecipSum_le`.  Product: `4^h e^{16h} L^{24h}`.  Exact.

**8. Mertens-type input** (`primeRecipSum_le`): `Σ_{v<p≤y} 1/p ≤ 8 + 12 log(log y/log v)` for
`2 ≤ v ≤ y`, from blocks `[v^{2^i}, v^{2^{i+1}}]` each `≤ 8` (`block_le_eight`, a Chebyshev
upper bound; the true value is `log 2 + o(1)`), `n = ⌈log₂ L⌉ ≤ log₂L + 1` blocks, and
`8/log 2 = 11.54 ≤ 12`.  I did not re-derive `block_le_eight` from Chebyshev; it is a crude
constant with a factor `> 10` of room.

**Hypothesis chain into the consumer** (`brun_sifted_count_lower` → `prime_density_brun_lower`
→ `brun_lower_fundamental`): `s ≥ 1920h = 80·(24h)`; `hsA` identical with `K = 4^h e^{16h}`;
`y ≥ e²`; `U` primes in `(h, y]` so `g ∈ [0,1)`; `Dimension` from §7 (needs `y ≥ 2`).  All met.
In the assembly `s = σ = log x/(4 log y) ≥ 1/(4ε) ≥ 1920k` under `ε ≤ 1/(7680k)`, and
`40 log(4^k e^{16k}) + 4 = 40k(log 4 + 16) + 4 ≈ 695k + 4 ≤ 1920k`.  Room everywhere.

**Verdict.**  `brun_lower_three` is a correct crude-constant fundamental lemma of the Brun
sieve, and its Lean proof follows the derivation above step for step (`T ≤ n/20`,
`e^{1/20}e/20 ≤ 1/4`, `(1/16)^J ≤ e^{−2J}`, `e² ≤ 16`).  With this, every analytic input of the
sparse-NN chain has now been re-derived by at least one reader; the only remaining
not-re-derived lemma is the Chebyshev block constant `block_le_eight`.
