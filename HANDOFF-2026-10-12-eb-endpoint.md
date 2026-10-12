# HANDOFF: prove the EB growing-moment criterion (CoefmassErdosBorweinEndpoint.lean)

**Branch `research/eb-endpoint` is LOCAL ONLY.  Never `git push`.**  The repo is public, and this is
private research.

## Objective

Make `src/NormalNumbers/CoefmassErdosBorweinEndpoint.lean` sorry-free.  `#print axioms
NormalNumbers.ErdosBorweinEndpoint.ebRandom_ae_normal_of_divisorVariance_diverges` must show only
`propext`, `Classical.choice` and `Quot.sound`.

- Do not edit the statements of `divisorVarianceMass`, `collisionCutoff` or
  `ebRandom_ae_normal_of_divisorVariance_diverges`.  They are verbatim copies of a frozen statement.
- Helpers are free.  Do not edit `CoefmassErdosBorweinPositive.lean` (import it; copy-and-adapt a
  lemma into the new module if it needs a different shape).
- If the statement is FALSE as written, put a counterexample under "Findings" here, then stop.

## Reuse (proved, `NormalNumbers.ErdosBorweinPositive`, in `CoefmassErdosBorweinPositive.lean`)

- `BernoulliLawNat`, `ebLambert`, `weylMean`, `measurable_ebLambert`, `norm_weylMean_le_one`,
  `weylMean_eq_weylAvg`.
- **Moment to tuples:** `ebMoment_le_tupleAvg` (E|weylMean|^{2k} ≤ tuple average of ∏ bernMod).
- **Good moduli:** `tupleGoodModuli`, `mem_tupleGoodModuli`, `anchor_residue_of_dvd`,
  `tupleGoodModuli_cos_le`, `signed_tuple_phase_error`, `cos_tuplePhase_mod`.
- **Contraction:** `bernMod_le_exp_of_cos_le`, `prod_bernMod_le_exp_neg_spectral`,
  `spectralConst_pos`, `tupleGoodModuli_bernMod_product_le`, `global_bernMod_product_le_good_anchor`
  (note: that one is specialised to the power lower bound; you need the general version with the
  mass `Σ_{m ∈ good} v_m`, so copy and generalize).
- **Counting:** `card_shifted_multiples_le`, `card_shifted_multiples_real_le`.
- **Assembly:** `ae_tendsto_weylMean_of_moment_decay` (FIXED k, polylog decay; you need a
  growing-k variant), `summable_log_slowSchedule_rpow`, the final part of
  `ebRandom_ae_normal_below_ln2_of_HR` (countable intersection + `isNormal_of_weylAvg`).

## Paper proof (subagent-reviewed, 85%)

Fix `b ≥ 2`, `h ≠ 0`; write `|h| = b^e·m'` with `b ∤ m'` and set `a₀ = e + 1` (the convention of
`global_bernMod_product_le_good_anchor`).  For moment order `k`, pick `K ≥ a₀` with
`16|h|·2k ≤ b^K`; require `2K ≤ P₀`.

1. **Per-tuple bound.**  For a tuple `n : Fin (2k) → Fin N`, let `G(n)` = number of
   `(i, j, r, m)` with `i ≠ j`, `1 ≤ r ≤ K`, `m > P₀`, `m ∣ n_i + a₀`, `m ∣ n_j + r`.
   - If `G(n) = 0`, every `m > P₀` dividing some `n_i + a₀` is good for that `i` (exactly one `i`;
     the case `r = a₀` rules out two anchors), so
     `∏ bernMod ≤ exp(-c_b Σ_i W(n_i))`, where `W(n) = divisorVarianceMass v P₀ (n + a₀)` and
     `c_b = spectralConst b`.  (Good sets for different `i` are disjoint.)
   - If `G(n) ≥ 1`, bound the product by 1.
2. **Moment bound.**
   `E|A_N|^{2k} ≤ φ_N^{2k} + E_tuple G`, with `φ_N = (1/N)Σ_{n<N} exp(-c_b W(n))` (independence of
   coordinates: the tuple average of a product of per-coordinate functions factors).
   `E_tuple G ≤ (2k)²K Σ_{P₀ < m ≤ N+K} (1/m + 1/N)² ≤ 4k²K(3/P₀ + 4/N)`.
3. **φ_N → 0 from `hdiv`.**  For `T > 0`: `φ_N ≤ (density of W ≤ T) + exp(-c_b T)`.  Both are
   small.  Mind the indexing: `hdiv` uses `n ∈ Icc 1 N`, the tuple average uses `Fin N`; shift
   `a₀` by one if convenient (`hdiv` holds for EVERY `a₀`).  And `P₀ = collisionCutoff N`.
4. **Borel–Cantelli.**  `N_j = ⌈exp √j⌉`, `k_j = ⌈log j⌉` (or any `k_j → ∞` with
   `k_j ≥ log j` and `k_j = O(log j)`), `K_j = a₀ + ⌈log_b(32|h|k_j)⌉`.
   - Markov: `P(|A_{N_j}| ≥ ε) ≤ ε^{-2k_j}(φ^{2k_j} + 4k_j²K_j(3/P₀ + 4/N_j))`.
   - `P₀(N_j) ≈ exp((log √j)²) = j^{(log j)/4}` beats every polynomial; `ε^{-2k_j}` is
     polynomial in `j`.  Once `φ_{N_j} ≤ ε/e` the first term is `≤ j^{-2}`.
   - Interpolate: `N_{j+1}/N_j → 1`.
   - It is fine to prove "for each `ε` rational, eventually `|A_{N_j}| < ε` a.s." and intersect.
5. **Headline.**  Countable intersection over `h ≠ 0` and `b ≥ 2`, then `isNormal_of_weylAvg`, as in
   the end of `ebRandom_ae_normal_below_ln2_of_HR`.

## Findings

(none yet)
