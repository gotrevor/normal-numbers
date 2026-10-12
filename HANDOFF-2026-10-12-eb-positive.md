# HANDOFF: prove the EB positive side, conditional on Hardy–Ramanujan (CoefmassErdosBorweinPositive.lean)

**Branch `research/eb-positive` is LOCAL ONLY.  Never `git push`.**  The repo is public, and this is
private research.

## Objective

Make `src/NormalNumbers/CoefmassErdosBorweinPositive.lean` sorry-free.  `#print axioms` must show
only `propext`, `Classical.choice` and `Quot.sound`.

- `HardyRamanujanLowerTail` is a `def ... : Prop`, a named literature input.  It stays a HYPOTHESIS:
  never prove it by `sorry`, never turn it into an `axiom`, and never drop it.
- Do not edit the statements of `BernoulliLawNat`, `ebLambert`, `HardyRamanujanLowerTail`,
  `shifted_gcd_divisor_moment`, `weylMean`, `eb_weyl_moment_decay` or
  `ebRandom_ae_normal_below_ln2_of_HR`.  They are verbatim copies of reviewed statements.
- Helpers are free.  A FALSE statement gets a counterexample under "Findings", then stop.

## Reuse (proved, `NormalNumbers.RandomLambertMoment`, general modulus, no primality)

- **Separation:** `anchor_phase_formula`, `anchor_tail_cos_le`, `cos_two_pi_le_of_near_rational`.
- **Bernoulli factor and phase algebra:** `bernMod_sq`, `bernMod_le_one`, `bernMod_neg`,
  `ePh_add_int`, `ePh_add`.
- **Weyl expansion:** `weylMean_even_expansion`, `tuple_ePh_weyl_sum`.
- **Bernoulli integrals:** `integral_ePh_finset_sum`, `norm_integral_ePh_finset_sum`,
  `norm_integral_ePh_add_randomLambert_le`, `summable_lambert_denom`.  These are `Prime`-indexed;
  port them to `ℕ` indices with the same proofs (copy and adapt inside this module).
- **Normality:** `NormalNumbers.isNormal_of_weylAvg` (QSpanCriterion.lean ~l.809), and
  `weylAvg` ↔ the local `weylMean`.

## Paper proof (codex2-accepted, 95%; note section "Below ln 2")

Fix `b ≥ 2` and `h ≠ 0`, with `a₀ = 1 + v_b(h)`.  Pick `K ≥ a₀` with `b^K ≥ 16|h|·2k`, and
`P₀ = 2K`.

1. **`shifted_gcd_divisor_moment`.**
   - `τ(gcd(n+u, m+v))^r ≤ Σ_{d ∣ gcd} τ(d)^r`, since `d = gcd` is one of the terms.
   - Use `P(d ∣ n+u, d ∣ m+v) ≤ (1/d + 1/N)² ≤ 9/d²` for `d ≤ 2N`, and `Σ_d τ(d)^r/d² < ∞`.
2. **Good set (per tuple).**  For a `2k`-tuple `n`, call `m > P₀` good for coordinate `i` if:
   - `m ∣ n_i + a₀`;
   - no other coordinate `j` has `n_j mod m ∈ {m-1, …, m-K}`.

   For each good `m`, the phase `h Σ_j ε_j α_m(n_j)` is at least `1/(2b)` from `ℤ`, by
   `anchor_tail_cos_le` with `p := m`.  So `bernMod δ_m (…) ≤ exp(-c_b v_m)`, using
   `bernMod_sq`.  The good set is chosen from the TUPLE, not the coins.  Independence splits off
   its finite Bernoulli factors, and the remainder has modulus at most 1.
3. **Mass.**
   - `W_i = Σ_{good m for i} v_m ≥ Σ_{P₀ < m ∣ n_i + a₀} v_m - B`.
   - Here `B = Σ_{j ≠ i, 1 ≤ r ≤ K} τ(gcd(n_i + a₀, n_j + r))`, because every excluded `m` divides
     such a gcd and `v_m ≤ 1/4`.
   - `Σ_{P₀ < m ∣ n+a₀} v_m ≥ c (log(N + a₀))^{-a} (2^{ω(n+a₀)} - P₀)`, using `a ≥ 0` and
     `m ≤ N + a₀`.
4. **Moment.**  Choose `α ∈ (a/ln 2, 1)`, `0 < η < α ln 2 - a`, `T = (log N)^η`, `q < Q(α)` with
   `kq > 1`, and `R > 2kq/η`.  Then
   `E|A_N|^{2k} ≤ p_N^{2k} + O((log N)^{-ηR}) + exp(-c_b T)`.
   - `p_N ≤ C(log N)^{-q}` by `hHR`, since the coordinates are independent and uniform.
   - The middle term comes from Markov on `E B^R`, via `shifted_gcd_divisor_moment`.
   - This is `eb_weyl_moment_decay` with exponent `2kq > 2`.
5. **Headline.**  Markov, then Borel–Cantelli along `⌊exp √j⌋`, then interpolation, then a
   countable intersection, then `isNormal_of_weylAvg`.

Expect step 4 to be the longest.  Splitting it into named leaves is progress.

## Gates

- Compile: `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean`.  If the import's
  olean is missing: `lake build NormalNumbers.CoefmassRandomLambertMoment`.
- One green checkpoint per lap.  Update "Status", commit, NEVER push.

## Status

- Lap 6 retained-variance checkpoint (`research/eb-positive`): the scoped file still has exactly
  two frozen proof debts.  The complete one-anchor mass lower bound is now formalized.
  `two_pow_primeFactors_card_le_card_divisors` proves `2^ω(M) ≤ τ(M)`;
  `card_divisors_le_cutoff_add_large` loses at most `P₀` divisors at the cutoff; and
  `card_large_anchor_moduli_eq_good_add_bad` gives the exact good/bad partition.  The analytic
  leaf `tupleGoodModuli_variance_mass` uses `p ∣ n_i+a₀`, `p ≤ n_i+a₀`, and antitonicity of
  `x ↦ x^(-a)` to freeze every good factor at the anchor scale.  Consequently
  `retained_variance_mass_le` proves
  `c(log(n_i+a₀))^(-a) (2^ω(n_i+a₀)-P₀-#bad) ≤ Σ_good δ_p(1-δ_p)`.
  Together with `card_tupleBadModuli_le`, this is exactly the retained-mass estimate prescribed
  by step 3.  No frozen statement or copied definition changed.
- Exact verification run (lap 6):
  - Shared-store preflight: `lake-base status leanprover/lean4:v4.33.1` and `lake-base status
    v4.33.1` both reported that no shared store exists; no relink was available.
  - `lake env lean _EBRetainedProbe.lean` (green kernel probe for the five-lemma chain; temporary
    file removed).
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `git diff --check` (clean before the handoff edit).
  - `~/personal/bin/lean-green ~/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.retained_variance_mass_le`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly `propext`, `Classical.choice`, and
    `Quot.sound`).
- Previous checkpoints: lap 5 proved the full-tuple good-modulus cosine gap; lap 4 built the
  collision-modulus and spectral-product bridges; lap 3 proved `shifted_gcd_divisor_moment`; lap 2
  proved its complete finite shifted-gcd reduction; lap 1 proved `ebMoment_le_tupleAvg`, closing
  the infinite random-series side.
- Current blocker: `eb_weyl_moment_decay`.  The phase geometry and one-anchor retained mass are
  closed.  Its remaining content is the deterministic tuple-product contraction and the tuple
  exceptional-set average combining Hardy--Ramanujan with the shifted-gcd moments.  The final
  Borel--Cantelli/interpolation theorem remains downstream.
- Next highest-value attack: prove the deterministic per-tuple product bridge combining
  `tupleGoodModuli_cos_le`, `prod_bernMod_le_exp_neg_spectral`, and
  `retained_variance_mass_le`.  The selected set passed to `ebMoment_le_tupleAvg` is zero-based
  (`m` contributes the Bernoulli factor at `m+1`), whereas `tupleGoodModuli` contains the actual
  moduli `p`; therefore reindex it injectively by `p ↦ p-1` (all good `p ≥ 2`) and prove
  `(p-1)+1=p` explicitly.  Once that bridge is in place, split tuples according to the HR lower
  tail and a Markov threshold for the `card_tupleBadModuli_le` shifted-gcd sum.

## Findings

(none yet)
