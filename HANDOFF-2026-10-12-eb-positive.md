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

- Lap 7 deterministic-contraction checkpoint (`research/eb-positive`): the scoped file still has
  exactly two frozen proof debts.  `spectralConst_pos` proves the fixed cosine gap is positive.
  The new load-bearing theorem `tupleGoodModuli_bernMod_product_le` completes the bridge requested
  by lap 6: it injectively reindexes every actual good modulus by `p ↦ p - 1`, proves
  `(p - 1) + 1 = p` from `p > P₀ ≥ 1`, applies `tupleGoodModuli_cos_le` and
  `prod_bernMod_le_exp_neg_spectral`, and inserts `retained_variance_mass_le` with the correct
  inequality direction.  Thus the exact zero-based product accepted by `ebMoment_le_tupleAvg` is
  bounded by the exponential of
  `-spectralConst b * c(log(n_i+a₀))^(-a) (2^ω(n_i+a₀)-P₀-#bad)`.
  No frozen statement or copied definition changed.
- Exact verification run (lap 7):
  - Shared-store check: `/Users/gotrevor/personal/bin/lake-base status
    leanprover/lean4:v4.33.1` and `/Users/gotrevor/personal/bin/lake-base status v4.33.1` both
    reported that no shared store exists; no relink is available.
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `git diff --check` (clean before the handoff edit).
  - `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.tupleGoodModuli_bernMod_product_le`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly `propext`, `Classical.choice`, and
    `Quot.sound`).
- Previous checkpoints: lap 6 proved the complete one-anchor retained-variance mass lower bound;
  lap 5 proved the full-tuple good-modulus cosine gap; lap 4 built the collision-modulus and
  spectral-product bridges; lap 3 proved `shifted_gcd_divisor_moment`; lap 2 proved its complete
  finite shifted-gcd reduction; lap 1 proved `ebMoment_le_tupleAvg`, closing the infinite
  random-series side.
- Current blocker: `eb_weyl_moment_decay`.  The phase geometry and one-anchor retained mass are
  now closed through the deterministic tuple-product contraction.  Its remaining content is the
  tuple exceptional-set average combining Hardy--Ramanujan with high moments of the shifted-gcd
  collision loss.  The final Borel--Cantelli/interpolation theorem remains downstream.
- Next highest-value attack: prove the high-moment tuple collision estimate needed for Markov.
  Raise `card_tupleBadModuli_le` to a fixed positive power `R`, dominate the power of its finite
  `(j,r)` sum by a constant times the sum of the `R`-th powers, and sum over all tuples.  The two
  active coordinates are controlled by `shifted_gcd_divisor_moment`; the other `2k-2` coordinates
  contribute only powers of `N`.  Then combine that estimate with `hHR` to split the tuple average
  into the all-poor anchor event, the large-collision event, and the exponentially contracted
  complement.

## Findings

(none yet)
