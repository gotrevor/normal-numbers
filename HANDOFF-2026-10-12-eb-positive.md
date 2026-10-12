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

- Lap 3 divisor-series checkpoint (`research/eb-positive`): `shifted_gcd_divisor_moment` is now
  proved, so the scoped file has exactly two frozen proof debts.  The new prime-power induction
  proves
  `τ(n)^r ≤ ((ζ : ArithmeticFunction ℕ) ^ (2^r)) n`: at the successor step the convolution
  splits into `e + 1` terms and each term dominates `(e + 1)^r`.  Multiplicativity extends this
  to general `n`.  Repeated `ArithmeticFunction.LSeriesSummable_mul` then proves that every
  positive convolution power of zeta is summable at `s = 2`; coefficient casting and comparison
  give `summable_divisorCard_pow_div_sq`.  Applying the lap-2 reduction closes the first frozen
  theorem.  A fresh-history review found no statement drift and no break in the advertised route;
  no frozen statement or copied definition changed.
- Exact verification run (lap 3):
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassErdosBorweinPositive` (green, 8719 jobs).
  - `lake env lean AuditEBPositiveLap3.lean` with `#print axioms` for
    `divisorCard_pow_le_zetaPow_primePow`, `divisorCard_pow_le_zetaPow`,
    `natCast_zetaPow_apply`, `summable_zetaPow_div_sq`,
    `summable_divisorCard_pow_div_sq`, and `shifted_gcd_divisor_moment` (temporary audit file
    removed; every declaration exactly `[propext, Classical.choice, Quot.sound]`).
  - `git diff --check` (clean).
  - `~/personal/bin/lean-green ~/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.shifted_gcd_divisor_moment`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly the canonical three).
- Previous checkpoints: lap 2 proved the complete finite shifted-gcd reduction; lap 1 proved
  `ebMoment_le_tupleAvg`, closing the infinite random-series side and reducing every even Weyl
  moment to a finite tuple average of `bernMod` products.
- Current blocker: `eb_weyl_moment_decay`.  Its remaining content is now precisely the
  deterministic good-modulus phase contraction, the lower bound for good-modulus variance mass,
  and the tuple exceptional-set estimate combining Hardy--Ramanujan with the proved shifted-gcd
  moments.  The final Borel--Cantelli/interpolation theorem remains downstream.
- Next highest-value attack: define the per-tuple good-modulus finset and prove its one-coordinate
  contraction leaf using `anchor_phase_formula`, `anchor_tail_cos_le`,
  `cos_two_pi_le_of_near_rational`, and `bernMod_sq`.  Then prove the bad-modulus mass loss is
  bounded by the advertised shifted-gcd divisor sums; this is the bridge from the now-closed
  moment theorem to the Markov estimate in `eb_weyl_moment_decay`.

## Findings

(none yet)
