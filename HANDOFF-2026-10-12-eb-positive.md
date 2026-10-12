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

- Lap 4 good-modulus checkpoint (`research/eb-positive`): the scoped file still has exactly two
  frozen proof debts, but both deterministic bridges advertised for `eb_weyl_moment_decay` are
  now formalized.  `tupleGoodModuli` and `tupleBadModuli` encode the anchor divisors and collision
  exclusions.  `bad_modulus_dvd_shifted_gcd` constructs the exact shift
  `r = p - (n_j mod p) ∈ [1,K]`, and `card_tupleBadModuli_le` puts every collision modulus in
  the finite union of shifted-gcd divisor sets, giving the required divisor-count loss bound.
  Independently, `bernMod_le_exp_of_cos_le` turns any cosine gap into exponential Bernoulli
  variance decay, and `prod_bernMod_le_exp_neg_spectral` multiplies the good-modulus bounds into
  the exponential of their total variance.  No frozen statement or copied definition changed.
- Exact verification run (lap 4):
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassErdosBorweinPositive` (green, 8719 jobs).
  - `lake env lean AuditEBPositiveLap4.lean` with `#print axioms` for
    `mem_tupleGoodModuli`, `bad_modulus_dvd_shifted_gcd`, `card_tupleBadModuli_le`,
    `bernMod_le_exp_of_cos_le`, `bernMod_le_exp_spectral_of_cos_le`, and
    `prod_bernMod_le_exp_neg_spectral` (temporary audit file removed; every declaration exactly
    `[propext, Classical.choice, Quot.sound]`).
  - `git diff --check` (clean).
  - `~/personal/bin/lean-green ~/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.card_tupleBadModuli_le`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly the canonical three).
- Previous checkpoints: lap 3 proved `shifted_gcd_divisor_moment`; lap 2 proved its complete finite
  shifted-gcd reduction; lap 1 proved `ebMoment_le_tupleAvg`, closing the infinite random-series
  side and reducing every even Weyl moment to a finite tuple average of `bernMod` products.
- Current blocker: `eb_weyl_moment_decay`.  Its remaining content is now precisely the
  good-modulus phase cosine bound for the full signed `2k`-tuple, the lower bound for its retained
  variance mass, and the tuple exceptional-set estimate combining Hardy--Ramanujan with the
  shifted-gcd moments.  The final Borel--Cantelli/interpolation theorem remains downstream.
- Next highest-value attack: prove that membership in `tupleGoodModuli` forces
  `cos (2π tuplePhase) ≤ cos (π/b)`.  Factor `|h| = b^e m`, use the anchored residue
  `p-(e+1)`, and generalize `anchor_tail_phase_error` from one tail to the signed sum of the other
  `2k-1` coordinates under `b^K ≥ 16|h|·2k`.  Then apply
  `prod_bernMod_le_exp_neg_spectral` and subtract `card_tupleBadModuli_le` from the anchor-divisor
  variance mass.

## Findings

(none yet)
