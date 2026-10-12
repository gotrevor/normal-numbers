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

- Lap 5 full-tuple phase checkpoint (`research/eb-positive`): the scoped file still has exactly
  two frozen proof debts, and the route-decisive good-modulus cosine bridge is now formalized.
  `scaled_residuePhase_le` assigns each of the other `2k-1` coordinates its share of the tail
  budget under `16|h|·2k ≤ b^K`; `scaled_anchor_phase_error` controls the finite-period
  correction; and `signed_tuple_phase_error` combines them with arbitrary tuple signs.
  `anchor_residue_of_dvd` identifies the anchored residue `p-(e+1)`, while
  `cos_tuplePhase_mod` proves residue reduction changes the tuple phase only by an integer.
  Consequently `tupleGoodModuli_cos_le` proves exactly
  `cos (2π tuplePhase) ≤ cos (π/b)` for every good modulus, for either sign of `h` and either
  half of the signed tuple.  No frozen statement or copied definition changed.
- Exact verification run (lap 5):
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `lake build NormalNumbers.CoefmassErdosBorweinPositive` (green, 8719 jobs).
  - `lake env lean AuditEBPositiveLap5.lean` with `#print axioms` for
    `scaled_residuePhase_le`, `scaled_anchor_phase_error`, `signed_tuple_phase_error`,
    `cos_tuplePhase_mod`, `anchor_residue_of_dvd`, and `tupleGoodModuli_cos_le` (temporary audit
    file removed; every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`, with
    `anchor_residue_of_dvd` not needing choice).
  - `git diff --check` (clean before the handoff edit).
  - `~/personal/bin/lean-green ~/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.tupleGoodModuli_cos_le`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly the canonical three).
- Previous checkpoints: lap 4 built the collision-modulus and spectral-product bridges; lap 3
  proved `shifted_gcd_divisor_moment`; lap 2 proved its complete finite shifted-gcd reduction;
  lap 1 proved `ebMoment_le_tupleAvg`, closing the infinite random-series side.
- Current blocker: `eb_weyl_moment_decay`.  The phase geometry is closed.  Its remaining content
  is the lower bound for retained good-modulus variance mass and the tuple exceptional-set estimate
  combining Hardy--Ramanujan with the shifted-gcd moments.  The final
  Borel--Cantelli/interpolation theorem remains downstream.
- Next highest-value attack: prove a retained-mass lemma for one anchor coordinate.  Lower-bound
  `∑ p∈tupleGoodModuli δ_p(1-δ_p)` by the weighted divisor mass of `n_i+e+1` above `P₀`,
  minus the collision loss controlled by `card_tupleBadModuli_le`; use `hvar`, monotonicity of
  `(log p)^{-a}` for `a ≥ 0`, and `p ≤ n_i+e+1`.  Then combine
  `tupleGoodModuli_cos_le` with `prod_bernMod_le_exp_neg_spectral` and begin the HR/Markov tuple
  exceptional-set bound.

## Findings

(none yet)
