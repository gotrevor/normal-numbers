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

- Lap 12 completion checkpoint (`research/eb-positive`): the scoped module is sorry-free and the
  conditional positive-side theorem is complete.  The adversarial review reconstructed the route
  from the frozen statements and exposed one genuine implementation mismatch:
  `ebMoment_le_tupleAvg` had accidentally fixed `Ω : Type` while the frozen headline quantifies
  over `Ω : Type*`; the helper is now universe-polymorphic, with no mathematical statement
  change.  `normalized_exceptionalTuples_le` cancels the tuple-box factor exactly and leaves the
  Hardy--Ramanujan power and collision Markov power.  The stretched-exponential comparison and
  finite-initial-segment absorption then close `eb_weyl_moment_decay`.  Finally,
  `summable_log_slowSchedule_rpow` and `ae_tendsto_weylMean_of_moment_decay` reuse the checked
  slow schedule/interpolation machinery to obtain all Weyl limits on a countable intersection;
  `QSpanCriterion.isNormal_of_weylAvg` closes
  `ebRandom_ae_normal_below_ln2_of_HR`.  No frozen definition or theorem statement changed, and
  `HardyRamanujanLowerTail` remains an explicit hypothesis exactly as required.
- Exact verification run (lap 12):
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; no `sorry`
    warnings).
  - `rg -n '\bsorry\b|sorryAx' src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (no matches).
  - `git diff --check` (clean before the handoff edit).
  - `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.ebRandom_ae_normal_below_ln2_of_HR`
    (`FORMALIZE-TIER GREEN`, 8877 jobs; headline axioms exactly `propext`, `Classical.choice`, and
    `Quot.sound`).
- Current blocker: none in the scoped objective.  The host predicate
  `sorry-free:src/NormalNumbers/CoefmassErdosBorweinPositive.lean` is met.
- Next highest-value attack: no in-scope attack remains.  The distinct unconditional theorem in
  the private packet would require formalizing the named Hardy--Ramanujan literature input; do not
  turn that input into an axiom or silently broaden this completed conditional campaign.
- Lap 11 scalar contraction checkpoint (`research/eb-positive`): the asymptotic and deterministic
  rich/light bookkeeping needed by `eb_weyl_moment_decay` is now kernel-checked.
  `eventually_retained_log_power` proves that a logarithmic divisor supply of exponent `s` absorbs
  both the fixed cutoff and a collision threshold `(log N)^η` whenever `η < s - a`, and
  `eventually_retained_log_power_nat` ports this estimate to the shifted scale `log (N + u)`.
  `retained_log_mass_ge_of_rich_light` combines that scalar estimate with
  `log_rpow_lt_two_pow_primeFactors`, including the negative-power comparison between the anchor
  and endpoint scales.  `exists_moment_parameters` and `exists_eb_decay_parameters` simultaneously
  choose the Hardy--Ramanujan exponent, threshold exponent, Weyl moment, and collision moment so
  both exceptional powers are strictly greater than two.  Finally,
  `global_bernMod_product_le_rich_light` feeds the retained mass into the lap-10 global-product
  bridge and proves the uniform `exp (-spectralConst b * (c * (log (N+e+1))^η))` bound for every
  rich/light tuple.  Thus the entire nonexceptional-tuple contraction branch is closed.  No frozen
  statement or copied definition changed; the scoped file still has exactly its two frozen proof
  debts.
- Lap 10 finite exceptional-set checkpoint (`research/eb-positive`): the finite tuple split needed
  by `eb_weyl_moment_decay` is now kernel-checked.  `poorCoordinates` and `poorTuples` define the
  shifted Hardy--Ramanujan lower-tail set and its coordinatewise product;
  `card_poorTuples` proves its cardinality is exactly the `2k`-th power and
  `poorTuples_card_le_of_HR` raises the shifted HR estimate to that power.
  `collisionHeavyTuples` isolates a fixed anchor whose collision loss exceeds a real threshold,
  and `card_collisionHeavyTuples_mul_pow_le` is the exact finite Markov inequality driven by
  `tupleBadModuli_moment`.  Their union `exceptionalTuples` has the expected union bound, while
  `exists_rich_light_anchor_of_not_mem_exceptional` produces a rich coordinate with sub-threshold
  collision loss on every complementary tuple.  `sum_le_card_exceptional_add_uniform` packages
  the final exceptional/complement sum split.  Finally,
  `global_bernMod_product_le_good_anchor` closes the fixed-set mismatch in
  `ebMoment_le_tupleAvg`: the common truncation `range (N+e+1)` contains each tuple-dependent
  good-modulus image and therefore inherits its exponential contraction.  No frozen statement or
  copied definition changed; the scoped file still has exactly its two frozen proof debts.
- Lap 9 reflection / shifted Hardy--Ramanujan checkpoint (`research/eb-positive`): the scoped file
  still has exactly two frozen proof debts.  The analytic input now has the exact interface needed
  by zero-based tuple coordinates.  `hardyRamanujanExponent_pos` proves positivity of the
  lower-tail rate, `exists_hardyRamanujan_parameters` simultaneously chooses
  `a / log 2 < α < 1` and an admissible positive tail exponent, and
  `shifted_hardyRamanujanLowerTail` bounds the poor coordinates `n : Fin N` after the shift
  `n.val + u`.  Its proof injects into the one-based interval through endpoint `N + u` and absorbs
  the enlargement into the fixed factor `u + 1`; monotonicity of the negative log power loses
  nothing.  `log_rpow_lt_two_pow_primeFactors` then converts the complementary rich-coordinate
  inequality into the required squarefree-divisor supply.  No frozen statement or copied
  definition changed.
- Reflection audit: the reviewed private source note and frozen packet still agree verbatim with
  this module's assumptions and headline statements.  The tuple-dependent finite good-modulus set
  is selected before the independent Bernoulli factors are split, so the existing architecture has
  no hidden independence mismatch.  The reusable slow-schedule/interpolation machinery is already
  present elsewhere in the repository.  The finite exceptional split and its nonexceptional
  contraction are now closed; the route-decisive open work is the normalized moment assembly.
- Exact verification run (lap 11):
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `git diff --check` (clean before the handoff edit).
  - `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.global_bernMod_product_le_rich_light`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly `propext`, `Classical.choice`, and
    `Quot.sound`).
- Exact verification run (lap 10):
  - `lake env lean src/NormalNumbers/CoefmassErdosBorweinPositive.lean` (green; exactly the two
    remaining disclosed `sorry` warnings).
  - `git diff --check` (clean before the handoff edit).
  - `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/nn-eb-positive --target
    NormalNumbers.CoefmassErdosBorweinPositive --import
    NormalNumbers.CoefmassErdosBorweinPositive --axioms
    NormalNumbers.ErdosBorweinPositive.global_bernMod_product_le_good_anchor`
    (`FORMALIZE-TIER GREEN`, 8719 jobs; theorem axioms exactly `propext`, `Classical.choice`, and
    `Quot.sound`).
- Previous checkpoints: lap 8 proved arbitrary moments of the tuple collision loss; lap 7 proved
  the exact deterministic tuple-product contraction; lap 6 proved the complete one-anchor
  retained-variance mass lower bound; lap 5 proved the full-tuple good-modulus cosine gap; lap 4
  built the collision-modulus and spectral-product bridges; lap 3 proved
  `shifted_gcd_divisor_moment`; lap 2 proved its complete finite shifted-gcd reduction; lap 1
  proved `ebMoment_le_tupleAvg`, closing the infinite random-series side.
- Current blocker: `eb_weyl_moment_decay`.  Parameter selection, the finite tuple partition, and
  the complete uniform contraction of every nonexceptional tuple are now proved.  What remains is
  the final normalized finite-sum inequality: divide the poor-tuple bound and the `2k` fixed-anchor
  Markov bounds by `N^(2k)`, use `T_N^R = (log (N+e+1))^(ηR)`, and dominate the poor, collision,
  and stretched-exponential terms by one negative log power `q_out > 2`.  The finite initial
  segment must then be absorbed into the output constant.  The final Borel--Cantelli/interpolation
  theorem remains downstream.
- Next highest-value attack: assemble the eventual-`N` half of `eb_weyl_moment_decay` directly
  from `ebMoment_le_tupleAvg`, `poorTuples_card_le_of_HR`, `tupleBadModuli_moment`,
  `card_collisionHeavyTuples_mul_pow_le`, `card_exceptionalTuples_le`,
  `sum_le_card_exceptional_add_uniform`, and
  `global_bernMod_product_le_rich_light`.  First add a normalized exceptional-card lemma so the
  powers of `N` cancel once, then a scalar domination lemma for the three remaining terms.  Finish
  by taking the maximum over the finite range below the eventual cutoff.  This should close the
  first frozen proof debt without further mathematical input.

## Findings

(none yet)
