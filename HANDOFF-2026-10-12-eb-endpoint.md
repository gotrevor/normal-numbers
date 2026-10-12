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

## Lap checkpoint (2026-10-12, deterministic no-collision contraction)

Concrete advance in `CoefmassErdosBorweinEndpoint.lean`:

- Added the finite predicate `TupleCollisionFree` matching the paper's absence of a large common
  divisor between an anchor and any shifted second coordinate.
- Proved that collision freedom makes every divisor above `P₀` good
  (`tupleGoodModuli_eq_large_divisors_of_collisionFree`) and hence identifies its weighted sum
  exactly with `divisorVarianceMass`
  (`sum_tupleGoodModuli_eq_divisorVarianceMass_of_collisionFree`).
- Proved good-modulus sets at distinct anchors are disjoint (`disjoint_tupleGoodModuli`) and that
  mass over their union is the sum of all coordinate masses (`sum_tupleAllGoodModuli`).
- Generalized the existing positive-exponent contraction to actual Bernoulli variance mass, first
  for one anchor and then for the union of all anchors.  The capstone
  `global_bernMod_product_le_divisorVarianceMass_of_collisionFree` now proves the paper's full
  per-tuple no-collision bound
  `product ≤ exp (-spectralConst b * Σ_i divisorVarianceMass ...)`.

Verification run before this handoff update:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpoint.lean
```

It succeeds; the only warning is the disclosed `sorry` on the frozen headline.

Final repository gate (explicit import is required when targeting a single module):

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpoint \
  --import NormalNumbers.CoefmassErdosBorweinEndpoint \
  --axioms NormalNumbers.ErdosBorweinEndpoint.global_bernMod_product_le_divisorVarianceMass_of_collisionFree
```

Verdict: `FORMALIZE-TIER GREEN`; the capstone depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

Current blocker: turn `¬ TupleCollisionFree` into the finite union over `(i,j,r,p)` and prove the
normalized bad-tuple count bounded by the paper's
`4 k² K (3 / P₀ + 4 / N)`.  This is now the route-decisive bridge between the proved deterministic
contraction and `ebMoment_le_tupleAvg`.

Next highest-value attack: define the finite collision tuple set with `p ≤ N + K`, prove each
fixed `(i,j,r,p)` fiber has cardinality at most
`N^(2k-2) * (N/p + 1)^2` using `card_shifted_multiples_le`, sum the fibers, and combine its
complement with `global_bernMod_product_le_divisorVarianceMass_of_collisionFree`.

## Lap checkpoint (2026-10-12, finite collision union and count)

Concrete advance in `CoefmassErdosBorweinEndpoint.lean`:

- Proved the sharp single-coordinate residue-class count `card_fin_dvd_add_le` directly for
  `Fin N`: at most `N / p + 1` values satisfy `p ∣ n + a`.
- Defined `tupleCollisionFiber` and proved `card_tupleCollisionFiber_le`; a fixed ordered
  `(i,j,r,p)` collision has at most
  `(N / p + 1)^2 * N^(2*k-2)` tuples.  The proof identifies the fiber with a dependent
  `Fintype.piFinset`, so the `2*k-2` unrestricted-coordinate exponent is exact.
- Defined the full finite `tupleCollisionSet` over distinct ordered coordinates, shifts
  `r ∈ [1,K]`, and moduli `p ∈ (P₀,N+K]`.  Proved
  `mem_tupleCollisionSet_iff_not_collisionFree`: the finite union is exactly the complement of
  `TupleCollisionFree`; the upper cutoff follows from `p ∣ n_j+r > 0`.
- Summed the fibers with `Finset.card_biUnion_le`.  The capstone
  `card_tupleCollisionSet_le` gives
  `(2k)(2k-1)K * Σ_{P₀<p≤N+K} (N/p+1)^2 N^(2k-2)`.

Verification run before this handoff update:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpoint.lean
```

It succeeds; the only proof-debt warning in the target is the frozen headline.

Repository gate and axiom audit:

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpoint \
  --import NormalNumbers.CoefmassErdosBorweinEndpoint \
  --axioms NormalNumbers.ErdosBorweinEndpoint.card_tupleCollisionSet_le \
  --axioms NormalNumbers.ErdosBorweinEndpoint.mem_tupleCollisionSet_iff_not_collisionFree
```

Verdict: `FORMALIZE-TIER GREEN`; both audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

Current blocker: normalize `card_tupleCollisionSet_le` by `N^(2k)` and prove the real analytic
tail

```text
Σ_{P₀ < p ≤ N+K} (1/p + 1/N)^2 ≤ 3/P₀ + 4/N
```

under the eventual size hypotheses needed by the schedule.  This is now purely the
cast/division/harmonic-tail layer; the finite event and every fiber count are closed.

Next highest-value attack: prove a real-valued `collisionDensity_le` from
`card_tupleCollisionSet_le`, then split the square and bound the three elementary sums
(`Σ p⁻²`, `Σ p⁻¹/N`, and the interval cardinality over `N²`).  Feed that estimate and
the exact complement theorem into a tuple-average lemma combining
`global_bernMod_product_le_divisorVarianceMass_of_collisionFree` with the unit bound on the
collision set.

## Lap checkpoint (2026-10-12, normalized moment bound and density bridge)

Concrete advance in `CoefmassErdosBorweinEndpoint.lean` (commit `e28109fb`):

- Closed the elementary analytic tail.  `sum_inv_sq_Ioc_le_cutoff` proves the telescoping
  reciprocal-square estimate, and `sum_divisor_collision_density_le` proves
  `Σ_{P<p≤N+K}(1/p+1/N)² ≤ 3/P+4/N` under `P,N ≥ 1` and `K ≤ N`.
- Normalized the exact finite collision count.  `cast_collision_fiber_bound_le` handles the
  Nat/real cast and the `N^(2k-2)/N^(2k)` cancellation; `collisionDensity_le_four` gives the
  paper's bound
  `#collision/N^(2k) ≤ 4k²K(3/P+4/N)`.
- Assembled the deterministic contraction across the collision split.
  `tupleBernMod_sum_le_collision_add_pow` bounds the full tuple sum by the collision cardinality
  plus the `2k`-th power of the one-coordinate exponential divisor-mass sum.  The factorization is
  exact via `Fintype.prod_sum`.
- Connected this to the random Weyl moment.  The capstone
  `ebMoment_le_divisorMassAvg_pow_add_collision` proves precisely
  `E|A_N|^(2k) ≤ φ_N^(2k) + 4k²K(3/P+4/N)` with the phase hypotheses exposed.
- Closed the qualitative density input, including the indexing mismatch.  The map
  `x : Fin N ↦ x+1 ∈ Icc 1 N` is implemented by an exact finite bijection in
  `divisorMassExpAvg_le_density_add`; `tendsto_divisorMassExpAvg` now proves `φ_N → 0` directly
  from the frozen `hdiv` hypothesis.  Thus all finite counting, normalization, tuple assembly, and
  use of `hdiv` are complete.

Verification:

```text
lake env lean src/NormalNumbers/CoefmassErdosBorweinEndpoint.lean
```

Exit 0; the only proof debt in the target remains the frozen headline.

```text
~/personal/bin/lean-green ~/src/nn-eb-endpoint \
  --target NormalNumbers.CoefmassErdosBorweinEndpoint \
  --import NormalNumbers.CoefmassErdosBorweinEndpoint \
  --axioms NormalNumbers.ErdosBorweinEndpoint.collisionDensity_le_four \
  --axioms NormalNumbers.ErdosBorweinEndpoint.ebMoment_le_divisorMassAvg_pow_add_collision \
  --axioms NormalNumbers.ErdosBorweinEndpoint.tendsto_divisorMassExpAvg
```

Verdict: `FORMALIZE-TIER GREEN`.  Each audited declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`.

Adversarial review result: the three frozen declarations are byte-for-byte unchanged from staging
commit `f573b093`, and the route still reaches the headline.  No counterexample was found.  The
kickoff's "staged but uncommitted" skeleton had already been committed as `f573b093` before this
lap began; the worktree was clean at startup.

Current blocker: the remaining proof is the genuinely growing-moment probability layer.  Along
`N_j = CantorLiouville.sched (j+3)`, choose
`k_j = Nat.log 2 (j+3)+1` and, for fixed `b,h`, the deliberately coarse
`K_j = e+1+32|h|k_j`.  The latter makes the phase-size inequality elementary and remains
`O(log j)`.  What is still needed is (i) eventual `2K_j ≤ collisionCutoff N_j` and `K_j ≤ N_j`,
(ii) summability after Markov of
`ε^(-2k_j)·4k_j²K_j·(3/collisionCutoff N_j+4/N_j)`, and (iii) the variable-exponent
Borel--Cantelli/interpolation wrapper.

Next highest-value attack: prove one schedule lemma saying that for every fixed real polynomial
power `q`, `collisionCutoff (CantorLiouville.sched (j+3))` eventually dominates `(j+3)^q`.
Together with the standard bounds for `Nat.log 2`, this simultaneously gives the cutoff side
conditions and collision-error summability.  Then adapt
`ae_tendsto_weylMean_of_moment_decay` to a sequence of exponents `k_j`; the existing
`CantorLiouville.sched_strictMono`, `sched_ratio`, and interpolation theorem can be reused verbatim.
