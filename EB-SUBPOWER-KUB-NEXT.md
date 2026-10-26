# Non-normality below the sub-power weight for every `c > 1`, given `KubiliusTV` 🎯

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` sorry-free.  The headline
`ebRandom_ae_not_normal_subpower_of_kubilius` must be axiom-clean.

**Do not change** `primesUpTo`, `kubiliusMass`, `KubiliusTV` or the headline: they are verbatim from
the KB packet.  `KubiliusTV` is a named HYPOTHESIS: never prove, weaken or axiomatize it.  Helpers go
above the headline or in a new `CoefmassErdosBorweinSubpowerKubAux.lean`.  You may delete `private`
in `CoefmassErdosBorweinSubpower*.lean`, and nothing else in existing files.  No `native_decide`, no
new `axiom`.  **NEVER git push:** `research/eb-random` is local only.

## The shape: one new lemma, then copy the c > 3 assembly

The PROVED c > 3 proof (`CoefmassErdosBorweinSubpower.lean`) has exactly one c > 3-specific input,
`exists_subpower_marginal_large_cards_le` (`hc : 3 < c`):

    ∃ L₀, 3 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ T J, Σ_{j<J} #{n ≤ T : ε·2^{j/2} < marginalDivisorMass δ (dyadicExpCutoff L) n} ≤ ζ·T

`subpower_capped_marginal_residual_small` and the headline are otherwise c-free.  So:
1. Prove **`exists_subpower_marginal_large_cards_le_of_kubilius`**: the same conclusion, from
   `hK : KubiliusTV` and `hc : 1 < c`.
2. Copy `subpower_capped_marginal_residual_small` and the headline proof, swapping in step 1.

## Proof of the new lemma (paper: draft section "Non-normal for c > 1 given KubiliusTV")

Write `ψ(u) = √(c u log u)`, `u_ℓ = ℓ ln 2`, `y_ℓ = e^{2^ℓ}`, and `L_T = log log T`.
1. **Walk bound.**  Divisors in dyadic block `ℓ` divide `smoothPart y_{ℓ+1} n` (reuse the c > 3 block
   decomposition, `weightedDivisorBlockMass`).  `τ(smoothPart y n) ≤ 2^{ω(n; ≤ y)}·τ(b(n))`, with `b`
   the squarefull part, or any prime-power excess factor with `E_T log² ≤ K` uniformly in `T`.
2. **Trivial range.**  For `T ≤ dyadicExpCutoff L` every count is `0`, because there is no divisor
   `> M`.  So assume `T > M`, which forces `L_T ≥ L·ln 2 − O(1)` to be large.
3. **Top cut.**  Let `v = ⌈log L_T⌉` and `y₀ = ⌊T^{1/v}⌋`.  Then `n ≤ T` has `< v` prime factors `> y₀`.
   Blocks with `y_{ℓ+1} > y₀` contribute `≤ K·2^{(top sub-y₀ level) + v}`.
4. **Truncate thresholds.**  Split at `j ≤ 4L_T`.  For larger `j`, use `μ ≤ C·τ(n)` and
   `Σ_{n≤T} τ(n) ≤ T(log T + 1)`: the tail is `≤ T·e^{L_T}·L_T·2^{−2L_T}·(const/ε)`, which is small.
5. **Transfer.**  Each remaining count is `#{n ≤ T : n.primeFactors.filter (· ≤ y₀) ∈ A_j}`, after
   splitting off the prime-power factor by Cauchy–Schwarz (step 1).  Apply `hK` at `(T, y₀)`.  The
   error is `4L_T·C·(v^{−v} + T^{−1/2}) → 0` (`u = log T/log y₀ ≥ v` and `u^{−u}` is decreasing).
6. **Model bound** (the analytic heart; state it as a standalone lemma about `kubiliusMass`).
   - Under the model, `ω(≤ y) = S_y + Σ_{p≤y} 1/p`, with `S` a centered sum of independent
     Bernoulli(`1/p`) − `1/p`.  Upper Mertens (`Erdos67.PrimeEstimates.mertensBound`) gives
     `Σ 1/p ≤ log log y + B`.
   - Need: `kubiliusMass y₀ {S : ∃ ℓ ≥ L, S-walk at y_{ℓ+1} > ψ̃(u_ℓ) + x}` integrated over the
     thresholds is `→ 0` as `L → ∞`, uniformly in `y₀`.  Here `ψ̃ = ψ − 2 log₂ ℓ − O(1)`.
   - **Doob's exponential maximal inequality** on geometric blocks `u ∈ [r^k, r^{k+1})`, with
     `r := (1 + c)/2 ∈ (1, c)`:
     `P(max_{p ≤ P} S_p ≥ h + x) ≤ e^{−θ(h+x)}·Π_{p≤P}(1 + (e^θ−1)/p)e^{−θ/p} ≤ e^{(e^θ−1−θ)(log log P + B) − θ(h+x)}`.
     Take `θ = h/U`, `U = r^{k+1} + O(1)`, `h = ψ̃(r^k)`.  Integrating over `x` gives
     `≤ (U/h)·exp(−h²/(2U) + o(1)) ≲ r^{k(1/2 − c/(2r))}/√k`, which is summable since `r < c`.
     Use `e^θ − 1 − θ ≤ θ²/2 + θ³` for `0 ≤ θ ≤ 1`.
   - Doob: Mathlib `MeasureTheory.maximal_ineq` (submartingale `exp(θ S)`).  Alternatively a direct
     finite first-passage argument over the finitely many primes `≤ y₀`.  The model is finite, so
     either works.  **Reference:** `~/src/nn-eb-endpoint/src/NormalNumbers/CoefmassErdosBorweinEndpointKub.lean`
     (read-only sibling branch).  It handles `kubiliusMass` as an independent Bernoulli subset mass
     (`kubiliusMass_eq_bernoulliSubsetMass`, `kubiliusMass_blockCenteredSum_*`); adapt, don't import.
   - The top-cut shift `v` costs a factor `e^{θ v}`, with `θ v = O(log L_T·√(log L_T/L_T)) → 0`.

Why the ratio matters: unit blocks (the c > 3 proof) lose a factor `u/ψ` per scale, ratio-2 blocks give
`c > 2`, and ratio `r < c` gives `c > 1`.  Do not use ratio 2.

## Order of attack
6 (the model maximal bound, pure probability; the main risk) → 1 → 3 → 4 → 5 → 2 → the copied assembly.
Commit each green lemma.  If step 6 fights, JUDGE-FLAG the exact inequality in the handoff rather
than weaken anything.

## Lap checkpoint — 2026-10-26

The finite-probability core of step 6 is now kernel-checked.

- Commit `c0162cf3` adds `CoefmassErdosBorweinSubpowerKubAux.lean`.  It realizes the independent
  Bernoulli model as a weighted powerset, proves exact total mass and recursive first-passage mass,
  and proves the finite Doob/Ville exponential maximal inequality directly (without a measure-theory
  detour).
- Commit `c13cf6c1` identifies the recursive event with an explicit centered prefix crossing,
  specializes the maximal inequality to `kubiliusMass`, inserts the proved Mertens upper bound, and
  proves the cubic estimate
  `exp θ - 1 - θ ≤ θ² / 2 + θ³` for `0 ≤ θ ≤ 1`.
- The current checkpoint formalizes the route-decisive geometric choice
  `r = kubiliusBlockRatio c = (1+c)/2`: Lean proves `1 < r < c`,
  `1/2 - c/(2r) < 0`, and summability of the resulting `r`-power majorant.  Thus the exact analytic
  exponent needed to pass from `c > 3` to every `c > 1` is no longer heuristic.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged from `e61852e6`; `KubiliusTV` remains only a hypothesis.  There is no new `axiom`, no
`native_decide`, and the only `sorry` in the scoped target remains the headline proof.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  expected headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.summable_kubiliusGeometricDecay --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.kubiliusMass_exists_centeredPrefixSum_ge_le_exp_cubic` —
  `FORMALIZE-TIER GREEN`; both declarations report only `Classical.choice`, `Quot.sound`, and
  `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job build, `FORMALIZE-TIER GREEN`.

The remaining crux is to package these ingredients into the uniform integrated model bound from
step 6.  The next highest-value attack is a standalone `kubiliusMass` theorem on geometric log-log
blocks: instantiate the cubic maximal inequality with `θ = h/U`, prove `θ ≤ 1`, include the lowered
barrier `h = √(c u log u) - 2 log₂ u - O(1)` and the top-cut shift, integrate the auxiliary threshold,
then dominate the block terms by the summable majorant proved here.  Only after that model theorem
is green should work move to divisor/squarefull comparison (step 1) and the `KubiliusTV` transfer.

## Lap checkpoint — 2026-10-26, optimized one-block bound

The optimization and auxiliary-threshold integration portions of the uniform model bound are now
kernel-checked.

- `kubiliusMass_exists_centeredPrefixSum_ge_add_le_exp_optimized` instantiates the cubic maximal
  inequality at `θ = h/U`, for any Mertens variance cap `U`, and gives the exact exponent
  `-h²/(2U) + h³/U² - hx/U`.
- `hasSum_kubiliusOptimizedTail` and `tsum_kubiliusOptimizedTail_le` sum the auxiliary integer
  thresholds exactly as a geometric series and bound their total cost by `2U/h` when `2h ≤ U`.
- `sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_optimized` packages those facts as a single
  finite-threshold `kubiliusMass` estimate, uniformly in the number of thresholds.
- `kubiliusOptimizedExponent_eq` specializes to the ideal barrier
  `h = u * blockSigma c u = √(cu log u)` and `U = r*u`.  The existing exact square/cubic identities
  reduce its exponent to `(-c/(2r) + c*blockSigma c u/r²) log u`.
- `eventually_kubiliusOptimizedExponent_le` uses `blockSigma c u → 0` to absorb the cubic
  correction by half the strict gap `r < c`, leaving `-(c+r)/(4r) log u`.  After the already-proved
  reciprocal-barrier cost `U/h ≪ √u`, this leaves the negative power `(r-c)/(4r)`, exactly half
  of `kubiliusGeometricDecayExponent`; hence the geometric-block sum remains summable for every
  `r < c`.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
still unchanged from `e61852e6`.  `KubiliusTV` remains only a hypothesis; no `axiom` or
`native_decide` was added.  The scoped target still has its single headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_optimized
  --axioms NormalNumbers.ErdosBorweinSubpowerKub.eventually_kubiliusOptimizedExponent_le --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.summable_kubiliusGeometricDecay` — `FORMALIZE-TIER GREEN`;
  all three declarations report only `Classical.choice`, `Quot.sound`, and `propext`.
- `~/personal/bin/lean-green .` — full repository build, `FORMALIZE-TIER GREEN`.

The remaining step-6 blocker is no longer the maximal inequality, its optimization, the threshold
sum, or the leading geometric exponent.  It is the deterministic event comparison for the actual
lowered barrier: incorporate `2 log₂ u + O(1)` and the top-cut shift `v = ⌈log L_T⌉` into `h`, prove
these losses are `o(√(u log u))` uniformly over a geometric block, and map a selected-prime set's
block walk to the prefix event in
`sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_optimized`.  The next lap should formalize that
lowered-barrier comparison and its eventual parameter conditions (`0 < h`, `2h ≤ U`), then combine
it with `eventually_kubiliusOptimizedExponent_le`.  Only then move to the squarefull/divisor
comparison and `KubiliusTV` transfer.

## Lap checkpoint — 2026-10-26, lowered-barrier comparison

The deterministic lowered-barrier layer of step 6 is now kernel-checked.

- `kubiliusMass_mono` proves monotonicity of the packet's finite Bernoulli mass directly, with no
  measure-theory detour.
- `sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_of_le` separates the deterministic event
  comparison from probability: any larger actual threshold inherits the already-proved optimized
  finite-threshold sum bound from a smaller ideal threshold.
- `kubiliusLoweredBarrier c A B u = u * blockSigma c u - A log u - B` packages exactly the
  logarithmic and bounded losses required by the paper route.
- `blockSigma_eq_sqrt_ratio_mul` identifies the fixed gap between coefficient-`c₀` and
  coefficient-`c` ideal barriers.
- `eventually_idealBarrier_le_kubiliusLoweredBarrier` proves, for every `0 < c₀ < c` and fixed
  `A,B` with `0 ≤ B`, that the lowered `c` barrier eventually dominates the ideal `c₀` barrier.
  The proof uses the exact identity `u * blockSigma c u ^ 2 = c log u`; thus a logarithmic loss
  divided by the ideal barrier is a constant multiple of `blockSigma c u → 0`.
- `eventually_kubiliusLoweredBarrier_conditions` adds the operational side conditions: for
  nonnegative losses the lowered barrier is eventually positive, at most the ideal `c` barrier,
  and satisfies `2h ≤ r*u` for every fixed `r > 0`.  This is precisely the hypothesis required by
  the optimized threshold sum with variance cap `U = r*u`.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
still unchanged from `e61852e6`.  `KubiliusTV` remains only a hypothesis; no `axiom` or
`native_decide` was added.  The scoped target still has its single headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.kubiliusMass_mono --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.sum_kubiliusMass_exists_centeredPrefixSum_ge_add_le_of_le
  --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.eventually_idealBarrier_le_kubiliusLoweredBarrier --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.eventually_kubiliusLoweredBarrier_conditions` —
  `FORMALIZE-TIER GREEN`; all four declarations report only `Classical.choice`, `Quot.sound`, and
  `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The next highest-value attack is the geometric-block assembly of the model theorem.  Choose an
inner coefficient `c₀` strictly between `r = (1+c)/2` and `c`, use the new event comparison to
replace the actual lowered threshold by `u * blockSigma c₀ u`, combine
`eventually_kubiliusOptimizedExponent_le` with the `U/h ≪ √u` prefactor, and sum the resulting
negative-power majorant over geometric blocks.  After that, identify a selected-prime set's block
walk with the ordered-prefix event and only then move to the squarefull/divisor comparison and
`KubiliusTV` transfer.

## Review-lap checkpoint — 2026-10-26, integrated geometric-block majorant

Fresh reconstruction from the frozen packet statement, the proved `c > 3` theorem, source, and
history confirms the route: the old headline assembly is c-free after
`exists_subpower_marginal_large_cards_le`, so this campaign still needs exactly its Kubilius-based
replacement and then can reuse `subpower_capped_marginal_residual_small` and the final marginal
criterion.  A diff against planting commit `e61852e6` reconfirmed that `primesUpTo`,
`kubiliusMass`, `KubiliusTV`, and the headline statement are byte-unchanged.

The geometric-block assembly requested by the previous checkpoint is now kernel-checked.

- `kubiliusInnerCoefficient c` chooses `c₀ = (r+c)/2`, where
  `r = kubiliusBlockRatio c = (1+c)/2`; Lean proves `r < c₀ < c`.
- `kubiliusIntegratedDecayExponent c = (r-c₀)/(4r)` records the exponent remaining after the
  optimized maximal tail and the reciprocal-barrier cost.  It is strictly negative for every
  `c > 1`.
- `eventually_kubiliusLoweredCrossingMass_le` is the uniform one-block model theorem.  For every
  sufficiently large log-log coordinate `u`, every terminal prime cutoff `y` whose Mertens
  variance is at most `r*u`, and every finite number of auxiliary thresholds, the total
  `kubiliusMass` of lowered-barrier prefix crossings is at most
  `kubiliusIntegratedMajorantConstant c * u ^ kubiliusIntegratedDecayExponent c`.
  The proof composes the lowered-barrier event comparison, the optimized cubic maximal bound,
  the exponent gap `r < c₀`, and `blockSigma_inv_le_sqrt_div_sqrt`.
- `kubiliusIntegratedMajorant_geometric` specializes `u = r^k`, and
  `summable_kubiliusIntegratedMajorant` proves the resulting full majorant summable.  Thus the
  analytic probability calculation on geometric blocks no longer has an open exponent or
  summation step.

The scoped target still has its single frozen headline `sorry`.  `KubiliusTV` remains only a
hypothesis; no `axiom` declaration or `native_decide` was added.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.eventually_kubiliusLoweredCrossingMass_le --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.summable_kubiliusIntegratedMajorant --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.kubiliusIntegratedMajorant_geometric` —
  `FORMALIZE-TIER GREEN`; all three declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The remaining step-6 blocker is now purely the deterministic event interface, not the maximal
estimate or geometric summation.  The next highest-value attack is to define the actual selected-
prime walk on a geometric log-log block and prove that crossing its lowered barrier implies the
ordered-prefix event in `kubiliusLoweredCrossingMass` (with the terminal cutoff variance cap).
Then sum those block events using `summable_kubiliusIntegratedMajorant`.  After this model theorem
is packaged, move to the squarefull/large-prime comparison and the `KubiliusTV` transfer; only then
copy the proved `c > 3` capped-residual and headline assembly.
