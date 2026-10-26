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

## Lap checkpoint — 2026-10-26, arithmetic prime cutoffs enter the Doob walk

The deterministic selected-prime event interface requested by the previous checkpoint is now
kernel-checked.

- `centeredBernoulliFinsetSum` gives the centered selected-coordinate sum on an unordered finite
  cutoff, and `centeredBernoulliPrefixSum_eq_finsetSum_take` proves that it is exactly the ordered
  Doob walk on a duplicate-free list prefix.
- `primesUpTo_sort_take_card` proves the route-decisive ordering fact: whenever `a ≤ y`, the primes
  up to `a` are literally the first `#primesUpTo a` coordinates of the increasing primes-up-to-`y`
  list.  Thus no interpolation or approximate event comparison is needed at arithmetic cutoffs.
- `kubiliusSelectedPrimeWalk_at_cutoff` identifies the actual selected-prime walk at that time with
  the centered sum over `primesUpTo a`.
- `primeCutoffCrossing_subset_centeredPrefixCrossing` packages the deterministic event inclusion,
  and `kubiliusMass_primeCutoffCrossing_le_centeredPrefixCrossing` transfers it through monotonicity
  of the packet's `kubiliusMass`.
- `kubiliusLoweredCrossingMass_eq_selectedPrimeWalk` rewrites the already-proved one-block model
  quantity directly as selected-prime-walk crossing masses.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged.  `KubiliusTV` remains only a hypothesis; no `axiom` declaration or `native_decide` was
added.  The scoped target still has its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKubAux.lean` — succeeds.
- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.centeredBernoulliPrefixSum_eq_finsetSum_take --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.primesUpTo_sort_take_card --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.primeCutoffCrossing_subset_centeredPrefixCrossing --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.kubiliusMass_primeCutoffCrossing_le_centeredPrefixCrossing
  --axioms NormalNumbers.ErdosBorweinSubpowerKub.kubiliusLoweredCrossingMass_eq_selectedPrimeWalk`
  — `FORMALIZE-TIER GREEN`; all five declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The remaining step-6 work is the geometric-block union/tail packaging, not the cutoff-to-prefix
interface: instantiate arithmetic cutoffs in each log-log block, use the new mass inclusion and
`eventually_kubiliusLoweredCrossingMass_le`, then sum the resulting block majorants with
`summable_kubiliusIntegratedMajorant`.  Once that uniform model theorem is packaged, proceed to the
squarefull/large-prime divisor comparison and the `KubiliusTV` transfer, then reuse the proved
`c > 3` capped-residual and headline assembly.

## Lap checkpoint — 2026-10-26, geometric prime-cutoff tail packaged

The remaining geometric-block union/tail layer of step 6 is now kernel-checked, including the
actual arithmetic prime cutoffs rather than only the ordered-prefix event.

- `kubiliusPrimeCutoffLoweredCrossingMass` is the model mass of a selected-prime walk crossing at
  some arithmetic cutoff `a ≤ y`, summed over the auxiliary integer thresholds.
- `kubiliusPrimeCutoffLoweredCrossingMass_le` uses the proved cutoff-to-prefix inclusion termwise
  to dominate this quantity by `kubiliusLoweredCrossingMass`.
- `exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt` composes the eventual uniform
  one-block estimate with `summable_kubiliusIntegratedMajorant`.  Given any `ζ > 0`, all finite
  families of sufficiently late geometric blocks have total crossing mass `< ζ`, uniformly in
  each block's terminal cutoff and number of auxiliary thresholds, provided the terminal Mertens
  variance obeys the required `r * u` cap.  Thus step 6's maximal inequality, arithmetic event
  interface, geometric union, and tail limit are all packaged.

The diff from planting commit `e61852e6` is insertion-only at the helper layer: `primesUpTo`,
`kubiliusMass`, `KubiliusTV`, and the headline statement remain unchanged.  `KubiliusTV` remains
only a hypothesis; no `axiom` declaration or `native_decide` was added.  The scoped target still
has its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.kubiliusPrimeCutoffLoweredCrossingMass_le --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt`
  — `FORMALIZE-TIER GREEN`; both declarations report exactly `Classical.choice`, `Quot.sound`, and
  `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The model-probability step 6 is now complete at the geometric arithmetic-cutoff interface.  The
remaining crux is the deterministic/arithmetic comparison needed for
`exists_subpower_marginal_large_cards_le_of_kubilius`: bound the divisor block mass by the selected
small-prime walk while controlling prime-power excess and the fewer than `v` primes above the top
cutoff, truncate the auxiliary thresholds, and then apply `KubiliusTV` (including its summed error).
The next highest-value attack is the squarefull/prime-power excess moment bound and the resulting
event inclusion from a large `weightedDivisorBlockMass` to a lowered selected-prime-walk crossing.
Once that comparison and transfer are green, copy the proved `c > 3` capped-residual and headline
assembly verbatim except for swapping in the new large-cards lemma.

## Reflection-lap checkpoint — 2026-10-26, square-divisor arithmetic event bridge

The prime-power excess and its exact interface with the selected-prime walk are now kernel-checked.
The reflection used a simpler excess factor than the paper's proposed squarefull/Cauchy--Schwarz
route: if `e = v_p(n)`, then `e + 1 ≤ 2 (⌊e/2⌋ + 1)`.  Consequently the smooth divisor count is at
most `2^ω` times the number of square divisors.  The latter has a uniformly bounded first moment,
which is enough once its cutoff is allowed to depend on the geometric block and shift threshold.

- `squareDivisorRoot` and `squareDivisorCount` encode the choices `0 ≤ a_p ≤ ⌊v_p(n)/2⌋`.
  Lean proves `q^2 ∣ n ↔ q ∣ squareDivisorRoot n` and the exact Euler product for the count.
- `smoothDivisorCount_le_two_pow_mul_squareDivisorCount` proves
  `τ(n_y) ≤ 2^{ω(n;≤y)} Q(n)` without hiding any prime-power loss.
- `sum_squareDivisorCount_eq_sum_div` double-counts square divisors exactly, and
  `sum_squareDivisorCount_le` bounds their first moment by
  `T * ∑_{q : ℕ} 1/q²`.  `squareDivisorCount_large_card_le` is the resulting uniform Markov bound.
- `subpowerWeightedDivisorBlockMass_le_two_pow_mul_squareDivisorCount` inserts this factorization
  into the existing weighted divisor-block estimate.
- `log_subpowerWeight_dyadicExpCutoff_eq_blockSigma` computes the logarithm of the frozen weight
  exactly at a dyadic-exponential cutoff.  There is no asymptotic replacement: the main penalty is
  precisely `log 2 * u * blockSigma c u`.
- `centeredBernoulliFinsetSum_primeFactors_filter_primesUpTo` identifies the arithmetic truncated
  prime-factor count with the selected Kubilius coordinate sum.
- `subpowerWeightedDivisorBlockMass_large_imp_square_or_centered_sum_gt` is the resulting
  transfer-ready event inclusion.  A large divisor block forces either `U < Q(n)` or a centered
  prime-walk crossing at the exact cutoff `dyadicExpCutoff (ℓ+1)`, above
  `u*blockSigma c u + (log R-log U)/log 2 - log 2 - mertensBound`.
- `kubiliusTV_sum_card_div_le` packages the packet hypothesis termwise over a finite threshold
  family and records the accumulated TV error explicitly.

The diff from planting commit `e61852e6` remains insertion-only around the frozen packet
declarations: `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are unchanged.
`KubiliusTV` remains only a named hypothesis.  No `axiom`, `opaque`, or `native_decide` was added;
the scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.sum_squareDivisorCount_le --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.kubiliusTV_sum_card_div_le --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.subpowerWeightedDivisorBlockMass_large_imp_square_or_centered_sum_gt`
  — `FORMALIZE-TIER GREEN`; all three declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The next crux is the finite bookkeeping that turns this event inclusion into
`exists_subpower_marginal_large_cards_le_of_kubilius`.  On each geometric log-log block, choose a
cutoff `U = U(k,j)` large enough that the first-moment square-divisor exceptions remain summable
over both arithmetic levels and threshold shifts, while `log U` costs only `A log u` plus a fixed
fraction of the shift.  Then bound the block-allocation term in `log R`, group the resulting walk
events under `kubiliusPrimeCutoffLoweredCrossingMass`, control the finite TV error with
`kubiliusTV_sum_card_div_le`, and add the top-cut and large-threshold tails.  Once the large-cards
lemma is green, reuse `subpower_capped_marginal_residual_small` and the proved `c > 3` headline
assembly with only that input replaced.

## Lap checkpoint — 2026-10-26, shift allocation and square-exception sum

The first finite-bookkeeping layer after the arithmetic event bridge is now kernel-checked.  The
square-divisor cutoff can be chosen to grow polynomially in the log-log coordinate and
geometrically in the shift without destroying the lowered-barrier model estimate.

- `log_blockAllocation_ge` proves the explicit loss bound
  `log(blockAllocation ℓ) ≥ -2 log(blockLogLog ℓ) - 2 log 4` for `ℓ ≥ 6`.
- `subpowerKubiliusSquareCutoff D u j = u^D * 2^(j/4)` allocates the square-divisor exceptions.
  `subpowerKubiliusLossA` and `subpowerKubiliusLossB` package the resulting fixed logarithmic and
  constant losses.
- `subpowerBlockThreshold_after_squareCutoff_ge_lowered` proves that this choice retains
  `⌊j/4⌋` of the original shift above the lowered Kubilius barrier.  Thus the prime-power excess
  consumes only half of the available `j/2` logarithmic threshold.
- `subpowerWeightedDivisorBlockMass_large_imp_square_or_kubiliusLowered` composes that inequality
  with the previous divisor-block bridge: a large block now forces either the allocated
  square-divisor exception or an actual selected-prime crossing above the lowered barrier plus
  `⌊j/4⌋`.
- `sum_squareDivisorCount_large_card_subpowerCutoff_le` sums the square-divisor exception over an
  arbitrary finite shift family, uniformly in its length, at cost
  `T * squareDivisorMomentConstant * u^{-D} * subpowerSquareShiftConstant`.  This removes the
  prime-power excess from the remaining model/TV bookkeeping once `D > 1` is fixed.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged.  `KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide`
was added.  The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.subpowerWeightedDivisorBlockMass_large_imp_square_or_kubiliusLowered
  --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.sum_squareDivisorCount_large_card_subpowerCutoff_le
  --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.subpowerBlockThreshold_after_squareCutoff_ge_lowered` —
  `FORMALIZE-TIER GREEN`; all three declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The next highest-value attack is the remaining level-grouping/cardinality interface.  For levels
whose `blockLogLog` coordinates lie in one geometric interval `[r^k,r^(k+1))`, use the new
pointwise disjunction to bound the sum of large-block cards by (i) the now-summable square term and
(ii) at most four copies of each integer-threshold prime-cutoff crossing event.  Compare the
level's ideal barrier with the block anchor, apply `kubiliusTV_sum_card_div_le`, and feed the model
terms to `exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt`.  The later top-cut,
large-threshold truncation, and trivial `T ≤ dyadicExpCutoff L` cases remain after that interface.

## Lap checkpoint — 2026-10-26, fixed-level TV transfer and anchored barriers

The fixed-level arithmetic/TV layer of the remaining grouping interface is now kernel-checked.

- `sum_comp_nat_div_four_le` proves the exact shift bookkeeping: after the square-divisor cutoff
  consumes three quarters of the original shift, grouping by `⌊j/4⌋` costs at most four copies of
  each integer threshold.
- `idealBarrier_mono`, `subpowerKubiliusModelCoefficient`, and
  `eventually_kubiliusLevelBarrier_ge_anchor_blockLogLog` compare every sufficiently late
  arithmetic level to a geometric-block anchor.  The model coefficient is `(1+c)/2`, strictly
  between `1` and `c`; the fixed logarithmic losses are absorbed by that coefficient gap.
- `kubiliusArithmeticEventFinset` and `kubiliusArithmeticEventCard` pin the finite arithmetic event
  used by `KubiliusTV`, avoiding any decidability-instance ambiguity at the cardinality boundary.
- `exists_subpowerBlock_large_cards_div_le_square_add_kubilius` composes the square-or-walk event
  inclusion, the summed square-divisor estimate, the four-to-one shift grouping, and
  `KubiliusTV`.  For one arithmetic level it bounds the normalized sum of large weighted-block
  cards by the square exception, four times the anchored prime-cutoff crossing mass, and the
  explicit accumulated TV error.

This also sharpens the remaining interface requirement: levels in one geometric block must be
unioned before taking cardinality.  Summing the new fixed-level estimate over levels would multiply
the maximal crossing mass by the number of levels and lose the Doob gain.  The next theorem should
therefore take a finite level set, bound the cardinality of `∃ ℓ` large-block events by (i) the sum
of square exceptions and (ii) one prime-cutoff crossing event, and only then sum over shifts and
apply TV.  Connect that union theorem directly to the marginal-divisor large-card cover instead of
using the old sum-of-level-card bound.  Once grouped by anchors
`(kubiliusBlockRatio (subpowerKubiliusModelCoefficient c))^k`, its model terms feed directly into
`exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt`.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged.  `KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide`
was added.  The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.eventually_kubiliusLevelBarrier_ge_anchor_blockLogLog
  --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_subpowerBlock_large_cards_div_le_square_add_kubilius
  --axioms NormalNumbers.ErdosBorweinSubpowerKub.sum_comp_nat_div_four_le` —
  `FORMALIZE-TIER GREEN`; all three declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

## Review-lap checkpoint — 2026-10-26, union-before-cardinality transfer

Fresh reconstruction from the frozen packet statement, the proved `c > 3` assembly, current
source, and recent history confirms the route but also confirms the last checkpoint's warning:
the fixed-level transfer cannot simply be summed over arithmetic levels.  Doing so would multiply
the Doob crossing mass by the number of levels in a geometric block and lose the maximal-inequality
gain.  The level union must be formed before cardinality and before applying `KubiliusTV`.

That load-bearing correction is now kernel-checked.

- `exists_subpowerBlock_union_large_cards_div_le_square_add_kubilius` takes an arbitrary finite
  set of arithmetic levels sharing one geometric anchor and terminal prime cutoff.  It unions all
  large weighted-block events before taking cardinality.
- Only the square-divisor exceptions are then summed over levels.  Every selected-prime walk event
  is absorbed into one anchored arithmetic event, so the theorem charges exactly one
  `kubiliusPrimeCutoffLoweredCrossingMass` and one accumulated `KubiliusTV` error for the whole
  level set.
- The theorem retains the existing four-to-one threshold grouping and all explicit barrier,
  cutoff, and total-variation side conditions.  No disjointness of the level events is assumed.

The diff from the preceding checkpoint is insertion-only above the frozen headline.  The packet
declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement remain
unchanged.  `KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide`
was added.  The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_subpowerBlock_union_large_cards_div_le_square_add_kubilius`
  — `FORMALIZE-TIER GREEN`; the new theorem reports exactly `Classical.choice`, `Quot.sound`, and
  `propext`.
- `~/personal/bin/lean-green .` — full repository build, `FORMALIZE-TIER GREEN`.

The next highest-value attack is to connect this finite-level union theorem directly to the
marginal-divisor cover.  Partition the active levels into geometric `blockLogLog` intervals with
ratio `kubiliusBlockRatio (subpowerKubiliusModelCoefficient c)`, take the terminal cutoff once per
interval, and apply the union theorem before summing over geometric blocks.  Then discharge the
remaining two uniformity tails: levels above the top cutoff and shifts beyond the TV truncation.
This produces `exists_subpower_marginal_large_cards_le_of_kubilius`; after that, reuse the proved
`subpower_capped_marginal_residual_small` and `c > 3` headline assembly with only that input
replaced.

## Lap checkpoint — 2026-10-26, grouped marginal cover reaches `KubiliusTV`

The marginal-divisor decomposition is now connected to the union-before-cardinality transfer
without reintroducing a factor equal to the number of arithmetic levels.

- `sum_marginalDivisorMass_large_cards_le_grouped_block_unions` replaces the old
  sum-of-level-cardinalities cover by an arbitrary finite family of level groups.  Each group's
  large-block events are unioned before cardinality.  Levels deliberately left for the top-cut or
  another deterministic estimate live in one explicit `exceptional` finset, so the lemma does not
  hide or assume away the remaining tail.
- `exists_sum_marginalDivisorMass_large_cards_div_le_grouped_kubilius` composes that grouped cover
  with `exists_subpowerBlock_union_large_cards_div_le_square_add_kubilius`.  Its conclusion charges
  one square-divisor sum, one prime-walk crossing mass, and one accumulated `KubiliusTV` error per
  group; the exceptional contribution stays visible on the right-hand side.
- This pins the remaining global bookkeeping as side conditions rather than prose: construct the
  geometric groups and their anchors/cutoffs, bound the displayed exceptional contribution, and
  make the displayed square, model, and TV sums uniformly small.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged.  `KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide`
was added.  The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.sum_marginalDivisorMass_large_cards_le_grouped_block_unions
  --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_sum_marginalDivisorMass_large_cards_div_le_grouped_kubilius`
  — `FORMALIZE-TIER GREEN`; both declarations report exactly `Classical.choice`, `Quot.sound`, and
  `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The next highest-value attack is the explicit geometric partition.  Use ratio
`kubiliusBlockRatio (subpowerKubiliusModelCoefficient c)`, put levels above the usable prime cutoff
in the theorem's `exceptional` finset, and prove that contribution small by the top-cut plus
large-threshold estimates.  For the ordinary groups, choose the left `blockLogLog` endpoint as
`u₀` and the largest arithmetic prime cutoff as `y`; then feed the model terms to
`exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt`, sum the square terms with a fixed
`D > 1`, and show the finitely accumulated TV errors tend to zero uniformly.  That is the last
substantial input before `exists_subpower_marginal_large_cards_le_of_kubilius` and the copied
`c > 3` final assembly.

## Lap checkpoint — 2026-10-26, slack-aware geometric schedule

The model tail is now separated from the arithmetic grouping ratio, and the fixed endpoint loss
has a kernel-checked absorption lemma.  This corrects one detail in the preceding plan: grouping at
the model variance ratio itself leaves no strict room for the additive
`log 2 + Erdos67.PrimeEstimates.mertensBound` incurred when a level uses the next dyadic endpoint.

- `summable_kubiliusIntegratedDecay_of_ratio` and
  `summable_kubiliusIntegratedMajorant_of_ratio` prove that the existing negative-power one-block
  majorant is summable along every schedule `q^k` with `q > 1`, not only along the hard-coded model
  variance ratio.
- `exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt_of_ratio` packages the resulting
  uniform model tail.  Its anchor is `q^k`, while its variance cap correctly remains
  `kubiliusBlockRatio c * q^k`.
- `subpowerKubiliusGroupingRatio c` chooses a concrete arithmetic grouping ratio strictly between
  `1` and `kubiliusBlockRatio (subpowerKubiliusModelCoefficient c)`.
- `eventually_grouping_pow_succ_add_le_varianceRatio_mul_pow` proves that the strict ratio gap
  eventually absorbs any fixed additive loss.  Combining it with mathlib's
  `exists_nat_pow_near` gives
  `eventually_exists_grouping_pow_le_and_add_le_varianceRatio_mul_pow`.
- `eventually_exists_subpowerKubiliusGroupingIndex` specializes this to the actual arithmetic
  levels: every sufficiently late `ℓ` has an anchor `q^k ≤ blockLogLog ℓ` for which
  `blockLogLog (ℓ+1) + mertensBound` lies under the model variance cap.  Thus the barrier lower
  bound and terminal-cutoff variance upper bound can hold simultaneously in each group.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged.  `KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide`
was added.  The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.summable_kubiliusIntegratedDecay_of_ratio --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt_of_ratio
  --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.eventually_grouping_pow_succ_add_le_varianceRatio_mul_pow
  --axioms NormalNumbers.ErdosBorweinSubpowerKub.eventually_exists_subpowerKubiliusGroupingIndex`
  — `FORMALIZE-TIER GREEN`; all four declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The next highest-value attack is now the finite partition itself.  For sufficiently late levels,
group `ℓ` by the index supplied by `eventually_exists_subpowerKubiliusGroupingIndex`; within each
nonempty group take the largest `ℓ` and terminal cutoff `dyadicExpCutoff (ℓ+1)`.  The new theorem
supplies both the anchor/barrier side and the Mertens variance cap, while monotonicity supplies all
smaller cutoffs.  Put levels whose cutoff exceeds the averaging range in `exceptional`, prove their
top-cut contribution directly, and then apply
`exists_sum_marginalDivisorMass_large_cards_div_le_grouped_kubilius`.  The remaining global terms
are the square tail, the arbitrary-ratio model tail proved here, and the finite accumulated TV
error; controlling those yields `exists_subpower_marginal_large_cards_le_of_kubilius`, after which
the proved `c > 3` capped-residual and headline assembly can be reused.

## Reflection-lap checkpoint — 2026-10-26, canonical finite partition wired through TV

The explicit finite partition requested by the preceding checkpoint is now kernel-checked and
composed with the grouped arithmetic transfer.  Reflection also sharpened the remaining top-cut
architecture: the Kubilius estimate should handle all levels below a common prime cutoff, while
the old one-level fractional-moment estimate handles only the thin exceptional top band.  This
does not require summing the old majorant over the full tail (the step that forced `c > 3`).

- `subpowerKubiliusGroupingIndex` makes a canonical choice of the slack-aware geometric index.
  `eventually_subpowerKubiliusGroupingIndex_spec` retains both the left-anchor and variance-cap
  inequalities, and `eventually_le_subpowerKubiliusGroupingIndex` proves that these chosen indices
  tend to infinity.  Thus late arithmetic levels really land beyond the tail index supplied by the
  summable model theorem; this was not encoded by the preceding existential statement alone.
- `subpowerKubiliusOrdinaryLevels` and `subpowerKubiliusExceptionalLevels` split the finite level
  interval at an arbitrary common prime cutoff `Y`.  `subpowerKubiliusLevelGroups` partitions the
  ordinary levels into full fibers of the canonical index.  Every produced fiber is nonempty,
  contains its supremum, and is characterized exactly by its key; the map from groups to keys is
  injective (`subpowerKubiliusLevelGroup_index_injOn`).
- `subpowerKubiliusGroupCutoff` takes the next dyadic endpoint of the largest level in a group, and
  `subpowerKubiliusGroupAnchor` records its common geometric anchor.
  `exists_subpowerKubiliusLevelGroups_data` proves, uniformly for all sufficiently late starting
  levels, the exact cover, barrier comparison, terminal-cutoff bound, Mertens variance cap, and an
  arbitrary lower bound on every group key.
- `subpowerKubiliusCanonicalGroupedBound` names the four terms still to estimate: the exceptional
  top band, square-divisor sum, model crossing sum, and accumulated TV error.
  `exists_sum_marginalDivisorMass_large_cards_div_le_canonical_kubilius` now applies
  `exists_sum_marginalDivisorMass_large_cards_div_le_grouped_kubilius` to the canonical partition
  and retains both the variance caps and late-key facts needed for the next summation step.

The cumulative diff from planting commit `e61852e6` is still insertion-only: `primesUpTo`,
`kubiliusMass`, `KubiliusTV`, and the headline statement remain byte-unchanged.  `KubiliusTV`
remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide` was added.  The scoped
target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning.
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.eventually_le_subpowerKubiliusGroupingIndex --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.subpowerKubiliusLevelGroup_index_injOn --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_subpowerKubiliusLevelGroups_data --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_sum_marginalDivisorMass_large_cards_div_le_canonical_kubilius`
  — `FORMALIZE-TIER GREEN`; all four declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

The next highest-value attack is to bound the four named terms in
`subpowerKubiliusCanonicalGroupedBound`.  Choose a common dyadic cutoff a logarithmic number of
levels below the largest active level.  Reindex the model terms injectively by the now-explicit
group keys and apply
`exists_kubiliusPrimeCutoffLoweredCrossingMass_geometric_sum_lt_of_ratio`; take fixed `D > 1` for
the square sum; use the resulting large value of `log T / log Y` for the accumulated TV error.
For the thin exceptional band, generalize the existing one-level Chernoff majorant only far enough
to show it tends to zero for every `c > 1`, then multiply by the logarithmic band width.  These four
estimates yield `exists_subpower_marginal_large_cards_le_of_kubilius`; the final capped-residual and
headline proofs should then be copied from the proved `c > 3` assembly with that sole input swapped.

## Lap checkpoint — 2026-10-26, canonical model term discharged

One of the four named terms in `subpowerKubiliusCanonicalGroupedBound` is now uniformly controlled.
The canonical geometric partition is sparse in its schedule index, so applying the earlier
consecutive-range model theorem directly would either require artificial filler blocks or obscure
why missing blocks cost nothing.  This lap proved the exact sparse interface and specialized it to
the canonical groups.

- `exists_kubiliusPrimeCutoffLoweredCrossingMass_injective_sum_lt_of_ratio` bounds an arbitrary
  finite family of prime-cutoff crossing masses whose geometric schedule keys are distinct and lie
  beyond a common tail index.  The proof subtracts that tail index, uses injectivity to reindex the
  family into a finite subset of `ℕ`, and compares it with the shifted `tsum` of the already-proved
  summable majorant.  No interval completion and no level-count factor is introduced.
- `exists_subpowerKubiliusCanonical_model_sum_lt` applies the sparse theorem to
  `subpowerKubiliusLevelGroups`.  The previously proved
  `subpowerKubiliusLevelGroup_index_injOn`, retained variance caps, and retained late-key facts
  discharge its hypotheses.  It includes the factor `4` from the shift grouping, so the entire
  model-crossing contribution displayed in the canonical bound is `< ζ`.

The packet declarations `primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement are
unchanged.  `KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide`
was added.  The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning (plus publish-tier tactic guidance).
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_kubiliusPrimeCutoffLoweredCrossingMass_injective_sum_lt_of_ratio
  --axioms NormalNumbers.ErdosBorweinSubpowerKub.exists_subpowerKubiliusCanonical_model_sum_lt` —
  `FORMALIZE-TIER GREEN`; both declarations report exactly `Classical.choice`, `Quot.sound`, and
  `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

Three global terms remain: the square-divisor sum, accumulated `KubiliusTV` error, and exceptional
top band.  The next highest-value attack is the square term because it is independent of the common
cutoff choice: prove the canonical level fibers pairwise disjoint, rewrite their double sum over
ordinary levels, fix any `D > 1` (for example `D = 2`), and dominate
`(blockLogLog ℓ)^{-D}` using `blockLogLog_ge_quarter_add` and a convergent p-series tail.  After
that, choose the common cutoff `Y` to make the TV error small while leaving only a thin exceptional
band for the one-level estimate.

## Review-lap checkpoint — 2026-10-26, canonical square term discharged

Fresh reconstruction from the frozen packet statement, the proved `c > 3` assembly, current
source, and recent commits reconfirmed the route.  The old capped-residual and headline proofs are
independent of `c` after the large-card input, and a diff from planting commit `e61852e6` still has
zero deletions in the scoped file.  Thus the live path remains the canonical grouped bound followed
by the copied final assembly; no statement repair or route change is warranted.

The square-divisor contribution in `subpowerKubiliusCanonicalGroupedBound` is now uniformly
controlled.

- `subpowerKubiliusLevelGroups_pairwiseDisjoint` proves that distinct canonical fibers cannot share
  an arithmetic level, and `subpowerKubiliusLevelGroups_biUnion` proves that their union is exactly
  `subpowerKubiliusOrdinaryLevels`.  The latter includes the empty and truncated cases, so the
  reindexing carries no hidden nonemptiness assumption.
- `summable_blockLogLog_neg_rpow` proves convergence of
  `∑ℓ (blockLogLog ℓ)^{-D}` for every `D > 1`, using
  `blockLogLog ℓ ≥ (ℓ+2)/4` and the shifted real p-series.
- `exists_subpowerKubiliusCanonical_square_sum_lt` unions the disjoint fibers before summing,
  shifts every ordinary level by the starting level `L`, and compares the entire finite double sum
  with the corresponding `tsum` tail.  Consequently the square contribution is `< ζ` uniformly in
  `c`, `T`, and `Y` once `L` is late enough.  The final assembly may specialize to `D = 2`.

The cumulative diff from `e61852e6` is insertion-only (`3179` inserted lines, `0` deleted lines):
`primesUpTo`, `kubiliusMass`, `KubiliusTV`, and the headline statement remain byte-unchanged.
`KubiliusTV` remains only a named hypothesis; no `axiom`, `opaque`, or `native_decide` was added.
The scoped target still has exactly its single frozen headline `sorry`.

Verification actually run:

- `lake env lean src/NormalNumbers/CoefmassErdosBorweinSubpowerKub.lean` — succeeds, with only the
  pre-existing headline `sorry` warning (plus publish-tier tactic guidance).
- `~/personal/bin/lean-green . --target NormalNumbers.CoefmassErdosBorweinSubpowerKub --import
  NormalNumbers.CoefmassErdosBorweinSubpowerKub --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.subpowerKubiliusLevelGroups_pairwiseDisjoint --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.subpowerKubiliusLevelGroups_biUnion --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.summable_blockLogLog_neg_rpow --axioms
  NormalNumbers.ErdosBorweinSubpowerKub.exists_subpowerKubiliusCanonical_square_sum_lt` —
  `FORMALIZE-TIER GREEN`; all four declarations report exactly `Classical.choice`, `Quot.sound`,
  and `propext`.
- `~/personal/bin/lean-green .` — full 10,847-job repository build, `FORMALIZE-TIER GREEN`.

Two global terms remain: the accumulated `KubiliusTV` error and the exceptional top band.  The next
highest-value attack is the common-cutoff schedule that couples them.  Choose a dyadic-exponential
`Y ≤ T` roughly `log log log T` arithmetic levels below the largest active cutoff, prove that every
ordinary group's ratio `log T / log(groupCutoff)` tends uniformly to infinity and that the number
of canonical groups is only logarithmic, then sum
`J*K*((log T/log y)^(-(log T/log y)) + T^{-1/2})` uniformly for the truncated range of shifts.
Retain explicitly that the complementary exceptional set is only the resulting thin top band; the
following checkpoint can apply the one-level fractional-moment estimate there without ever summing
it over the full tail.  These two estimates are the last substantial inputs before
`exists_subpower_marginal_large_cards_le_of_kubilius` and the copied `c > 3` final assembly.
