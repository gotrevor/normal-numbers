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
