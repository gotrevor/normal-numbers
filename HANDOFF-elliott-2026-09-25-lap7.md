# HANDOFF elliott 2026-09-25 (laps 1–7) — the crux's graph side is largely built

Branch `wip/elliott-port`, HEAD `471136b`.  Working tree clean.  `lake build NormalNumbers.ElliottGeneral`
green (warm tree; never `lake exe cache get`).

## Target

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3).  The dependency `lean-proofs-latest` proves only
`Erdos67b.unitCircleLogElliott` (shift `n, n+h`; `f` completely multiplicative with `‖f‖ = 1`;
`g₂ = conj f`).  Never edit dependency files; never vendor them.

## The ladder (`src/NormalNumbers/ElliottLadder.lean`)

`nonasymptoticLogElliott = nonasymptotic_of_affineCM (affineCM_of_dilatedCM dilatedCMLogElliott)`.

**Two open leaves, both disclosed with full route docstrings:**

1. **`dilatedCMLogElliott` — THE CRUX.**  Two independent completely multiplicative unimodular
   `f₁, f₂`, non-pretentiousness on `f₁` only, affine forms with a common dilation `a·n+c₁`,
   `a·n+c₂`, `c₁ ≠ c₂`.
2. **`nonasymptotic_of_affineCM`** — `1`-bounded multiplicative → completely multiplicative
   unimodular.  Untouched this session; full route in its docstring (Hall/Wirsing dichotomy on
   `∑_{p≤X}(1−‖g₁(p)‖)/p`; in the bounded case two convolution expansions with absolutely convergent
   `∑1/d` tails — `g = g̃ ⋆ u` with `u` supported on squarefull `d`, and `‖g̃‖ = 1 ⋆ v`; the
   divisibility constraints they produce are dilations of the affine form, hence absorbed by
   `AffineCMLogElliott` itself; non-pretentiousness survives with loss of a fixed constant).

**Proved and axiom-clean in the ladder:**
- `affineCM_of_dilatedCM` — Tao's **affine generality is free** on the CM-unimodular rung.  Multiply
  form 1 by `a₂`, form 2 by `a₁`: the pair becomes `(a n + a₂b₁, a n + a₁b₂)` with `a = a₁a₂`, at the
  cost of the *unimodular* constant `f₁(a₂)f₂(a₁)`, so the norms are equal.  `a₁b₂ − a₂b₁ ≠ 0` is
  exactly "the two new shifts differ".  No residue classes, no AP-restricted machinery.
- `unitCircle_of_dilatedCM` — faithfulness anchor: the crux rung really generalises the proved case.
- `positiveIntExtension_natMul`, `elliottLogCorrelation_common_dilation`, `pairObservable`,
  `norm_pairObservable_le_one`, `elliottLogCorrelation_eq_pairObservable`,
  `pairObservable_dilation`, `pairObservable_dilation_twisted`.

## What the crux actually needs (settled this session)

Lap 1 claimed the two-function case was free because the prime dilation is a pointwise isometry.
**That was wrong at the aggregation step and is retracted** in the crux docstring:
`Erdos67b.primeGraphMean` is a *complex* sum over the graph's primes, not a sum of norms, so
`exists_logProb_dyadic_primeGraphMean_lower` needs every edge to contribute the *same* correlation,
and the phase `f₁(p)f₂(p)` varies with `p` and can cancel it.

The repair is a **phase-twisted, two-block prime graph**: attach to each prime the known unimodular
weight `conj (f₁(p) f₂(p))`, and replace `primeGraphEdge`'s hardcoded `b ⊗ conj b` by two blocks.

## `src/NormalNumbers/ElliottTwistedGraph.lean` — ZERO sorries, all axiom-clean

Upper-bound side, **complete**:
- `twistedPrimeGraphMean/Multiplier`, `twistedPrimeGraphMean_eq_fourier` (the weight lives entirely
  inside the multiplier; `blockFourier` untouched).
- `fourth_moment_twistedPrimeGraphMultiplier_le_energy` — **exactly** the untwisted additive-energy
  bound.  Structural reason: `Erdos67b.fourth_moment_weightedExponentialSum_le_energy` already allows
  an arbitrary complex weight with `‖w x‖ ≤ B`.
- `pairShiftEdge` (+ `pairShiftEdge_conj` = `primeGraphEdge` by `rfl`), `pairBlockPairing`,
  `sum_pairBlockPairing_mul_phase` (bilinear orthogonality, from the block-independent primitive
  `Erdos67b.sum_phase_block_shift`), `pairTwistedPrimeGraphMean_eq_fourier`.
- `norm_pairTwistedPrimeGraphMean_le_largeFrequencies` — **the right-hand side involves the Fourier
  first moment of the FIRST block only**; the second enters solely via `‖blockFourier (conj∘c) t‖ ≤ H`
  plus Parseval.  This is *why* Tao assumes non-pretentiousness of `g₁` and nothing about `g₂`.
- `norm_dyadic_twistedPrimeGraphMultiplier_le_primeCounting`,
  `exists_dyadic_twistedPrimeGraphMultiplier_fourth_moment_bound` (same `A`, `P₀`),
  `exists_eventually_twistedPrimeGraphMultiplier_bounds` (same `C`; uniform in the twist),
  `card_pairTwistedLargeFrequencies_le`.
- **`exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`** — the full analogue of
  `Erdos67b.exists_primeGraphMean_small_of_fourier_first_moment`, one of the two analytic inputs to
  the proved case.  Parameter choreography is the dependency's verbatim, which works only because the
  twisted bounds carry the dependency's own constants.

Lower-bound side, decisive step done:
- `pairLogCorrelation` (+ `pairLogCorrelation_conj = logPairCorrelation` by `rfl`), `pairTwist`,
  `norm_pairTwist`, `pairTwist_mul_cancel`, `pair_dilation`, **`pair_dilation_twisted`** (exact),
  `pairTwistedDivisibleObservable`, `norm_..._le_one`,
  **`norm_logProb_pairTwistedDivisible_sub_correlation_le`** — port of
  `Erdos67b.norm_logProb_divisiblePair_sub_correlation_le` with the dependency's *identical* errors
  `2/M + 2j/(L·M)`.

## NEXT (lap 8), in order

1. Port `Erdos67b.exists_logProb_primeGraphMean_correlation_close` to `pairTwistedPrimeGraphMean`.
   Largest remaining port; routes through the CRT/entropy concentration (`primeGraphSum`,
   `primeGraphObservable`, `PrimeGraphDecoupling`, Hoeffding), which consume only `‖edge‖ ≤ 1`
   (`norm_pairShiftEdge_le`).  **Design conclusion already reached: the twist cannot ride inside the
   block** — the weight is indexed by the prime, not the position — so `primeGraphObservable` needs
   the weight threaded, exactly as `twistedPrimeGraphMean` does.
   Note `Erdos67b.primeGraphCorrelationWeight` and `exists_dyadic_primeGraphCorrelationWeight_lower`
   depend only on `H`, `h`, the prime set — **not on the functions** — so they apply unchanged.
2. `exists_logProb_dyadic_primeGraphMean_lower`, then the contradiction assembly mirroring
   `Erdos67b.exists_logPairCorrelation_small_of_fourier_first_moments`.
3. Audit the MRT side (`Erdos67b.mrtModulatedShortIntervalUnrestricted`): applied to `f₁` alone, so it
   should need no change for the crux.  Check whether its `hunit` is used essentially or only via
   `‖·‖ ≤ 1`.
4. Then wire the assembled graph criterion + MRT into `dilatedCMLogElliott`, mirroring
   `Erdos67b.unitCircleLogElliott`'s proof, and handle the common dilation `a` in the window
   bookkeeping (the graph step `n ↦ pn` sends `c₂−c₁` to `p(c₂−c₁)`, the same `h ↦ ph` step).

## Confidence

The crux's graph/Fourier upper bound is done and the lower bound's decisive identity is done, both
with the dependency's own constants — so no step of the remaining graph work has feasibility in
doubt; it is port labour.  Leaf 2 (`1`-bounded → unimodular) is standard multiplicative-function
technology and still entirely unstarted; it is the larger of the two remaining risks.

`DIRECTION.md`'s CURRENT DIRECTIVE predates this lane (2026-09-23 vs the 2026-09-24 Elliott kickoff
and this run's explicit operator scope) and does not mention Elliott; its forbidden-drift list does
not cover these files.  Left unedited, as altitude laps own it.
