# Handoff: 2026-09-22 — frozen `KMT_quant₂` PROVED; sparse normality unconditional

**Branch** `wip/g5-prime-subset` · **HEAD** `e222677` (Part I) · build 🟢 · Fable session
(token allocation expiring 2026-09-23 05:00 EDT).

## What the result says

`NormalNumbers.PrimeModel.KMT.KMT_quant₂_primeModel : KMT_quant₂ C₁ C₂` with
`C₁ k = exp (4k)`, `C₂ k = exp (exp (k+7))` — the literal frozen statement of
`G4WiringSparse.lean`, uniform in the prime set `S` and in the frequency `h`.  Fed to the
existing block construction:

    exists_sparse_normal_unconditional :
      ∃ (S : ℕ → Prop) (_ : DecidablePred S), DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4)

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]`.  No frozen module was
edited (`git diff 7bb2159 HEAD -- G4WiringSparse.lean PrimeModelBrunCount.lean
PrimeModelRadicalState.lean` is empty).  It does **not** say anything about `G₄` or any
classical constant: the normal number is a selected-prime Lambert constant.

## How (five new modules, all sorry-free)

| Module | Content |
|---|---|
| `PrimeModelPhaseAlgebra` | `|1+w| ≤ exp(Re w + |w|²/2)`; `|∏a−∏b| ≤ ∑|a−b|`; least nontrivial site has `Re z ≤ 0`; model phase `‖∏(1+A/p)‖ ≤ e^{2k} exp(−∑1/p)` |
| `PrimeModelPhaseFactor` | `ω_S = ω_{≤y} + ω_{>y}`; E1 `‖W − W_y‖ ≤ 4k·recipSumIoc + 2k²/x`; `∏ z_j^{ω_{≤y}} = residuePhase(n mod k#) · statePhase(actualState)` (needs `k ≤ y` — the one statement fix found in audit) |
| `PrimeModelJointLaw` | empirical joint law on `Fin k# × states`, mass one, fibre-sum identity; Brun lower atoms; transfer `‖W_y − M‖ ≤ 2ke^{20}/T^{1/(2log y)} + 4e^{−σ/2} + 2Q⌊T⌋^k R²/x` |
| `PrimeModelParameters` | regime `ε ≤ 1/(7680k)` ⇒ `log log x > 7680k`; `y=⌊x^ε⌋₊`, `σ = log x/(4 log y)`, `T = x^{1/(4k)}`, `R = x^{1/4}`; all absorptions into `exp(−1/(8k²ε))`; Cauchy–Schwarz vs interval Mertens; constants and their growth |
| `PrimeModelKMT` | assembly; regime R1 by the trivial bound + `brun_large_epsilon_absorbed` |

Spec with every constant: `papers/prime-model-assembly-2026-09-22.md` (Part I).

## Part II: the family theorem — PROVED

Target: `Sparse P` (`π_P(x) log log x ≤ π(x)` eventually) ∧ `DivergentRecip P` ⇒
`IsNormal 4 (subsetLambert P 4)`.  Schedule from the actual mass:
`ε_N = 2/log log N`, `y_N = ⌊N^{ε_N}⌋₊`, `J_N = min(⌊L₃N/24⌋₊, ⌊recipSumLe P y_N/8⌋₊)`.
`PrimeModelFamily.isNormal_subsetLambert_of_sparse : Sparse P → DivergentRecip P →
IsNormal 4 (subsetLambert P 4)`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
`PrimeModelDensityMass` holds the two analytic inputs (dominated Abel summation (M1),
accumulated mass `≤ C + 100 L₃N` (M2)); both modules sorry-free.  Full build 🟢 9125 jobs.
Paper Part II has the verification of all four terms.

**Exact obstacle for the stronger target (relative density zero alone):** the L¹ tail forces
`4^{J} ≫ S_P(N)` while the correlation bound forces (even with bounded constants)
`log log S_P(N) · √δ(N^{ε_N}) → 0`; a set with `π_P ≈ π/L₄` has `S_P ≈ L₂/L₄`, `δ ≈ 1/L₄` and
violates it.  Not a constants problem.  Precisely: the current correlation majorant and the
current L¹ tail criterion cannot both vanish in this growth regime (a conditional growth-regime
obstruction, assuming a genuine counting law `π_P ~ π/L₄`; not a constructed counterexample).
Astra's centered-in-probability consumer (mail 20260922T175904Z) only relaxes `4^J ≫ S` to
`4^J ≫ √S`, which does not escape the regime; see the paper's Part II closing section.

## Addendum (later 2026-09-22): sharper family theorem

`PrimeModelFamilySharp.isNormal_subsetLambert_of_sparseIter : SparseIter P → DivergentRecip P →
IsNormal 4 (subsetLambert P 4)` with `SparseIter P := ∀ᶠ x, π_P(x)·(log log log x)^5 ≤ π(x)`,
and `sparseIter_of_sparse : Sparse P → SparseIter P`.  Axiom-clean.  Mechanism: consume
`window_bound_regime` (polynomial constants) directly, schedule `J_N = min(⌊L₃N⌋₊, ⌊S_P(y_N)/8⌋₊)`,
tail paid by the crude `∑_{p≤2N}1/p ≤ 12L₂N + 21`.  Modules `PrimeModelFamilySharpMass`,
`PrimeModelFamilySharp`; paper Part III.  Next step if wanted: `ε = J^{-4}` schedule → exponent
`2+η` (needs `y_N` lemmas with `P`-dependent `ε`).
