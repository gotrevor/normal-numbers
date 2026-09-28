# ROUTE ESCALATION — 2026-09-25 (lap 92): input (c) of the Elliott crux is FALSE

**Status: the defect is diagnosed, machine-refuted, and repaired in `src/`.**  No pivot of the
campaign is needed; the decomposition of laps 85–91 was wrong in one parameter (a frequency
threshold) and the repair is strictly cleaner than what it replaces.

## What fired

Not a registered trigger — a **fidelity audit finding** on the crux, which is the same class of
event and outranks a trigger: laps 85–91 reduced `TwoPointElliottLog` to two named classical
`Prop`s, and **one of them is false**, so
`ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density` is *vacuous* and item 4 of the
directive was not in fact achieved.

## The refutation (machine-checked)

`src/NormalNumbers/ElliottArchimedeanRefuted.lean`:

```
NormalNumbers.ElliottArchimedeanRefuted.not_archimedeanCorrelationBound
  {A : ℕ} (hA : 0 < A) {η : ℝ} (hη : 0 < η) : ¬ ArchimedeanCorrelationBound A η
```
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

The refuted statement was

```
ArchimedeanCorrelationBound A η :=
  ∃ X₀, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ v, 1 < |v| log X → |v| ≤ A²X →
    ‖∑_{p≤X} p^{-iv}/p‖ ≤ (1-η)·∑_{p≤X} 1/p .
```

**Witness: `v = 2/log X`.**  It satisfies the hypothesis exactly (`|v| log X = 2 > 1`, and
`|v| < 3 ≤ A²X`), but then `|v| log p ≤ 2` for *every* `p ≤ X`, so the phases never leave a
bounded arc.  With `cos θ ≥ 1 − θ²/2`,

```
Re ∑_{p≤X} p^{-iv}/p  ≥  M(X) − (v²/2)·∑_{p≤X}(log p)²/p
                      ≥  M(X) − (2/(log X)²)·(log X)(log X + C)   [ (log p)² ≤ (log X)(log p) ]
                      ≥  M(X) − 2 − 2C ,
```
`C` the constant of Mertens' first theorem (`exists_mertensOne`).  Since `M(X) → ∞`, this exceeds
`(1−η)M(X)` for every `η > 0` once `M(X) > (2+2C)/η`.  Entirely elementary — one Mertens bound and
one Taylor inequality.

## Why it was wrong, and what is true

The estimate itself is fine; the **frequency range** was not.  The truth is

```
‖∑_{p≤X} p^{-iv}/p‖ = log min(log X, 1/|v|) + O(1)     for |v| ≤ 1,
```
(the main term is `∫_{log 2}^{log X} e^{-ivy} dy/y`, which is `log(1/|v|) + O(1)` once
`1/|v| ≤ log X`).  So a *fixed* relative loss `η` needs

```
|v| ≥ (log X)^{-1+ε},    not    |v| ≥ 1/log X.
```

The old threshold `|v| log X > 1` was chosen because it is exactly where the *other* branch of the
dichotomy stops working: `NearTrivialTwist` and the de-twisting `exists_charDefect_le` both need
`|t| log X ≤ 1` (the de-twisting cost is `2|t|·∑_{p≤X} log p/p ≈ 2|t| log X`).  Raising the
Archimedean threshold therefore opens an **intermediate band**

```
1/log X  ≲  |t|  ≲  (log X)^{-1+ε}
```
covered by neither alternative: there the de-twisting cost is `(log X)^ε ≫ M(X)`, and
`‖C‖ ≈ log(1/|t|)` is within `O(1)` of `M(X)`, so neither `‖C‖ ≤ (1−δ)M` nor `‖C − M‖ = O(1)`
holds.  **Moving the threshold alone does not repair the route.**

## The repair (in `src/`, compiled, axiom-clean)

`src/NormalNumbers/ElliottTwistRepair.lean`.  The insight: the consumer never needed `C ≈ M(X)`.
It needed only that `C` be close to a **nonnegative real number at most `M(X)`**, because the
rotation by `ζ = e(u) ≠ 1` then already costs `(1 − Re ζ)·M(X)`.

```
AlmostRealTwist K χ t X := ∃ R, 0 ≤ R ∧ R ≤ M(X) ∧ ‖C − R‖ ≤ K
```

* `re_phase_mul_twistCorr_le` : `Re(ζ·C) ≤ max(Re ζ, 0)·M(X) + K`.  This is the whole content.
* `almostRealTwist_of_norm_sub_primeMass` / `twistAlmostRealDichotomy_of_old` : the old easy
  branch is the case `R = M(X)`, so the new dichotomy is **weaker** and nothing from laps 85–91 is
  lost.
* `AlmostRealTwist` is *true across the intermediate band*: for principal `χ` and
  `|t| ≤ (log X)^{-1+ε}`, `C = log(1/|t|) + O(1)` and `log(1/|t|) ∈ [0, M(X)]`.

The two inputs are now split at a **threshold function** `T : ℕ → ℝ` (honestly
`T X = (log X)^{-1+ε}`), not at the false `1/log X`:

| input | statement | depth |
|---|---|---|
| **(c′)** `ArchimedeanCorrelationBoundAbove A η T` | `T X < \|v\| ≤ A²X → ‖archCorr v X‖ ≤ (1−η)M(X)` | the only zero-free-region site |
| **(e)** `SmallShiftAlmostReal A K T` | `\|t\| ≤ T X → AlmostRealTwist K χ t X` | Mertens + `L(1,χ) ≠ 0`; **no zero-free region** |

`twistAlmostRealDichotomy_of_inputs` derives the dichotomy from (c′) + (e) with the single
parameter link `A√(2δ) < η` (the bootstrap loss), and
`twoPointElliottLog_of_repaired_inputs` is the payoff.

**What the repair deletes from the critical path:** `CharacterClusterRigidity`, `PrimeDensityAP`,
`exists_charDefect_le`, and the whole de-twisting branch.  Input (e) hands over the easy
alternative directly, so the character never has to be shown principal.  Lap 91's proof of
rigidity from `PrimeDensityAP` survives in `src/` as a proved side result, now off-path.

## The new frontier (supersedes the lap-91 list)

1. **(e) `SmallShiftAlmostReal`** — the new softer pole, and the next lap's target.  Two cases:
   * non-principal `χ`: `‖∑_{p≤X} χ̄(p) p^{-it}/p‖ = O_q(1)`, i.e. `log L(1+it, χ̄)` bounded;
     needs `L(1,χ) ≠ 0` (mathlib has Dirichlet's theorem) and uniformity over `|t| ≤ T X`.
   * principal `χ`: `Im C = −∑_{p≤X} sin(t log p)/p` is `O(1)` *uniformly*, because the main term
     is `Si(t log X) − Si(t log 2)` (bounded!) and the Mertens error contributes
     `O(1 + |t| log log X) = O(1)` on `|t| ≤ (log X)^{-1+ε}`.  `Re C = log(1/|t|) + O(1) ∈ [0,M]`.
     The Lean cost is Abel summation of `∑_{p≤X} f(p)/p` against a two-sided Mertens
     `∑_{p≤u} 1/p = log log u + B + O(1/log u)` — **check whether the two-sided form is already in
     `BoundedGaps` / `Erdos67b.PrimeEstimates`; only the lower bound
     (`characterTwistPrimeMass_mertens_lower`) is currently used.**
2. **(c′) `ArchimedeanCorrelationBoundAbove`** — the long pole, unchanged in depth.  Note the
   dependency's own cited `Erdos67b.PolynomialHeightPrimeCorrelationBound` uses the range
   `Y ≤ |v| ≤ T·Y^D`, i.e. it *only* claims the bound at polynomial height and deliberately avoids
   the small-`v` range — further confirmation that `1/log X` was the wrong threshold.
   A promising unconditional route for the *upper* part of the range, which replaces the zero-free
   region by van der Corput: if `∑_{p≤X}(1 − Re(γ̄ p^{-iv}))/p ≤ ηM` then the completely
   multiplicative `n ↦ n^{iv}` is pretentious to a constant, forcing `|∑_{n≤X} n^{iv}| ≫ X`, while
   van der Corput on dyadic blocks gives `|∑_{n≤X} n^{iv}| ≪ X^{1/2} log X` for `1 ≪ |v| ≪ X²`.
   Record as the alternative to grind if the zero-free region stays out of reach.

## Verdict

Direction **KEPT**, decomposition **REVISED**.  The campaign target (item 4, the downstream
consumer) is unchanged; its reduction now runs through (c′) + (e) instead of (c) + (d1), and the
false statement is refuted in-kernel rather than quietly carried.
