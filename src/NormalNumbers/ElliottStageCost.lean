import NormalNumbers.ElliottStageStep
import NormalNumbers.ElliottScaleWindow

/-!
# The expansion step in its *cost-shaped* form

Leaf 2, Case B.  `ElliottStageStep.norm_le_of_reduced` bounds the correlation by

`(M + 4D)·D·e² + (a+|b|)·(1 + log Y − log L)·εt`

for **any** lower bound `L` on the affine form over the window.  Case B always instantiates `L` at
the thin scale `ElliottScaleWindow.thinScale`, and then `ElliottScaleWindow.logRatio_le` turns the
logarithmic ratio into `log W + logRatioConst a b`.  This module performs that instantiation once,
for both arguments, so that the assembly sees a cost of the shape

`(M + 4D)·D·e² + (a+|b|)·(log W + κ)·εt`,

i.e. a piece proportional to `log W` (absorbed by the `ε`-budget) plus an absolute constant
(absorbed by taking `W` large).

Also here: the two small facts about `cmExt` the assembly needs as hypotheses of
`AffineCMLogElliott` (complete multiplicativity and unimodularity on positives), and the
observation that `MRTNonpretentious` only looks at prime values — so it transfers from a cover
`u` to its completely multiplicative extension `cmExt u` for free.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottStageCost

open Erdos67b NormalNumbers.ElliottSquarefullConv NormalNumbers.ElliottRestricted
open NormalNumbers.ElliottReindex NormalNumbers.ElliottScaleWindow
open NormalNumbers.ElliottStageStep

noncomputable section

/-! ## `logRatioConst` is monotone -/

/-- `logRatioConst` is monotone in the dilation and in the size of the shift.  The assembly needs
this because the inner expansion runs at the substituted data `(a₂d₁, a₂n₀₁+b₂)`, which varies
over the finite family, while the `ε`-budget must be fixed in advance. -/
theorem logRatioConst_mono {a a' : ℕ} {b b' : ℤ} (ha : a ≤ a') (hb : b.natAbs ≤ b'.natAbs) :
    logRatioConst a b ≤ logRatioConst a' b' := by
  rw [logRatioConst, logRatioConst]
  have hmono : (5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) : ℕ)
      ≤ 5 * (a' * (2 * b'.natAbs + 2) + b'.natAbs + 1) := by
    have h1 : a * (2 * b.natAbs + 2) ≤ a' * (2 * b'.natAbs + 2) :=
      Nat.mul_le_mul ha (by omega)
    omega
  have hpos : (0 : ℝ) < ((5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) : ℕ) : ℝ) := by
    have : (0 : ℕ) < 5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) := by omega
    exact_mod_cast this
  have := Real.log_le_log hpos (by exact_mod_cast hmono :
    ((5 * (a * (2 * b.natAbs + 2) + b.natAbs + 1) : ℕ) : ℝ)
      ≤ ((5 * (a' * (2 * b'.natAbs + 2) + b'.natAbs + 1) : ℕ) : ℝ))
  linarith

/-! ## The expansion step at the thin scale -/

/-- **The first-argument expansion, cost-shaped.**  `ElliottStageStep.norm_le_of_reduced` at
`L = thinScale`, with `ElliottScaleWindow.logRatio_le` applied to the truncation cost. -/
theorem norm_le_cost_first {U : ℕ → ℂ} (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1)
    {g : ℤ → ℂ} (hg : ∀ z : ℤ, ‖g z‖ ≤ 1)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (a₂ : ℕ) (b₁ b₂ : ℤ) {X W D : ℕ}
    (hW : 2 ≤ W) (hWX : W ≤ X) (hD : 1 ≤ D) (hDY : D ≤ a₁ * X + b₁.natAbs)
    {εt M : ℝ} (hεt : 0 ≤ εt) (hM : 0 ≤ M)
    (htail : ∑ d ∈ Finset.Icc (D + 1) (a₁ * X + b₁.natAbs),
      ‖squarefullPart U d‖ / (d : ℝ) ≤ εt)
    (hbound : ∀ d ∈ Finset.Icc 1 D, ∀ n₀ < d, (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁ →
      ‖elliottLogCorrelation (positiveIntExtension (fun k => cmExt U k)) g
          a₁ (a₂ * d) (newShift a₁ b₁ d n₀) ((a₂ : ℤ) * n₀ + b₂)
          (progScale X n₀ d) (min W (progScale X n₀ d))‖ ≤ M) :
    ‖elliottLogCorrelation (positiveIntExtension U) g a₁ a₂ b₁ b₂ X W‖
      ≤ (M + 4 * (D : ℝ)) * ((D : ℝ) * Real.exp 2)
        + ((a₁ + b₁.natAbs : ℕ) : ℝ) *
            ((Real.log (W : ℝ) + logRatioConst a₁ b₁) * εt) := by
  have hX : 2 ≤ X := le_trans hW hWX
  have hWpos : 0 < W := by omega
  have hbase := norm_le_of_reduced hone hmul hU hg ha₁ a₂ b₁ b₂
    (L := thinScale a₁ b₁ X W) hWpos (one_le_thinScale _ _ _ _) hD hDY
    (thinScale_le_top ha₁ b₁ hW hX)
    (fun n hn hpos => thinScale_le_integerAffine ha₁ b₁ hWpos hn hpos) hεt hM htail hbound
  refine le_trans hbase ?_
  have hratio := logRatio_le ha₁ b₁ hW hWX
  have hC : (0 : ℝ) ≤ ((a₁ + b₁.natAbs : ℕ) : ℝ) := by positivity
  have hstep : (1 + Real.log ((a₁ * X + b₁.natAbs : ℕ) : ℝ)
      - Real.log ((thinScale a₁ b₁ X W : ℕ) : ℝ)) * εt
      ≤ (Real.log (W : ℝ) + logRatioConst a₁ b₁) * εt :=
    mul_le_mul_of_nonneg_right hratio hεt
  have := mul_le_mul_of_nonneg_left hstep hC
  linarith

/-- **The second-argument expansion, cost-shaped.** -/
theorem norm_le_cost_second {U : ℕ → ℂ} (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1)
    {g : ℤ → ℂ} (hg : ∀ z : ℤ, ‖g z‖ ≤ 1)
    (a₁ : ℕ) {a₂ : ℕ} (ha₂ : 0 < a₂) (b₁ b₂ : ℤ) {X W D : ℕ}
    (hW : 2 ≤ W) (hWX : W ≤ X) (hD : 1 ≤ D) (hDY : D ≤ a₂ * X + b₂.natAbs)
    {εt M : ℝ} (hεt : 0 ≤ εt) (hM : 0 ≤ M)
    (htail : ∑ d ∈ Finset.Icc (D + 1) (a₂ * X + b₂.natAbs),
      ‖squarefullPart U d‖ / (d : ℝ) ≤ εt)
    (hbound : ∀ d ∈ Finset.Icc 1 D, ∀ n₀ < d, (d : ℤ) ∣ (a₂ : ℤ) * (n₀ : ℤ) + b₂ →
      ‖elliottLogCorrelation g (positiveIntExtension (fun k => cmExt U k))
          (a₁ * d) a₂ ((a₁ : ℤ) * n₀ + b₁) (newShift a₂ b₂ d n₀)
          (progScale X n₀ d) (min W (progScale X n₀ d))‖ ≤ M) :
    ‖elliottLogCorrelation g (positiveIntExtension U) a₁ a₂ b₁ b₂ X W‖
      ≤ (M + 4 * (D : ℝ)) * ((D : ℝ) * Real.exp 2)
        + ((a₂ + b₂.natAbs : ℕ) : ℝ) *
            ((Real.log (W : ℝ) + logRatioConst a₂ b₂) * εt) := by
  have hX : 2 ≤ X := le_trans hW hWX
  have hWpos : 0 < W := by omega
  have hbase := norm_le_of_reduced_second hone hmul hU hg a₁ ha₂ b₁ b₂
    (L := thinScale a₂ b₂ X W) hWpos (one_le_thinScale _ _ _ _) hD hDY
    (thinScale_le_top ha₂ b₂ hW hX)
    (fun n hn hpos => thinScale_le_integerAffine ha₂ b₂ hWpos hn hpos) hεt hM htail hbound
  refine le_trans hbase ?_
  have hratio := logRatio_le ha₂ b₂ hW hWX
  have hC : (0 : ℝ) ≤ ((a₂ + b₂.natAbs : ℕ) : ℝ) := by positivity
  have hstep : (1 + Real.log ((a₂ * X + b₂.natAbs : ℕ) : ℝ)
      - Real.log ((thinScale a₂ b₂ X W : ℕ) : ℝ)) * εt
      ≤ (Real.log (W : ℝ) + logRatioConst a₂ b₂) * εt :=
    mul_le_mul_of_nonneg_right hratio hεt
  have := mul_le_mul_of_nonneg_left hstep hC
  linarith

/-! ## `cmExt` satisfies the hypotheses of `AffineCMLogElliott` -/

/-- The completely multiplicative extension really is completely multiplicative on positives. -/
theorem isCM_cmExt (U : ℕ → ℂ) :
    IsCompletelyMultiplicativeOnPositive (fun k => cmExt U k) :=
  ⟨cmExt_one U, fun m n hm hn => cmExt_mul U (by omega) (by omega)⟩

/-- The completely multiplicative extension of a unimodular function is unimodular. -/
theorem norm_cmExt_eq_one {U : ℕ → ℂ} (hU : ∀ p : ℕ, p.Prime → ‖U p‖ = 1) {n : ℕ} (hn : 0 < n) :
    ‖cmExt U n‖ = 1 :=
  norm_cmExt hU (by omega)

/-! ## `MRTNonpretentious` only sees prime values -/

/-- The pretentious distance depends on `f` only through its values at the primes `≤ x`. -/
theorem pretentiousDistSq_congr {f f' g : ℕ → ℂ} {x : ℕ}
    (hfe : ∀ p : ℕ, p.Prime → p ≤ x → f p = f' p) :
    pretentiousDistSq f g x = pretentiousDistSq f' g x := by
  rw [pretentiousDistSq, pretentiousDistSq]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [mem_primesUpTo] at hp
  rw [pretentiousTerm, pretentiousTerm, hfe p hp.1 hp.2]

/-- Hence non-pretentiousness transfers along any function agreeing at the primes `≤ X`. -/
theorem mrtNonpretentious_congr {f f' : ℕ → ℂ} {A X : ℕ}
    (hfe : ∀ p : ℕ, p.Prime → p ≤ X → f p = f' p) (h : MRTNonpretentious f A X) :
    MRTNonpretentious f' A X := by
  intro q hq hqA χ t ht
  have := h q hq hqA χ t ht
  rwa [pretentiousDistSqToTwist, pretentiousDistSq_congr hfe] at this

/-- The specialisation used by the assembly: a cover `u` and its completely multiplicative
extension have the same prime values, so non-pretentiousness passes to `cmExt u`. -/
theorem mrtNonpretentious_cmExt {u : ℕ → ℂ} {A X : ℕ} (h : MRTNonpretentious u A X) :
    MRTNonpretentious (fun k => cmExt u k) A X := by
  refine mrtNonpretentious_congr (fun p hp _ => ?_) h
  have := cmExt_prime_pow (U := u) hp 1
  simpa using this.symm

end

end NormalNumbers.ElliottStageCost
