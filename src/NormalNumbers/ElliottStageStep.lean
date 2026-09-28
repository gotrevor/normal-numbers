import NormalNumbers.ElliottRestricted
import NormalNumbers.ElliottCaseAThin

/-!
# One expansion step of Case B

Leaf 2, Case B.  This module packages the composition

`ElliottExpand.norm_elliottLogCorrelation_le_truncated` ∘ `ElliottRestricted.norm_restrictedCorr_le`

into a **single reusable brick**: if every one of the finitely many *reduced* correlations
(one per pair `d ≤ D`, `n₀ < d`) is bounded by `M`, then the original correlation is bounded by
`(M + 4D)·D·e²` plus the truncation cost.

The point of packaging it is that Case B applies this step **twice** — once to expand `U₁`, once
(after `Erdos67b.elliottLogCorrelation_swap`) to expand `U₂` — and the two applications are
literally the same lemma at different affine data.  Expanding both functions simultaneously is a
trap: it produces a two-variable tail `∑ ‖u₁d₁‖‖u₂d₂‖·gcd(d₁,d₂)/(d₁d₂)` whose `gcd` factor breaks
the product bound.  One variable at a time never sees more than one divisor.

## Main results

* `sum_Icc_norm_squarefullPart_le` — `∑_{d ≤ D} ‖u d‖ ≤ D e²`, from the absolute `e²` bound on
  `∑ ‖u d‖/d`.  This is the crude step that makes the per-class additive `4` affordable.
* `norm_le_of_reduced` — the brick.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottStageStep

open Erdos67b NormalNumbers.ElliottSquarefullConv NormalNumbers.ElliottExpand
open NormalNumbers.ElliottRestricted NormalNumbers.ElliottReindex

noncomputable section

/-- **The crude head bound.**  `∑_{d ≤ D} ‖u d‖ ≤ D·e²`: drop the `1/d` from the absolute bound
`∑_{d ≤ D} ‖u d‖/d ≤ e²` at a cost of one factor `D`. -/
theorem sum_Icc_norm_squarefullPart_le {U : ℕ → ℂ} (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1) (D : ℕ) :
    ∑ d ∈ Finset.Icc 1 D, ‖squarefullPart U d‖ ≤ (D : ℝ) * Real.exp 2 := by
  classical
  have hstep : ∀ d ∈ Finset.Icc 1 D,
      ‖squarefullPart U d‖ ≤ (D : ℝ) * (‖squarefullPart U d‖ / (d : ℝ)) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hdD' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
    rw [mul_div_assoc']
    rw [le_div_iff₀ hd0]
    have hnn : (0 : ℝ) ≤ ‖squarefullPart U d‖ := norm_nonneg _
    nlinarith
  calc ∑ d ∈ Finset.Icc 1 D, ‖squarefullPart U d‖
      ≤ ∑ d ∈ Finset.Icc 1 D, (D : ℝ) * (‖squarefullPart U d‖ / (d : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = (D : ℝ) * ∑ d ∈ Finset.Icc 1 D, ‖squarefullPart U d‖ / (d : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (D : ℝ) * Real.exp 2 := by
        have hb := sum_norm_squarefullPart_div_le_exp_two (U := U) hone hmul hU D
        have : (0 : ℝ) ≤ (D : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hb this

/-- **The expansion step.**  Expand the *first* argument `U` of the correlation into its squarefull
part convolved with its completely multiplicative extension `Ũ = cmExt U`, truncate the divisor sum
at `D`, and split each residue class.  If all the reduced correlations — with `Ũ` first, the new
dilations `a₁` and `a₂d`, the new shifts `newShift a₁ b₁ d n₀` and `a₂n₀+b₂`, at the reduced scale
`progScale X n₀ d` — are bounded by `M`, then so is the original, up to the two costs
`4D·D·e²` (the per-class reindexing error) and the uniform squarefull tail. -/
theorem norm_le_of_reduced {U : ℕ → ℂ} (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1)
    {g : ℤ → ℂ} (hg : ∀ z : ℤ, ‖g z‖ ≤ 1)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (a₂ : ℕ) (b₁ b₂ : ℤ) {X W L D : ℕ}
    (hW : 0 < W) (hL : 1 ≤ L) (hD : 1 ≤ D) (hDY : D ≤ a₁ * X + b₁.natAbs)
    (hLY : L ≤ a₁ * X + b₁.natAbs)
    (hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₁ b₁ n →
      (L : ℤ) ≤ integerAffine a₁ b₁ n)
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
            ((1 + Real.log ((a₁ * X + b₁.natAbs : ℕ) : ℝ) - Real.log (L : ℝ)) * εt) := by
  classical
  have hUp : ∀ p : ℕ, p.Prime → ‖U p‖ = 1 := fun p hp => hU p hp.pos
  have hmaster := norm_elliottLogCorrelation_le_truncated (U₁ := U) hone hUp (g₂ := g) hg
    ha₁ a₂ b₁ b₂ X W hL hD hDY hLY hεt hLbd htail
  refine hmaster.trans ?_
  have hhead : ∑ d ∈ Finset.Icc 1 D,
      ‖squarefullPart U d‖ * ‖restrictedCorr U g a₁ a₂ b₁ b₂ X W d‖
      ≤ (M + 4 * (D : ℝ)) * ((D : ℝ) * Real.exp 2) := by
    have hper : ∀ d ∈ Finset.Icc 1 D,
        ‖squarefullPart U d‖ * ‖restrictedCorr U g a₁ a₂ b₁ b₂ X W d‖
        ≤ (M + 4 * (D : ℝ)) * ‖squarefullPart U d‖ := by
      intro d hd
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
      have hd0 : 0 < d := hd1
      have hrc := norm_restrictedCorr_le (U₁ := U) hUp (g₂ := g) hg a₁ a₂ b₁ b₂ (X := X) hd0 hW
      have hclass : ∑ n₀ ∈ (Finset.range d).filter
            (fun n₀ : ℕ => (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁),
          ((d : ℝ)⁻¹ * ‖elliottLogCorrelation
              (positiveIntExtension (fun k => cmExt U k)) g
              a₁ (a₂ * d) (newShift a₁ b₁ d n₀) ((a₂ : ℤ) * n₀ + b₂)
              (progScale X n₀ d) (min W (progScale X n₀ d))‖ + 4)
          ≤ M + 4 * (D : ℝ) := by
        have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hdD' : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
        have hterm : ∀ n₀ ∈ (Finset.range d).filter
            (fun n₀ : ℕ => (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁),
            ((d : ℝ)⁻¹ * ‖elliottLogCorrelation
                (positiveIntExtension (fun k => cmExt U k)) g
                a₁ (a₂ * d) (newShift a₁ b₁ d n₀) ((a₂ : ℤ) * n₀ + b₂)
                (progScale X n₀ d) (min W (progScale X n₀ d))‖ + 4)
            ≤ (d : ℝ)⁻¹ * M + 4 := by
          intro n₀ hn₀
          obtain ⟨hn₀mem, hn₀dvd⟩ := Finset.mem_filter.mp hn₀
          have := hbound d hd n₀ (Finset.mem_range.mp hn₀mem) hn₀dvd
          have hdinv : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
          nlinarith
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((((Finset.range d).filter
            (fun n₀ : ℕ => (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁)).card : ℕ) : ℝ) ≤ (d : ℝ) := by
          have := Finset.card_filter_le (Finset.range d)
            (fun n₀ : ℕ => (d : ℤ) ∣ (a₁ : ℤ) * (n₀ : ℤ) + b₁)
          rw [Finset.card_range] at this
          exact_mod_cast this
        have hposfac : (0 : ℝ) ≤ (d : ℝ)⁻¹ * M + 4 := by positivity
        have hstep := mul_le_mul_of_nonneg_right hcard hposfac
        have hdM : (d : ℝ) * ((d : ℝ)⁻¹ * M + 4) = M + 4 * (d : ℝ) := by
          field_simp
        nlinarith [hstep, hdM.le, hdM.ge]
      have hnn : (0 : ℝ) ≤ ‖squarefullPart U d‖ := norm_nonneg _
      calc ‖squarefullPart U d‖ * ‖restrictedCorr U g a₁ a₂ b₁ b₂ X W d‖
          ≤ ‖squarefullPart U d‖ * (M + 4 * (D : ℝ)) :=
            mul_le_mul_of_nonneg_left (hrc.trans hclass) hnn
        _ = (M + 4 * (D : ℝ)) * ‖squarefullPart U d‖ := by ring
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [← Finset.mul_sum]
    have hDe := sum_Icc_norm_squarefullPart_le hone hmul hU D
    have hMD : (0 : ℝ) ≤ M + 4 * (D : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hDe hMD
  linarith


/-- **The expansion step, applied to the second argument.**  Identical to `norm_le_of_reduced`
after `Erdos67b.elliottLogCorrelation_swap`: here `g` (the *first* function, with dilation `a₁`) is
left alone and the second function `U` is expanded, so the reduced correlations keep `g` first and
carry the new dilation `a₁d` on it. -/
theorem norm_le_of_reduced_second {U : ℕ → ℂ} (hone : U 1 = 1)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → U (x * y) = U x * U y)
    (hU : ∀ n : ℕ, 0 < n → ‖U n‖ = 1)
    {g : ℤ → ℂ} (hg : ∀ z : ℤ, ‖g z‖ ≤ 1)
    (a₁ : ℕ) {a₂ : ℕ} (ha₂ : 0 < a₂) (b₁ b₂ : ℤ) {X W L D : ℕ}
    (hW : 0 < W) (hL : 1 ≤ L) (hD : 1 ≤ D) (hDY : D ≤ a₂ * X + b₂.natAbs)
    (hLY : L ≤ a₂ * X + b₂.natAbs)
    (hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₂ b₂ n →
      (L : ℤ) ≤ integerAffine a₂ b₂ n)
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
            ((1 + Real.log ((a₂ * X + b₂.natAbs : ℕ) : ℝ) - Real.log (L : ℝ)) * εt) := by
  rw [elliottLogCorrelation_swap]
  refine norm_le_of_reduced hone hmul hU hg ha₂ a₁ b₂ b₁ hW hL hD hDY hLY hLbd hεt hM htail ?_
  intro d hd n₀ hn₀ hdvd
  rw [elliottLogCorrelation_swap]
  exact hbound d hd n₀ hn₀ hdvd

end

end NormalNumbers.ElliottStageStep
