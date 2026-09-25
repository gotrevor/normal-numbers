import NormalNumbers.ElliottDivisorTail

/-!
# Truncating the window from below

Leaf 2, Case B, the repair of the dichotomy-scale obstruction (`PENDING_WORK.md`, laps 71–75).

The Case A/B dichotomy is on the Euler defect at the *thin* scale `L ≈ a₁X/W`, but the pretentious
transfer needs it at `≈ X`, and the two differ by `≈ log(log X / log L)`, which blows up exactly
when `W` is close to `X`.  The cure is to throw away the bottom of the window: shrinking `W` to
`W'' ≤ W` raises the thin scale to `≈ a₁X/W''` at the cost of the harmonic mass of the discarded
`n ≤ X/W''`, which is at most `1 + log(X/W'')` — and the point of the repair is that `W''` can be
chosen so that this is `≤ (ε/4) log W` while `X ≤ (X/W'')^{16/ε}`.

Because `elliottLogWindow X W = {n : 0 < n ≤ X, X < nW}` is *monotone in `W`*, the truncated
correlation is a genuine `elliottLogCorrelation` at the same `X` — no reindexing is needed.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottWindowTruncate

open Erdos67b

noncomputable section

theorem elliottLogWindow_subset {X W'' W : ℕ} (h : W'' ≤ W) :
    elliottLogWindow X W'' ⊆ elliottLogWindow X W := by
  intro n hn
  obtain ⟨hpos, hnX, hXn⟩ := mem_elliottLogWindow.mp hn
  refine mem_elliottLogWindow.mpr ⟨hpos, hnX, ?_⟩
  exact lt_of_lt_of_le hXn (Nat.mul_le_mul_right _ h)

/-- **The truncation.**  Shrinking the window ratio from `W` to `W''` costs at most the harmonic
mass of the discarded initial segment `n ≤ ⌊X/W''⌋`. -/
theorem norm_le_truncated {g₁ g₂ : ℤ → ℂ} (h₁ : ∀ z : ℤ, ‖g₁ z‖ ≤ 1) (h₂ : ∀ z : ℤ, ‖g₂ z‖ ≤ 1)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) {X W W'' : ℕ} (hW'' : 0 < W'') (hle : W'' ≤ W) :
    ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
      ≤ ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W''‖
        + ∑ m ∈ Finset.Icc 1 (X / W''), (m : ℝ)⁻¹ := by
  classical
  set F : ℕ → ℂ := fun n => (harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) *
    g₂ (integerAffine a₂ b₂ n) with hF
  have hsub := elliottLogWindow_subset (X := X) hle
  have hsplit : ∑ n ∈ elliottLogWindow X W, F n
      = (∑ n ∈ elliottLogWindow X W'', F n)
        + ∑ n ∈ (elliottLogWindow X W) \ (elliottLogWindow X W''), F n := by
    rw [← Finset.sum_sdiff hsub]; ring
  have hbad : (elliottLogWindow X W) \ (elliottLogWindow X W'') ⊆ Finset.Icc 1 (X / W'') := by
    intro n hn
    obtain ⟨hnw, hnout⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hpos, hnX, -⟩ := mem_elliottLogWindow.mp hnw
    refine Finset.mem_Icc.mpr ⟨hpos, ?_⟩
    have hnot : ¬ (X < W'' * n) := by
      intro hc
      exact hnout (mem_elliottLogWindow.mpr ⟨hpos, hnX, hc⟩)
    refine (Nat.le_div_iff_mul_le hW'').mpr ?_
    rw [Nat.mul_comm]
    omega
  have hterm : ∀ n ∈ (elliottLogWindow X W) \ (elliottLogWindow X W''),
      ‖F n‖ ≤ (n : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨hnw, -⟩ := Finset.mem_sdiff.mp hn
    have hpos : 0 < n := (mem_elliottLogWindow.mp hnw).1
    rw [hF]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (harmonicWeight_nonneg n)]
    rw [harmonicWeight]
    have hprod : ‖g₁ (integerAffine a₁ b₁ n)‖ * ‖g₂ (integerAffine a₂ b₂ n)‖ ≤ 1 := by
      calc ‖g₁ (integerAffine a₁ b₁ n)‖ * ‖g₂ (integerAffine a₂ b₂ n)‖ ≤ 1 * 1 :=
            mul_le_mul (h₁ _) (h₂ _) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    nlinarith
  have hrest : ‖∑ n ∈ (elliottLogWindow X W) \ (elliottLogWindow X W''), F n‖
      ≤ ∑ m ∈ Finset.Icc 1 (X / W''), (m : ℝ)⁻¹ := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg hbad ?_
    intro m _ _
    positivity
  calc ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
      = ‖(∑ n ∈ elliottLogWindow X W'', F n)
          + ∑ n ∈ (elliottLogWindow X W) \ (elliottLogWindow X W''), F n‖ := by
        rw [elliottLogCorrelation, ← hsplit]
    _ ≤ ‖∑ n ∈ elliottLogWindow X W'', F n‖
          + ‖∑ n ∈ (elliottLogWindow X W) \ (elliottLogWindow X W''), F n‖ := norm_add_le _ _
    _ ≤ ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W''‖
          + ∑ m ∈ Finset.Icc 1 (X / W''), (m : ℝ)⁻¹ := by
        rw [elliottLogCorrelation]
        linarith [hrest]

/-- The discarded mass, in closed form. -/
theorem discarded_mass_le {N : ℕ} :
    ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ ≤ 1 + Real.log (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have := NormalNumbers.ElliottDivisorTail.sum_Icc_inv_le (a := 1) (b := N) le_rfl hN
    simpa using this

end

end NormalNumbers.ElliottWindowTruncate
