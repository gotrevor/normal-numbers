import NormalNumbers.ElliottEulerBound

/-!
# Case A of leaf 2: a large pretentious defect makes the correlation trivially small

`NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM` splits on the size of
`Σ_X(g₁) = ∑_{p ≤ X}(1 - ‖g₁ p‖)/p`.  When `Σ` is large, the correlation is bounded *pointwise* by
`‖g₁(a₁n+b₁)‖`, so no oscillation is needed: it suffices that the logarithmic mean of the
nonnegative multiplicative function `‖g₁‖` is small, which is the content of
`NormalNumbers.ElliottEulerBound.sum_Icc_le_log_mul_exp_neg_defect`.

This file does the wiring:

* `normDivArith` — `m ↦ ‖g m‖/m` as a multiplicative `ArithmeticFunction ℝ`;
* `norm_elliottLogCorrelation_le_window_sum` — the pointwise bound;
* `sum_window_le_transfer` — the affine-form transfer: the window sum over `n` is at most
  `(a₁ + |b₁|) ∑_{m ≤ a₁X + |b₁|} ‖g m‖/m + |b₁|`.  Bounding the arithmetic progression
  `m ≡ b₁ (mod a₁)` by *all* integers is free here: `a₁` and `b₁` are quantified before `ε`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottCaseA

open Erdos67b
open ArithmeticFunction

noncomputable section

/-- `m ↦ ‖g m‖ / m`, as an arithmetic function. -/
noncomputable def normDivArith (g : ℤ → ℂ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else ‖g (n : ℤ)‖ / (n : ℝ)
  map_zero' := by simp

theorem normDivArith_apply (g : ℤ → ℂ) {n : ℕ} (hn : 0 < n) :
    normDivArith g n = ‖g (n : ℤ)‖ / (n : ℝ) := by
  simp [normDivArith, hn.ne']

theorem normDivArith_nonneg (g : ℤ → ℂ) (n : ℕ) : 0 ≤ normDivArith g n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [normDivArith, h]
  · rw [normDivArith_apply g h]
    have : (0 : ℝ) < n := by exact_mod_cast h
    positivity

theorem normDivArith_le (g : ℤ → ℂ) (hg : ∀ n : ℤ, ‖g n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    normDivArith g n ≤ 1 / (n : ℝ) := by
  rw [normDivArith_apply g hn]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  gcongr
  exact hg _

theorem isMultiplicative_normDivArith {g : ℤ → ℂ} (hg : IsMultiplicativeOnPositiveInt g) :
    (normDivArith g).IsMultiplicative := by
  constructor
  · rw [normDivArith_apply g Nat.one_pos]
    norm_num [hg.1]
  · intro m n _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [normDivArith, hm]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [normDivArith, hn]
    have hmn : 0 < m * n := Nat.mul_pos hm hn
    rw [normDivArith_apply g hmn, normDivArith_apply g hm, normDivArith_apply g hn]
    have hcast : (((m * n : ℕ)) : ℤ) = ((m : ℕ) : ℤ) * ((n : ℕ) : ℤ) := by push_cast; ring
    have := hg.2 m n hm hn
    rw [show ((m * n : ℕ) : ℤ) = ((m * n : ℕ) : ℤ) from rfl]
    rw [this, norm_mul]
    push_cast
    have hmr : (m : ℝ) ≠ 0 := by positivity
    have hnr : (n : ℝ) ≠ 0 := by positivity
    field_simp

/-- The pointwise bound: the correlation is dominated by the window sum of `‖g₁‖`. -/
theorem norm_elliottLogCorrelation_le_window_sum (g₁ g₂ : ℤ → ℂ)
    (hg₂ : ∀ n : ℤ, ‖g₂ n‖ ≤ 1) (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) :
    ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤
      ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ * ‖g₁ (integerAffine a₁ b₁ n)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have hnpos : 0 < n := (mem_elliottLogWindow.mp hn).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [norm_mul, norm_mul, Complex.norm_real, harmonicWeight, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hnr)]
  calc (n : ℝ)⁻¹ * ‖g₁ (integerAffine a₁ b₁ n)‖ * ‖g₂ (integerAffine a₂ b₂ n)‖
      ≤ (n : ℝ)⁻¹ * ‖g₁ (integerAffine a₁ b₁ n)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hg₂ _) (by positivity)
    _ = _ := by ring

/-- **The affine-form transfer.**  The window sum of `‖g(a₁n+b₁)‖/n` is at most
`(a₁+|b₁|)` times the full logarithmic sum of `‖g‖` up to `a₁X+|b₁|`, plus the `|b₁|` terms whose
affine value is nonpositive (where `g` is unconstrained).

Bounding the arithmetic progression by all integers is free: `a₁, b₁` are quantified before `ε`. -/
theorem sum_window_le_transfer {g : ℤ → ℂ} (hg : ∀ n : ℤ, ‖g n‖ ≤ 1)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) (X W : ℕ) :
    ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤
      ((a₁ + b₁.natAbs : ℕ) : ℝ) *
          ∑ m ∈ Finset.Icc 1 (a₁ * X + b₁.natAbs), normDivArith g m
        + (b₁.natAbs : ℝ) := by
  classical
  have hIA : ∀ n : ℕ, integerAffine a₁ b₁ n = (a₁ : ℤ) * n + b₁ := fun n ↦ rfl
  set S := elliottLogWindow X W with hS
  set C : ℝ := ((a₁ + b₁.natAbs : ℕ) : ℝ) with hC
  set Y : ℕ := a₁ * X + b₁.natAbs with hY
  set P : ℕ → Prop := fun n ↦ 0 < integerAffine a₁ b₁ n with hP
  have hsplit : ∑ n ∈ S, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ =
      (∑ n ∈ S with P n, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖) +
        ∑ n ∈ S with ¬ P n, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ :=
    (Finset.sum_filter_add_sum_filter_not S P _).symm
  -- the nonpositive part: at most `|b₁|` terms, each at most `1`
  have hbad : ∑ n ∈ S with ¬ P n, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤
      (b₁.natAbs : ℝ) := by
    have hsub : (S.filter fun n ↦ ¬ P n) ⊆ Finset.Icc 1 b₁.natAbs := by
      intro n hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp hnS).1
      have hle : (a₁ : ℤ) * n + b₁ ≤ 0 := by
        simp only [hP, hIA] at hnP; omega
      have ha : (1 : ℤ) ≤ (a₁ : ℤ) := by exact_mod_cast ha₁
      have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
      have : (n : ℤ) ≤ b₁.natAbs := by
        have h1 : (n : ℤ) ≤ (a₁ : ℤ) * n := by nlinarith
        omega
      exact Finset.mem_Icc.mpr ⟨hnpos, by omega⟩
    have hterm : ∀ n ∈ S.filter fun n ↦ ¬ P n,
        (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤ 1 := by
      intro n hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp (Finset.mem_filter.mp hn).1).1
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have h1 : (n : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact hnr
      calc (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤ (n : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hg _) (by positivity)
        _ ≤ 1 := by simpa using h1
    calc _ ≤ ∑ _n ∈ S.filter fun n ↦ ¬ P n, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = ((S.filter fun n ↦ ¬ P n).card : ℝ) := by simp
      _ ≤ ((Finset.Icc 1 b₁.natAbs).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (b₁.natAbs : ℝ) := by simp
  -- the positive part: reindex by `m = a₁ n + b₁`
  set φ : ℕ → ℕ := fun n ↦ (integerAffine a₁ b₁ n).toNat with hφ
  have hgood : ∑ n ∈ S with P n, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤
      C * ∑ m ∈ Finset.Icc 1 Y, normDivArith g m := by
    have hmem : ∀ n ∈ S.filter P, φ n ∈ Finset.Icc 1 Y := by
      intro n hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnpos, hnX, -⟩ := mem_elliottLogWindow.mp hnS
      simp only [hP, hIA] at hnP
      have hcast : ((φ n : ℕ) : ℤ) = (a₁ : ℤ) * n + b₁ := by
        rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hnP.le
      refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
      have hub : (a₁ : ℤ) * n + b₁ ≤ (Y : ℤ) := by
        rw [hY]
        have h1 : (a₁ : ℤ) * n ≤ (a₁ : ℤ) * X := by
          have : (n : ℤ) ≤ (X : ℤ) := by exact_mod_cast hnX
          have ha : (0 : ℤ) ≤ (a₁ : ℤ) := by positivity
          nlinarith
        push_cast
        have hb : b₁ ≤ |b₁| := le_abs_self b₁
        linarith
      omega
    have hinj : ∀ x ∈ S.filter P, ∀ y ∈ S.filter P, φ x = φ y → x = y := by
      intro x hx y hy hxy
      have hxP := (Finset.mem_filter.mp hx).2
      have hyP := (Finset.mem_filter.mp hy).2
      simp only [hP, hIA] at hxP hyP
      have hcx : ((φ x : ℕ) : ℤ) = (a₁ : ℤ) * x + b₁ := by
        rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hxP.le
      have hcy : ((φ y : ℕ) : ℤ) = (a₁ : ℤ) * y + b₁ := by
        rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hyP.le
      rw [hxy] at hcx
      have ha : (0 : ℤ) < (a₁ : ℤ) := by exact_mod_cast ha₁
      have : (a₁ : ℤ) * x = (a₁ : ℤ) * y := by omega
      have := mul_left_cancel₀ (ne_of_gt ha) this
      exact_mod_cast this
    have hterm : ∀ n ∈ S.filter P,
        (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤ C * normDivArith g (φ n) := by
      intro n hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp hnS).1
      simp only [hP, hIA] at hnP
      have hcast : ((φ n : ℕ) : ℤ) = (a₁ : ℤ) * n + b₁ := by
        rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hnP.le
      have hφpos : 0 < φ n := by omega
      rw [normDivArith_apply g hφpos, hIA, ← hcast]
      have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hφr : (0 : ℝ) < ((φ n : ℕ) : ℝ) := by exact_mod_cast hφpos
      have hbound : ((φ n : ℕ) : ℝ) ≤ C * n := by
        have hint : ((φ n : ℕ) : ℤ) ≤ ((a₁ + b₁.natAbs : ℕ) : ℤ) * n := by
          rw [hcast]
          have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
          push_cast
          have hb : b₁ ≤ |b₁| := le_abs_self b₁
          have hbn : (0 : ℤ) ≤ |b₁| := abs_nonneg b₁
          nlinarith [mul_le_mul_of_nonneg_left hn1 hbn]
        rw [hC]
        exact_mod_cast hint
      have hnormnn : (0 : ℝ) ≤ ‖g ((φ n : ℕ) : ℤ)‖ := norm_nonneg _
      have key : (n : ℝ)⁻¹ ≤ C / ((φ n : ℕ) : ℝ) := by
        rw [inv_eq_one_div, div_le_div_iff₀ hnr hφr]
        linarith
      calc (n : ℝ)⁻¹ * ‖g ((φ n : ℕ) : ℤ)‖
          ≤ (C / ((φ n : ℕ) : ℝ)) * ‖g ((φ n : ℕ) : ℤ)‖ :=
            mul_le_mul_of_nonneg_right key hnormnn
        _ = C * (‖g ((φ n : ℕ) : ℤ)‖ / ((φ n : ℕ) : ℝ)) := by ring
    calc _ ≤ ∑ n ∈ S.filter P, C * normDivArith g (φ n) := Finset.sum_le_sum hterm
      _ = C * ∑ n ∈ S.filter P, normDivArith g (φ n) := by rw [Finset.mul_sum]
      _ = C * ∑ m ∈ (S.filter P).image φ, normDivArith g m := by
          rw [Finset.sum_image hinj]
      _ ≤ C * ∑ m ∈ Finset.Icc 1 Y, normDivArith g m := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ ↦ normDivArith_nonneg g i)
          intro m hm
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
          exact hmem n hn
  rw [hsplit]
  linarith


end

end NormalNumbers.ElliottCaseA

#print axioms NormalNumbers.ElliottCaseA.isMultiplicative_normDivArith
#print axioms NormalNumbers.ElliottCaseA.norm_elliottLogCorrelation_le_window_sum
#print axioms NormalNumbers.ElliottCaseA.sum_window_le_transfer
