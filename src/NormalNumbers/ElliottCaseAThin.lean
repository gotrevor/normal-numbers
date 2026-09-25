import NormalNumbers.ElliottHall

/-!
# Case A, the thin window

Leaf 2, step (5) of the `DIRECTION.md` CURRENT DIRECTIVE.

`ElliottCaseA.exists_caseA_threshold` settles Case A in the *thick* regime `log W ≥ θ log X`, by
bounding the window sum by the **full** logarithmic sum `∑_{m ≤ Y} ‖g m‖/m`, which the crude Euler
product controls by `log Y · e^{-Σ}`.  That is useless when `W` is small compared with `X`: the
target is `ε log W`, and `log Y ≈ log X` swamps it.

The thin-window fix is to keep the range.  Every `n` in the window satisfies `X < W n`, so
`a₁ n + b₁ ≥ a₁ ⌊X/W⌋ + a₁ − |b₁| =: L`, and the reindexed sum lands in `[L, Y]` rather than
`[1, Y]`.  Hall's inequality in the dyadic form `ElliottHall.sum_Icc_dyadic_le` then costs only the
**number of dyadic blocks** `⌊log₂(Y/L)⌋ + 1 ≈ log₂ W` — which is the right order — instead of
`log Y`.

The transfer is proved here for an *arbitrary* lower bound `L` supplied as a hypothesis
(`sum_window_le_transfer_ge`); `ElliottCaseA.sum_window_le_transfer` is the case `L = 1`.
`le_integerAffine_of_mem_window` then supplies the concrete `L`.

## Main results

* `sum_window_le_transfer_ge` — the transfer into `[L, Y]`.
* `le_integerAffine_of_mem_window` — the concrete thin lower bound.
* `norm_elliottLogCorrelation_le_caseA_thin` — **the thin-window Case-A bound**, with the dyadic
  block count in place of `log Y`.  No regime hypothesis: it holds for all `W`.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottCaseAThin

open Erdos67b ArithmeticFunction NormalNumbers.ElliottCaseA NormalNumbers.ElliottHall
open NormalNumbers.ElliottEulerBound

noncomputable section

/-- **The transfer, keeping the range.**  Identical to `ElliottCaseA.sum_window_le_transfer`
except that the reindexed sum is taken over `[L, Y]`, for any `L` that lower-bounds the affine form
on the window. -/
theorem sum_window_le_transfer_ge {g : ℤ → ℂ} (hg : ∀ n : ℤ, ‖g n‖ ≤ 1)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) (X W : ℕ) {L : ℕ} (hL : 1 ≤ L)
    (hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₁ b₁ n →
      (L : ℤ) ≤ integerAffine a₁ b₁ n) :
    ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤
      ((a₁ + b₁.natAbs : ℕ) : ℝ) *
          ∑ m ∈ Finset.Icc L (a₁ * X + b₁.natAbs), normDivArith g m
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
  have hbad : ∑ n ∈ S with ¬ P n, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤
      (b₁.natAbs : ℝ) := by
    have hsub : (S.filter fun n ↦ ¬ P n) ⊆ Finset.Icc 1 b₁.natAbs := by
      intro n hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp hnS).1
      simp only [hP, hIA, not_lt] at hnP
      have ha : (1 : ℤ) ≤ (a₁ : ℤ) := by exact_mod_cast ha₁
      have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnpos
      have hbn : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
      have hnegb : -b₁ ≤ |b₁| := neg_le_abs b₁
      have hle : (n : ℤ) ≤ (a₁ : ℤ) * n := le_mul_of_one_le_left (by linarith) ha
      have : (n : ℤ) ≤ (b₁.natAbs : ℤ) := by rw [hbn]; linarith
      exact Finset.mem_Icc.mpr ⟨hnpos, by exact_mod_cast this⟩
    have hterm : ∀ n ∈ S.filter fun n ↦ ¬ P n,
        (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤ 1 := by
      intro n hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp (Finset.mem_filter.mp hn).1).1
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have h1 : (n : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hnr
      calc (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤ (n : ℝ)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hg _) (by positivity)
        _ ≤ 1 := by simpa using h1
    calc _ ≤ ∑ _n ∈ S.filter fun n ↦ ¬ P n, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = ((S.filter fun n ↦ ¬ P n).card : ℝ) := by simp
      _ ≤ ((Finset.Icc 1 b₁.natAbs).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (b₁.natAbs : ℝ) := by simp
  set φ : ℕ → ℕ := fun n ↦ (integerAffine a₁ b₁ n).toNat with hφ
  have hgood : ∑ n ∈ S with P n, (n : ℝ)⁻¹ * ‖g (integerAffine a₁ b₁ n)‖ ≤
      C * ∑ m ∈ Finset.Icc L Y, normDivArith g m := by
    have hmem : ∀ n ∈ S.filter P, φ n ∈ Finset.Icc L Y := by
      intro n hn
      obtain ⟨hnS, hnP⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnpos, hnX, -⟩ := mem_elliottLogWindow.mp hnS
      have hnP' : (0 : ℤ) < integerAffine a₁ b₁ n := hnP
      have hcast : ((φ n : ℕ) : ℤ) = (a₁ : ℤ) * n + b₁ := by
        rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hnP'.le
      have hlow : (L : ℤ) ≤ ((φ n : ℕ) : ℤ) := by
        rw [hcast, ← hIA n]; exact hLbd n hnS hnP'
      have hub : (a₁ : ℤ) * n + b₁ ≤ (Y : ℤ) := by
        rw [hY]
        have h1 : (a₁ : ℤ) * n ≤ (a₁ : ℤ) * X := by
          have : (n : ℤ) ≤ (X : ℤ) := by exact_mod_cast hnX
          have ha : (0 : ℤ) ≤ (a₁ : ℤ) := by positivity
          nlinarith
        push_cast
        have hb : b₁ ≤ |b₁| := le_abs_self b₁
        have hbn : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
        linarith
      refine Finset.mem_Icc.mpr ⟨by exact_mod_cast hlow, ?_⟩
      omega
    have hinj : ∀ x ∈ S.filter P, ∀ y ∈ S.filter P, φ x = φ y → x = y := by
      intro x hx y hy hxy
      have hxP : (0 : ℤ) < integerAffine a₁ b₁ x := (Finset.mem_filter.mp hx).2
      have hyP : (0 : ℤ) < integerAffine a₁ b₁ y := (Finset.mem_filter.mp hy).2
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
      have hnP' : (0 : ℤ) < integerAffine a₁ b₁ n := hnP
      have hcast : ((φ n : ℕ) : ℤ) = (a₁ : ℤ) * n + b₁ := by
        rw [hφ]; simpa [hIA] using Int.toNat_of_nonneg hnP'.le
      have hφpos : 0 < φ n := by
        have : (0 : ℤ) < ((φ n : ℕ) : ℤ) := by rw [hcast]; simpa [hIA] using hnP'
        exact_mod_cast this
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
          have hbe : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
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
      _ = C * ∑ m ∈ (S.filter P).image φ, normDivArith g m := by rw [Finset.sum_image hinj]
      _ ≤ C * ∑ m ∈ Finset.Icc L Y, normDivArith g m := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ ↦ normDivArith_nonneg g i)
          intro m hm
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
          exact hmem n hn
  rw [hsplit]
  linarith

/-- **The concrete thin lower bound.**  `X < W n` forces `n ≥ ⌊X/W⌋ + 1`, hence
`a₁ n + b₁ ≥ a₁ (⌊X/W⌋ + 1) − |b₁|`. -/
theorem le_integerAffine_of_mem_window {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) {X W : ℕ} (hW : 0 < W)
    {n : ℕ} (hn : n ∈ elliottLogWindow X W) (hpos : 0 < integerAffine a₁ b₁ n) :
    ((a₁ * (X / W + 1) - b₁.natAbs : ℕ) : ℤ) ≤ integerAffine a₁ b₁ n := by
  obtain ⟨hnpos, -, hXW⟩ := mem_elliottLogWindow.mp hn
  have hnlow : X / W + 1 ≤ n := by
    have hXW' : X < n * W := by rw [Nat.mul_comm]; exact hXW
    have : X / W < n := (Nat.div_lt_iff_lt_mul hW).mpr hXW'
    omega
  have hb : (b₁.natAbs : ℤ) = |b₁| := (Int.abs_eq_natAbs b₁).symm
  have hstep : ((a₁ * (X / W + 1) : ℕ) : ℤ) - (b₁.natAbs : ℤ) ≤ integerAffine a₁ b₁ n := by
    rw [integerAffine]
    have h1 : ((a₁ * (X / W + 1) : ℕ) : ℤ) ≤ (a₁ : ℤ) * n := by
      push_cast
      have : ((X / W + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnlow
      have ha : (0 : ℤ) ≤ (a₁ : ℤ) := by positivity
      push_cast at this
      nlinarith
    have h2 : -(b₁.natAbs : ℤ) ≤ b₁ := by rw [hb]; exact neg_abs_le b₁
    linarith
  rcases Nat.lt_or_ge (a₁ * (X / W + 1)) b₁.natAbs with hlt | hge
  · have hz : (a₁ * (X / W + 1) - b₁.natAbs : ℕ) = 0 := by omega
    rw [hz]
    simpa using hpos.le
  · have hex : ((a₁ * (X / W + 1) - b₁.natAbs : ℕ) : ℤ)
        = ((a₁ * (X / W + 1) : ℕ) : ℤ) - (b₁.natAbs : ℤ) := by
      have : b₁.natAbs ≤ a₁ * (X / W + 1) := hge
      push_cast [Nat.cast_sub this]
      ring
    rw [hex]
    exact hstep

/-- **The thin-window Case-A bound.**  The block count `⌊log₂(Y/L)⌋ + 1` replaces `log Y`; with
`L ≈ a₁ X / W` the count is `≈ log₂ W`, which is the right order for the target `ε log W`.

Unlike `ElliottCaseA.exists_caseA_threshold` this carries **no regime hypothesis** on `W` versus
`X`, so it covers every window. -/
theorem norm_elliottLogCorrelation_le_caseA_thin {g₁ g₂ : ℤ → ℂ}
    (hm₁ : IsMultiplicativeOnPositiveInt g₁)
    (h₁ : ∀ n : ℤ, ‖g₁ n‖ ≤ 1) (h₂ : ∀ n : ℤ, ‖g₂ n‖ ≤ 1)
    {a₁ : ℕ} (ha₁ : 0 < a₁) (b₁ : ℤ) (a₂ : ℕ) (b₂ : ℤ) {X W : ℕ} (hW : 0 < W)
    {L : ℕ} (hL : 1 ≤ L) (hLle : L ≤ a₁ * (X / W + 1) - b₁.natAbs) :
    ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤
      ((a₁ + b₁.natAbs : ℕ) : ℝ) *
          (((Nat.log 2 ((a₁ * X + b₁.natAbs) / L) + 1 : ℕ) : ℝ) *
            (2 * hallConst * Real.exp (1 + Erdos67b.PrimeEstimates.mertensBound) *
              Real.exp (-primeDefect (normDivArith g₁) L)))
        + (b₁.natAbs : ℝ) := by
  have hLbd : ∀ n ∈ elliottLogWindow X W, 0 < integerAffine a₁ b₁ n →
      (L : ℤ) ≤ integerAffine a₁ b₁ n := by
    intro n hn hpos
    refine le_trans ?_ (le_integerAffine_of_mem_window ha₁ b₁ hW hn hpos)
    exact_mod_cast hLle
  have hCnn : (0 : ℝ) ≤ ((a₁ + b₁.natAbs : ℕ) : ℝ) := by positivity
  calc ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
      ≤ ∑ n ∈ elliottLogWindow X W, (n : ℝ)⁻¹ * ‖g₁ (integerAffine a₁ b₁ n)‖ :=
        norm_elliottLogCorrelation_le_window_sum g₁ g₂ h₂ a₁ a₂ b₁ b₂ X W
    _ ≤ ((a₁ + b₁.natAbs : ℕ) : ℝ) *
          ∑ m ∈ Finset.Icc L (a₁ * X + b₁.natAbs), normDivArith g₁ m + (b₁.natAbs : ℝ) :=
        sum_window_le_transfer_ge h₁ ha₁ b₁ X W hL hLbd
    _ ≤ _ := by
        have := sum_Icc_dyadic_le (g := g₁) hm₁ h₁ (L := L) (Y := a₁ * X + b₁.natAbs) hL
        have hmul := mul_le_mul_of_nonneg_left this hCnn
        linarith

end

end NormalNumbers.ElliottCaseAThin
