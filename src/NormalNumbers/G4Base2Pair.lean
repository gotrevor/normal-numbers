/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2Blocks
import NormalNumbers.G4Base2TTHyp

/-!
# N6 core: one dyadic block from TT 3.1(i) and N5

On a good scale, TT bound `(W/N)·Σ (g₁(n+h₁) − δ)·g₂(n+h₂)`; the second centring `δ'` costs
`|δ'|` times the shifted mean `(W/N)·Σ (g₁(n+h₁) − δ)`, which N5 controls.
-/

open Finset

namespace NormalNumbers.G4.Base2

/-- **The second centring.** -/
theorem block_bound (s : Finset ℕ) (g₁ g₂ : ℕ → ℝ) {δ δ' c η₁ η₂ D : ℝ} (h₁ h₂ : ℕ)
    (hTT : |c * ∑ n ∈ s, (g₁ (n + h₁) - δ) * g₂ (n + h₂)| ≤ η₁)
    (hmean : |c * ∑ n ∈ s, (g₁ (n + h₁) - δ)| ≤ η₂) (hδ' : |δ'| ≤ D) (hη₂ : 0 ≤ η₂) :
    |c * ∑ n ∈ s, (g₁ (n + h₁) - δ) * (g₂ (n + h₂) - δ')| ≤ η₁ + D * η₂ := by
  have heq : c * ∑ n ∈ s, (g₁ (n + h₁) - δ) * (g₂ (n + h₂) - δ')
      = c * ∑ n ∈ s, (g₁ (n + h₁) - δ) * g₂ (n + h₂) - δ' * (c * ∑ n ∈ s, (g₁ (n + h₁) - δ)) := by
    rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => by ring
  rw [heq]
  refine (abs_sub _ _).trans (add_le_add hTT ?_)
  rw [abs_mul]
  exact mul_le_mul hδ' hmean (abs_nonneg _) ((abs_nonneg _).trans hδ')

/-- Real-valued complex functions: the TT norm is the real absolute value. -/
theorem norm_TT_eq (s : Finset ℕ) (g₁ g₂ : ℕ → ℂ) (hg₁ : ∀ n, (g₁ n).im = 0)
    (hg₂ : ∀ n, (g₂ n).im = 0) (δ c : ℝ) (h₁ h₂ : ℕ) :
    ‖(c : ℝ) • ∑ n ∈ s, (g₁ (n + h₁) - ((δ : ℝ) : ℂ)) * g₂ (n + h₂)‖
      = |c * ∑ n ∈ s, ((g₁ (n + h₁)).re - δ) * (g₂ (n + h₂)).re| := by
  have hre : ∀ n, g₁ n = ((g₁ n).re : ℂ) := fun n => Complex.ext (by simp) (by simp [hg₁ n])
  have hre₂ : ∀ n, g₂ n = ((g₂ n).re : ℂ) := fun n => Complex.ext (by simp) (by simp [hg₂ n])
  have : (c : ℝ) • ∑ n ∈ s, (g₁ (n + h₁) - ((δ : ℝ) : ℂ)) * g₂ (n + h₂)
      = ((c * ∑ n ∈ s, ((g₁ (n + h₁)).re - δ) * (g₂ (n + h₂)).re : ℝ) : ℂ) := by
    rw [Complex.real_smul]
    push_cast
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [← hre, ← hre₂]
  rw [this, Complex.norm_real, Real.norm_eq_abs]

lemma card_Ioc_ap (N W b : ℕ) (hW : 0 < W) :
    |(((Ioc N (2 * N)).filter (fun n => n % W = b % W)).card : ℝ) - (N : ℝ) / W| ≤ 2 := by
  have hset : (Ioc N (2 * N)).filter (fun n => n % W = b % W)
      = (range (2 * N + 1)).filter (fun n => n ≡ b [MOD W])
        \ (range (N + 1)).filter (fun n => n ≡ b [MOD W]) := by
    ext n; simp only [mem_filter, mem_Ioc, mem_sdiff, mem_range]; unfold Nat.ModEq; omega
  have hsub : (range (N + 1)).filter (fun n => n ≡ b [MOD W])
      ⊆ (range (2 * N + 1)).filter (fun n => n ≡ b [MOD W]) := by
    intro n; simp only [mem_filter, mem_range]; exact fun h => ⟨by omega, h.2⟩
  rw [hset, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  have h1 := G4.abs_card_filter_modEq_sub_le (2 * N + 1) W b hW
  have h2 := G4.abs_card_filter_modEq_sub_le (N + 1) W b hW
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have : ((2 * N + 1 : ℕ) : ℝ) / W - ((N + 1 : ℕ) : ℝ) / W = (N : ℝ) / W := by
    push_cast; field_simp; ring
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

lemma abs_sum_Ioc_ite_le (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (p : ℕ → Prop) [DecidablePred p]
    (a h : ℕ) : |∑ m ∈ Ioc a (a + h), if p m then g m else 0| ≤ h := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Ioc a (a + h), |if p m then g m else 0| ≤ ∑ _m ∈ Ioc a (a + h), (1 : ℝ) :=
        sum_le_sum fun m _ => by split_ifs <;> simp [hg m]
    _ = h := by simp

/-- **Shifting a block sum** costs at most `2h`. -/
theorem shift_sum_le (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (N W b h : ℕ) (hh : h ≤ N) :
    |∑ n ∈ (Ioc N (2 * N)).filter (fun n => n % W = b % W), g (n + h)
      - ∑ m ∈ (Ioc N (2 * N)).filter (fun m => m % W = (b + h) % W), g m| ≤ 2 * h := by
  classical
  have hshift : ∑ n ∈ (Ioc N (2 * N)).filter (fun n => n % W = b % W), g (n + h)
      = ∑ m ∈ (Ioc (N + h) (2 * N + h)).filter (fun m => m % W = (b + h) % W), g m := by
    refine sum_nbij' (fun n => n + h) (fun m => m - h) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [mem_filter, mem_Ioc] at hn ⊢
      exact ⟨⟨by omega, by omega⟩, Nat.ModEq.add_right h hn.2⟩
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have h1 : m - h + h = m := by omega
      have h2 : (m - h + h) % W = (b + h) % W := by rw [h1]; exact hm.2
      exact Nat.ModEq.add_right_cancel' h h2
    · intro n _; simp
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm
      omega
    · intro n _; rfl
  rw [hshift, sum_filter, sum_filter]
  set q : ℕ → ℝ := fun m => if m % W = (b + h) % W then g m else 0 with hq
  have e1 := sum_Ioc_consecutive q (show N ≤ N + h by omega) (show N + h ≤ 2 * N + h by omega)
  have e2 := sum_Ioc_consecutive q (show N ≤ 2 * N by omega) (show 2 * N ≤ 2 * N + h by omega)
  have b1 := abs_sum_Ioc_ite_le g hg (fun m => m % W = (b + h) % W) N h
  have b2 := abs_sum_Ioc_ite_le g hg (fun m => m % W = (b + h) % W) (2 * N) h
  have hd : ∑ m ∈ Ioc (N + h) (2 * N + h), q m - ∑ m ∈ Ioc N (2 * N), q m
      = ∑ m ∈ Ioc (2 * N) (2 * N + h), q m - ∑ m ∈ Ioc N (N + h), q m := by linarith
  rw [hd]
  refine (abs_sub _ _).trans ?_
  linarith

/-- **The shifted centred mean** of a block, from the unshifted progression mean. -/
theorem shifted_mean_le (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (N W b h : ℕ) (hW : 0 < W)
    (hN : 0 < N) (hh : h ≤ N) {δ D E : ℝ} (hD : |δ| ≤ D)
    (hmean : |∑ m ∈ (Ioc N (2 * N)).filter (fun m => m % W = (b + h) % W), g m
      - (N : ℝ) / W * δ| ≤ E) :
    |(W : ℝ) / N * ∑ n ∈ (Ioc N (2 * N)).filter (fun n => n % W = b % W), (g (n + h) - δ)|
      ≤ (W : ℝ) / N * (E + 2 * h + 2 * D) := by
  have hs := shift_sum_le g hg N W b h hh
  have hc := card_Ioc_ap N W b hW
  set A := (Ioc N (2 * N)).filter (fun n => n % W = b % W)
  have heq : ∑ n ∈ A, (g (n + h) - δ) = (∑ n ∈ A, g (n + h) - (N : ℝ) / W * δ)
      - δ * ((A.card : ℝ) - (N : ℝ) / W) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity)]
  gcongr
  have h1 : |∑ n ∈ A, g (n + h) - (N : ℝ) / W * δ| ≤ 2 * h + E := by
    have := abs_add_le (∑ n ∈ A, g (n + h)
      - ∑ m ∈ (Ioc N (2 * N)).filter (fun m => m % W = (b + h) % W), g m)
      (∑ m ∈ (Ioc N (2 * N)).filter (fun m => m % W = (b + h) % W), g m - (N : ℝ) / W * δ)
    simp only [sub_add_sub_cancel] at this
    linarith
  have h2 : |δ * ((A.card : ℝ) - (N : ℝ) / W)| ≤ 2 * D := by
    rw [abs_mul]
    have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
    calc |δ| * |(A.card : ℝ) - (N : ℝ) / W| ≤ D * 2 :=
          mul_le_mul hD hc (abs_nonneg _) hD0
      _ = 2 * D := by ring
  refine (abs_sub _ _).trans ?_
  linarith

end NormalNumbers.G4.Base2
