/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.Walsh

/-!
# Krawtchouk coefficients for the symmetrized Walsh dual

`kraw L j w` is the coefficient of `X ^ j` in `(1 - X) ^ w * (1 + X) ^ (L - w)`.  The single
fact we need is that for `W ⊆ range L`,

  `∑_{S ⊆ range L, |S| = j} (-1) ^ |S ∩ W| = kraw L j |W|`,

i.e. the symmetrized character sum depends on the window only through its weight.  Working in
`ℝ[X]` lets `Finset.prod_add` do all the combinatorics: no bijection between subsets and
weight-graded pairs is needed.
-/

open Finset Polynomial

namespace NormalNumbers.Abelian

/-- The Krawtchouk coefficient: `[X^j] (1 - X)^w (1 + X)^(L-w)`. -/
noncomputable def kraw (L j w : ℕ) : ℝ :=
  (((1 - X) ^ w * (1 + X) ^ (L - w) : ℝ[X])).coeff j

@[simp] theorem kraw_zero_j (L w : ℕ) : kraw L 0 w = 1 := by
  simp [kraw, coeff_zero_eq_eval_zero]

/-- `kraw L j 0 = choose L j`. -/
theorem kraw_weight_zero (L j : ℕ) : kraw L j 0 = (L.choose j : ℝ) := by
  simp [kraw, add_comm (1 : ℝ[X]) X, Polynomial.coeff_X_add_one_pow]

/-- The generating identity: expanding `∏_{i<L} (1 + ε_i X)` with `Finset.prod_add`. -/
theorem prod_eq_sum_powerset (L : ℕ) (W : Finset ℕ) (hW : W ⊆ range L) :
    ((1 - X) ^ W.card * (1 + X) ^ (L - W.card) : ℝ[X]) =
      ∑ S ∈ (range L).powerset, C ((-1 : ℝ) ^ (S ∩ W).card) * X ^ S.card := by
  have hsplit : ∀ i : ℕ, (if i ∈ W then (-X : ℝ[X]) else X) + 1
      = if i ∈ W then (1 - X) else (1 + X) := by
    intro i; by_cases h : i ∈ W <;> simp [h] <;> ring
  have hL : ∏ i ∈ range L, (((if i ∈ W then (-X : ℝ[X]) else X)) + 1)
      = ((1 - X) ^ W.card * (1 + X) ^ (L - W.card) : ℝ[X]) := by
    rw [Finset.prod_congr rfl (fun i _ => hsplit i)]
    rw [Finset.prod_ite]
    have h1 : (range L).filter (fun i => i ∈ W) = W := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mp (hW h), h⟩⟩
    have h2 : ((range L).filter (fun i => i ∉ W)).card = L - W.card := by
      have he : (range L).filter (fun i => i ∉ W) = (range L) \ W := by
        ext i; simp [Finset.mem_sdiff, Finset.mem_filter]
      rw [he, Finset.card_sdiff, Finset.card_range]
      rw [Finset.inter_eq_left.mpr hW]
    rw [h1, Finset.prod_const, Finset.prod_const, h2]
  rw [← hL, Finset.prod_add]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.prod_const_one, mul_one]
  have : ∏ i ∈ S, (if i ∈ W then (-X : ℝ[X]) else X)
      = (∏ i ∈ S, (if i ∈ W then (-1 : ℝ[X]) else 1)) * ∏ i ∈ S, X := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by by_cases h : i ∈ W <;> simp [h])
  rw [this, Finset.prod_ite_mem, Finset.prod_const, Finset.prod_const,
    Finset.inter_comm S W, Finset.inter_comm W S]
  simp

/-- **The symmetrized character sum is a Krawtchouk coefficient.** -/
theorem sum_powersetCard_neg_one_pow (L j : ℕ) {W : Finset ℕ} (hW : W ⊆ range L) :
    ∑ S ∈ (range L).powersetCard j, (-1 : ℝ) ^ (S ∩ W).card = kraw L j W.card := by
  rw [kraw, prod_eq_sum_powerset L W hW, Polynomial.finsetSum_coeff]
  rw [Finset.powersetCard_eq_filter]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : S.card = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- `(-1)^|A ∩ S|` as a product over `S`. -/
theorem neg_one_pow_inter_eq_prod (A S : Finset ℕ) :
    (-1 : ℝ) ^ (A ∩ S).card = ∏ i ∈ S, (if i ∈ A then (-1 : ℝ) else 1) := by
  rw [Finset.prod_ite_mem, Finset.prod_const, Finset.inter_comm S A]

/-- **Orthogonality of the parity characters on the discrete cube.** -/
theorem sum_powerset_orth (L : ℕ) {T W : Finset ℕ} (hT : T ⊆ range L) (hW : W ⊆ range L) :
    ∑ S ∈ (range L).powerset, (-1 : ℝ) ^ (T ∩ S).card * (-1) ^ (W ∩ S).card
      = if T = W then (2 : ℝ) ^ L else 0 := by
  have key : ∀ S : Finset ℕ, (-1 : ℝ) ^ (T ∩ S).card * (-1) ^ (W ∩ S).card
      = (-1 : ℝ) ^ ((symmDiff T W) ∩ S).card := by
    intro S
    rw [neg_one_pow_inter_eq_prod, neg_one_pow_inter_eq_prod, neg_one_pow_inter_eq_prod,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ W <;>
      simp [Finset.mem_symmDiff, h1, h2]
  rw [Finset.sum_congr rfl (fun S _ => key S)]
  by_cases hTW : T = W
  · subst hTW
    simp [Finset.card_powerset]
  · rw [if_neg hTW]
    refine NormalNumbers.Walsh.sum_neg_one_pow_inter_eq_zero ?_ ?_
    · rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hTW (symmDiff_eq_bot.mp h)
    · intro i hi
      rw [Finset.mem_symmDiff] at hi
      rcases hi with ⟨h, _⟩ | ⟨h, _⟩
      · exact hT h
      · exact hW h

/-- Grading the powerset of `range L` by cardinality. -/
theorem sum_powerset_graded (L : ℕ) (f : Finset ℕ → ℝ) :
    ∑ T ∈ (range L).powerset, f T
      = ∑ j ∈ range (L + 1), ∑ T ∈ (range L).powersetCard j, f T := by
  simpa using Finset.sum_powerset (range L) f

/-- `∑_w kraw L j w * choose L w = 0` for `1 ≤ j`: the symmetrized character has mean zero. -/
theorem sum_kraw_mul_choose (L j : ℕ) (hj : 1 ≤ j) :
    ∑ w ∈ range (L + 1), kraw L j w * (L.choose w : ℝ) = 0 := by
  have h1 : ∀ w ∈ range (L + 1), kraw L j w * (L.choose w : ℝ)
      = ∑ T ∈ (range L).powersetCard w, kraw L j T.card := by
    intro w _
    rw [Finset.sum_congr rfl (fun T hT => by
      rw [(Finset.mem_powersetCard.mp hT).2]), Finset.sum_const, Finset.card_powersetCard,
      Finset.card_range, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl h1]
  rw [← sum_powerset_graded]
  have h2 : ∀ T ∈ (range L).powerset, kraw L j T.card
      = ∑ S ∈ (range L).powersetCard j, (-1 : ℝ) ^ (S ∩ T).card := by
    intro T hT
    exact (sum_powersetCard_neg_one_pow L j (Finset.mem_powerset.mp hT)).symm
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun S hS => ?_)
  obtain ⟨hSL, hScard⟩ := Finset.mem_powersetCard.mp hS
  exact NormalNumbers.Walsh.sum_neg_one_pow_inter_eq_zero
    (Finset.card_pos.mp (by omega)) hSL

/-- **Inversion.**  The weight-`w` indicator expands in the symmetrized characters. -/
theorem sum_kraw_mul_sum (L w : ℕ) {W : Finset ℕ} (hW : W ⊆ range L) :
    ∑ j ∈ range (L + 1), kraw L w j *
        (∑ S ∈ (range L).powersetCard j, (-1 : ℝ) ^ (S ∩ W).card)
      = if W.card = w then (2 : ℝ) ^ L else 0 := by
  have h1 : ∀ j ∈ range (L + 1), kraw L w j *
      (∑ S ∈ (range L).powersetCard j, (-1 : ℝ) ^ (S ∩ W).card)
      = ∑ S ∈ (range L).powersetCard j, kraw L w S.card * (-1 : ℝ) ^ (S ∩ W).card := by
    intro j _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2])
  rw [Finset.sum_congr rfl h1, ← sum_powerset_graded]
  have h2 : ∀ S ∈ (range L).powerset, kraw L w S.card * (-1 : ℝ) ^ (S ∩ W).card
      = ∑ T ∈ (range L).powersetCard w, (-1 : ℝ) ^ (T ∩ S).card * (-1 : ℝ) ^ (W ∩ S).card := by
    intro S hS
    rw [← sum_powersetCard_neg_one_pow L w (Finset.mem_powerset.mp hS), Finset.sum_mul,
      Finset.inter_comm S W]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  have h3 : ∀ T ∈ (range L).powersetCard w,
      ∑ S ∈ (range L).powerset, (-1 : ℝ) ^ (T ∩ S).card * (-1 : ℝ) ^ (W ∩ S).card
        = if T = W then (2 : ℝ) ^ L else 0 := by
    intro T hT
    exact sum_powerset_orth L (Finset.mem_powersetCard.mp hT).1 hW
  rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq' ((range L).powersetCard w) W
    (fun _ => (2 : ℝ) ^ L)]
  by_cases h : W.card = w
  · rw [if_pos (Finset.mem_powersetCard.mpr ⟨hW, h⟩), if_pos h]
  · rw [if_neg (fun hm => h (Finset.mem_powersetCard.mp hm).2), if_neg h]

end NormalNumbers.Abelian
