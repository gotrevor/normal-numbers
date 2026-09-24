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

end NormalNumbers.Abelian
