/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPointwise

/-!
# Joint richness: the `t` sampled windows take many values *together*

Lap 48 closed the frequency direction: every `t`-wise statement the capacity premise supports
must average over positions, because a law with a deficit of one bit per window can kill a fixed
pattern outright.  What that witness does **not** kill is *richness* — the box law still takes
`2^{t(m−1)}` distinct values on each block.

This module proves the joint richness statement, which is a genuinely different functional of
the joint law: not "which patterns occur how often" but "how many joint values occur at all".

* `sum_tuple_deficit_le` — the **zero-slack budget for the full `t`-tuple**: a total deficit of
  `Δ` on the joint law leaves a total deficit of at most `Δ` on the `|B|` block tuples.  This is
  `sum_patCoord_deficit_le` with the `ℓ`-pattern replaced by the whole windows, and it is the
  first use of `H₂_le_sum_H₂_map` on the *untruncated* tuple.
* `two_pow_H₂_le_card_support` — entropy is a lower bound on the support: `|supp| ≥ 2^{H₂}`.
* `card_support_tupleOf_ge` — block `b`'s `t` windows jointly take at least `2^{tm − d_b}`
  values, where `d_b` is that block's deficit.
* `card_poorBlocks_lt` — at most `Δ/η` blocks have `d_b > η`.

Together: **all but `Δ/η` of the blocks see at least `2^{tm − η}` distinct joint values.**
Lap 48's witness satisfies this (its `d_b = t`), as it must.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers Real

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ### Entropy as a lower bound on the support -/

/-- The support of a finite law. -/
noncomputable def suppOf {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (M : FinLaw Ω) : Finset Ω :=
  Finset.univ.filter (fun ω => M.p ω ≠ 0)

lemma suppOf_nonempty {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (M : FinLaw Ω) :
    (suppOf M).Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  have hz : ∀ ω : Ω, M.p ω = 0 := by
    intro ω
    by_contra hne
    have : ω ∈ suppOf M := by rw [suppOf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hne⟩
    rw [hcon] at this
    exact absurd this (Finset.notMem_empty ω)
  have := M.sum_p
  rw [Finset.sum_congr rfl (fun ω _ => hz ω)] at this
  simp at this

/-- **Entropy bounds the support from below**: `2^{H₂} ≤ |supp|`. -/
theorem two_pow_H₂_le_card_support {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (M : FinLaw Ω) :
    (2 : ℝ) ^ M.H₂ ≤ ((suppOf M).card : ℝ) := by
  classical
  have hne := suppOf_nonempty M
  have hpos : 0 < (suppOf M).card := Finset.card_pos.2 hne
  have hposR : (0 : ℝ) < ((suppOf M).card : ℝ) := by exact_mod_cast hpos
  have hH : M.H₂ ≤ Real.logb 2 ((suppOf M).card) :=
    M.H₂_le_logb hpos (suppOf M) (fun ω hω => by
      rw [suppOf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hω⟩) le_rfl
  calc (2 : ℝ) ^ M.H₂
      ≤ (2 : ℝ) ^ (Real.logb 2 ((suppOf M).card)) :=
        Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.2 hH
    _ = ((suppOf M).card : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hposR

/-! ### The full `t`-tuple of a block -/

/-- The `t` windows of a block, untruncated. -/
def tupleOf (m t : ℕ) (blk : B → Fin t → A) (b : B) (z : A → Fin (2 ^ m)) :
    Fin t → Fin (2 ^ m) :=
  fun s => z (blk b s)

/-- The coordinate of an atom the blocking misses; covered atoms get a constant. -/
noncomputable def leftTuple (m t : ℕ) (blk : B → Fin t → A) (α : A)
    (z : A → Fin (2 ^ m)) : Fin t → Fin (2 ^ m) :=
  open Classical in
  if (∃ p : B × Fin t, blk p.1 p.2 = α) then (fun _ => ⟨0, Nat.pow_pos (by norm_num)⟩)
  else (fun _ => z α)

/-- The two families, as one indexed family of coordinate maps. -/
noncomputable def richFam (m t : ℕ) (blk : B → Fin t → A) :
    (B ⊕ A) → (A → Fin (2 ^ m)) → (Fin t → Fin (2 ^ m)) :=
  Sum.elim (tupleOf m t blk) (leftTuple m t blk)

/-- Every block tuple carries at most `t·m` bits. -/
theorem H₂_map_tupleOf_le {m t : ℕ} (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (b : B) :
    (L.map (tupleOf m t blk b)).H₂ ≤ (t : ℝ) * (m : ℝ) := by
  classical
  have hpos : 0 < Fintype.card (Fin t → Fin (2 ^ m)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    positivity
  refine ((L.map (tupleOf m t blk b)).H₂_le_logb_card hpos).trans_eq ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [show (((2 ^ m) ^ t : ℕ) : ℝ) = (2 : ℝ) ^ (m * t) by push_cast; rw [← pow_mul]]
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  push_cast
  ring

/-- An atom the blocking covers contributes nothing; one it misses contributes at most `m`. -/
theorem H₂_map_leftTuple_le {m t : ℕ} (ht : 0 < t) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (α : A) :
    (L.map (leftTuple m t blk α)).H₂
      ≤ (if (∃ p : B × Fin t, blk p.1 p.2 = α) then (0 : ℝ) else (m : ℝ)) := by
  classical
  by_cases hcov : ∃ p : B × Fin t, blk p.1 p.2 = α
  · rw [if_pos hcov]
    have hfun : leftTuple m t blk α
        = fun _ : A → Fin (2 ^ m) => (fun _ => ⟨0, Nat.pow_pos (by norm_num)⟩ :
            Fin t → Fin (2 ^ m)) := by
      funext z; simp only [leftTuple]; rw [if_pos hcov]
    rw [hfun]
    exact FinLaw.H₂_map_const_le L _
  · rw [if_neg hcov]
    have hinj : Function.Injective
        (fun v : Fin (2 ^ m) => (fun _ => v : Fin t → Fin (2 ^ m))) := by
      intro a b hab
      exact congrFun hab ⟨0, ht⟩
    have heq : (L.map (leftTuple m t blk α)).H₂
        = (L.map (fun z : A → Fin (2 ^ m) => z α)).H₂ := by
      refine FinLaw.H₂_map_congr_comp L _ hinj _ (fun z => ?_)
      simp only [leftTuple]; rw [if_neg hcov]
    rw [heq]
    exact H₂_le_of_block _

/-- The two families together determine the sample vector. -/
theorem richFam_injective {m t : ℕ} (ht : 0 < t) (blk : B → Fin t → A) :
    Function.Injective (fun z : A → Fin (2 ^ m) =>
      fun i : B ⊕ A => richFam m t blk i z) := by
  classical
  intro z z' h
  funext α
  by_cases hcov : ∃ p : B × Fin t, blk p.1 p.2 = α
  · obtain ⟨p, rfl⟩ := hcov
    have hc := congrFun h (Sum.inl p.1)
    simp only [richFam, Sum.elim_inl] at hc
    exact congrFun hc p.2
  · have hc := congrFun h (Sum.inr α)
    simp only [richFam, Sum.elim_inr, leftTuple] at hc
    simp only [if_neg hcov] at hc
    exact congrFun hc ⟨0, ht⟩

/-- **The `t`-tuple deficit budget, with zero slack.**  A total deficit of `Δ` bits on the joint
law leaves a total deficit of at most `Δ` on the `|B|` block tuples. -/
theorem sum_tuple_deficit_le {m t : ℕ} (ht : 0 < t)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ∑ b : B, ((t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂) ≤ Δ := by
  classical
  have hsub := L.H₂_le_sum_H₂_map (richFam m t blk) (richFam_injective ht blk)
  have hsplit : ∑ i : B ⊕ A, (L.map (richFam m t blk i)).H₂
      = (∑ b : B, (L.map (tupleOf m t blk b)).H₂)
        + ∑ α : A, (L.map (leftTuple m t blk α)).H₂ := by
    rw [Fintype.sum_sum_type]
    rfl
  rw [hsplit] at hsub
  set U : Finset A := Finset.univ.filter (fun α => ¬ ∃ p : B × Fin t, blk p.1 p.2 = α) with hU
  have hcovimg : (Finset.univ.filter (fun α : A => ∃ p : B × Fin t, blk p.1 p.2 = α))
      = Finset.univ.image (fun p : B × Fin t => blk p.1 p.2) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  have hcardU : U.card + Fintype.card B * t = Fintype.card A := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset A)) (p := fun α => ∃ p : B × Fin t, blk p.1 p.2 = α)
    rw [hcovimg, Finset.card_image_of_injective _ hblk] at h1
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1 ⊢
    rw [hU]
    omega
  have hleft : ∑ α : A, (L.map (leftTuple m t blk α)).H₂ ≤ (U.card : ℝ) * (m : ℝ) := by
    calc ∑ α : A, (L.map (leftTuple m t blk α)).H₂
        ≤ ∑ α : A, (if (∃ p : B × Fin t, blk p.1 p.2 = α) then (0 : ℝ) else (m : ℝ)) :=
          Finset.sum_le_sum fun α _ => H₂_map_leftTuple_le ht blk L α
      _ = (U.card : ℝ) * (m : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hconst : ∑ _b : B, ((t : ℝ) * (m : ℝ))
      = (Fintype.card B : ℝ) * ((t : ℝ) * (m : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, hconst]
  have hcr : (U.card : ℝ) + (t : ℝ) * (Fintype.card B : ℝ) = (Fintype.card A : ℝ) := by
    have hc : ((U.card + Fintype.card B * t : ℕ) : ℝ) = ((Fintype.card A : ℕ) : ℝ) := by
      exact_mod_cast hcardU
    push_cast at hc
    linarith [hc]
  have hkey : (Fintype.card B : ℝ) * ((t : ℝ) * (m : ℝ)) + (U.card : ℝ) * (m : ℝ)
      = (m : ℝ) * (Fintype.card A : ℝ) := by
    linear_combination (m : ℝ) * hcr
  linarith [hsub, hleft, hkey]

/-! ### Richness -/

/-- **The joint richness of one block.**  Block `b`'s `t` windows jointly take at least
`2^{tm − d_b}` distinct values, `d_b` being that block's entropy deficit. -/
theorem card_support_tupleOf_ge {m t : ℕ} (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (b : B) {d : ℝ}
    (hd : (t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂ ≤ d) :
    (2 : ℝ) ^ ((t : ℝ) * (m : ℝ) - d) ≤ ((suppOf (L.map (tupleOf m t blk b))).card : ℝ) := by
  refine le_trans ?_ (two_pow_H₂_le_card_support _)
  exact Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.2 (by linarith)

/-- The blocks whose tuple deficit exceeds `η`. -/
noncomputable def poorBlocks (m t : ℕ) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (η : ℝ) : Finset B :=
  open Classical in
  Finset.univ.filter (fun b => η < (t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂)

/-- **Most blocks are rich.**  At most `Δ/η` of the `|B|` blocks have tuple deficit above `η`. -/
theorem card_poorBlocks_le {m t : ℕ} (ht : 0 < t) {η : ℝ} (hη : 0 < η)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ((poorBlocks m t blk L η).card : ℝ) * η ≤ Δ := by
  classical
  have hbudget := sum_tuple_deficit_le ht blk hblk L hΔ
  have hnn : ∀ b : B, 0 ≤ (t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂ := fun b => by
    have := H₂_map_tupleOf_le blk L b
    linarith
  have hsub : ∑ b ∈ poorBlocks m t blk L η,
      ((t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂)
      ≤ ∑ b : B, ((t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hnn b)
  have hlow : ((poorBlocks m t blk L η).card : ℝ) * η
      ≤ ∑ b ∈ poorBlocks m t blk L η,
          ((t : ℝ) * (m : ℝ) - (L.map (tupleOf m t blk b)).H₂) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [poorBlocks, Finset.mem_filter] at hb
    exact hb.2.le
  linarith

/-- **The joint richness endpoint (abstract).**  Under a total deficit of `Δ`, all but at most
`Δ/η` of the blocks see their `t` sampled windows take at least `2^{tm − η}` distinct joint
values.

This is not refuted by `no_pointwise_bound_from_deficit`: that witness has tuple deficit `t`
(one bit per window) and so is itself rich, taking `2^{t(m−1)}` joint values per block. -/
theorem joint_richness {m t : ℕ} (ht : 0 < t) {η : ℝ} (hη : 0 < η)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) {Δ : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    ((poorBlocks m t blk L η).card : ℝ) * η ≤ Δ ∧
      ∀ b ∉ poorBlocks m t blk L η,
        (2 : ℝ) ^ ((t : ℝ) * (m : ℝ) - η)
          ≤ ((suppOf (L.map (tupleOf m t blk b))).card : ℝ) := by
  classical
  refine ⟨card_poorBlocks_le ht hη blk hblk L hΔ, fun b hb => ?_⟩
  rw [poorBlocks, Finset.mem_filter] at hb
  push_neg at hb
  exact card_support_tupleOf_ge blk L b (hb (Finset.mem_univ b))

end NormalNumbers.G4Entropy
