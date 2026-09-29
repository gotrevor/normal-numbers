/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-B2: the bootstrap, and why it cannot close the crux

Lap 30's note said the tail cell (`w = []`) of `OrbitCellBound` is the sub-statement that must
control the general cell, "a bootstrap, not a bypass".  Laps 38–40 then showed the tail cell is
*exactly* the Gauss–Kuzmin tail law for the image, with no slack left on the Diophantine side.
This module settles what the bootstrap actually buys.

**The unconditional half (new, proved here).**  `blockCount_cellSet_le_shift`: for every
irrational `y ∈ (0,1)`, every word `w` and every `T`,

    blockCount (cellSet w T) p y ≤ blockCount (cellSet [] T) p y + w.length .

The reason is the shift: `Gⁿ y ∈ cellSet w T` forces `Gⁿ⁺ᴸ y ∈ cellSet [] T` (`cfDigit_add`),
and `n ↦ n + L` is injective.  So the general cell's frequency is *always* at most the tail
cell's frequency — no hypothesis, no geometry.  With `cellSet_mono_threshold` the other marginal
is free too: `blockCount (cellSet w T) ≤ blockCount (cfCylinder w)`.

**Why that is not enough (also proved here).**  The crux demands
`freq(w,T) ≤ C · γ(cellSet w T)`, and `γ(cellSet w T) ≍ γ(I_w) · γ(cellSet [] T)` — a PRODUCT.
The two unconditional bounds give only the MINIMUM of the two marginal frequencies, and
`min a b ≤ C · a · b` is false for every `C` (`not_min_le_const_mul`, with the explicit witness
`a = b = 1/(2C)`).  So no combination of the tail cell with the word-frequency bound can produce
the general cell: the crux needs the *joint* law of "word `w` then a large digit" in the image,
i.e. genuine independence, not two marginals.

This is the precise sense in which the `w ≠ []` cells are not a corollary of the `w = []` one —
and, with laps 38–40, it says the remaining content of `OrbitCellBound` is entirely the joint
statistics of the image expansion (fact (γ)), with every counting-side route now closed.
-/
import NormalNumbers.VandeheyS7Cell
import NormalNumbers.GaussKB

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-- Reading the word `w` and then a large digit forces a large digit `w.length` steps later. -/
lemma mem_cellSet_nil_of_mem_cellSet {z : ℝ} (hz : Irrational z) (hmem : z ∈ Set.Ioo (0:ℝ) 1)
    {w : List ℕ} {T : ℕ} (h : z ∈ cellSet w T) :
    gaussMap^[w.length] z ∈ cellSet [] T := by
  obtain ⟨-, hd⟩ := h
  obtain ⟨hirr', hmem'⟩ := irrational_orbit z hz hmem w.length
  refine ⟨?_, ?_⟩
  · rw [cfCylinder_nil]; exact hmem'
  · simpa [List.length_nil] using (cfDigit_add z w.length 0) ▸ (by simpa using hd)

/-- **The shift bound.**  Unconditionally, the general cell is visited no more often than the
tail cell, up to the word length. -/
theorem blockCount_cellSet_le_shift {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (w : List ℕ) (T p : ℕ) :
    blockCount (cellSet w T) p y ≤ blockCount (cellSet [] T) p y + w.length := by
  classical
  set L := w.length with hL
  -- step 1: pointwise domination after the shift
  have hpt : ∀ k, blockIndic (cellSet w T) (gaussMap^[k] y)
      ≤ blockIndic (cellSet [] T) (gaussMap^[L + k] y) := by
    intro k
    by_cases hk : gaussMap^[k] y ∈ cellSet w T
    · obtain ⟨hirr', hmem'⟩ := irrational_orbit y hy hmem k
      have hmem2 := mem_cellSet_nil_of_mem_cellSet hirr' hmem' hk
      have heq : gaussMap^[L + k] y = gaussMap^[w.length] (gaussMap^[k] y) := by
        rw [← hL, Function.iterate_add_apply]
      rw [blockIndic, blockIndic, Set.indicator_of_mem hk, heq, Set.indicator_of_mem hmem2]
      simp
    · rw [blockIndic, Set.indicator_of_notMem hk]
      exact blockIndic_nonneg _ _
  -- step 2: the shifted sum is a sum over `Ico L (p+L)`, inside the longer range
  have hrw : ∑ k ∈ Finset.range p, blockIndic (cellSet [] T) (gaussMap^[L + k] y)
      = ∑ j ∈ Finset.Ico L (p + L), blockIndic (cellSet [] T) (gaussMap^[j] y) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  have h2 : ∑ j ∈ Finset.Ico L (p + L), blockIndic (cellSet [] T) (gaussMap^[j] y)
      ≤ ∑ j ∈ Finset.range (p + L), blockIndic (cellSet [] T) (gaussMap^[j] y) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => blockIndic_nonneg _ _)
    intro j hj
    obtain ⟨-, h⟩ := Finset.mem_Ico.1 hj
    exact Finset.mem_range.2 h
  -- step 3: the longer range costs at most `L`
  have h3 : ∑ j ∈ Finset.range (p + L), blockIndic (cellSet [] T) (gaussMap^[j] y)
      ≤ (∑ j ∈ Finset.range p, blockIndic (cellSet [] T) (gaussMap^[j] y)) + L := by
    rw [Finset.sum_range_add]
    have hle : ∑ j ∈ Finset.range L, blockIndic (cellSet [] T) (gaussMap^[p + j] y) ≤ (L:ℝ) := by
      calc ∑ j ∈ Finset.range L, blockIndic (cellSet [] T) (gaussMap^[p + j] y)
          ≤ ∑ _j ∈ Finset.range L, (1:ℝ) :=
            Finset.sum_le_sum fun j _ => blockIndic_le_one _ _
        _ = (L:ℝ) := by simp
    linarith
  calc blockCount (cellSet w T) p y
      = ∑ k ∈ Finset.range p, blockIndic (cellSet w T) (gaussMap^[k] y) := rfl
    _ ≤ ∑ k ∈ Finset.range p, blockIndic (cellSet [] T) (gaussMap^[L + k] y) :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = _ := hrw
    _ ≤ _ := h2
    _ ≤ _ := h3

/-- **The obstruction.**  The crux asks for the PRODUCT `γ(I_w) · γ(cellSet [] T)`; the two
unconditional marginal bounds give only the MINIMUM, and no constant converts one into the
other.  Witness: `a = b = 1/(2C)`. -/
theorem not_min_le_const_mul {C : ℝ} (hC : 0 < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧ C * (a * b) < min a b := by
  refine ⟨min (1/(2*C)) 1, min (1/(2*C)) 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · exact min_le_right _ _
  · exact lt_min (by positivity) (by norm_num)
  · exact min_le_right _ _
  · set a := min (1/(2*C)) 1 with ha
    have hapos : 0 < a := lt_min (by positivity) (by norm_num)
    have hale : a ≤ 1/(2*C) := min_le_left _ _
    rw [min_self]
    have : C * (a * a) ≤ C * ((1/(2*C)) * a) := by
      have := mul_le_mul_of_nonneg_right hale hapos.le
      nlinarith
    have hhalf : C * ((1/(2*C)) * a) = a / 2 := by field_simp
    linarith [hhalf ▸ this, hapos]

section Audit

#print axioms blockCount_cellSet_le_shift
#print axioms not_min_le_const_mul

end Audit

end NormalNumbers.VandeheyS7
