/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiTupleMass

/-!
# The per-tuple bound: step 4's analytic half

`inner_pair_bound` (`C3MrtTwoShift`) turns the rung's bound `R` on the Elliott window into the
per-pair bound `1 + (3 + R + log A)/(de)` that `full_sum_bound` consumes.  This file does the
same at `K` points, for `multi_full_sum_bound`.

The three ingredients of the `K = 2` proof are all *blind to the number of shifts* — they only
use `‖G j‖ ≤ 1` for the phase `G` — so they are extracted here in generic form and then applied
to `G j = ∏_{i<K} z_i^{Ω(c_i j + b_i)}`:

* `inner_harmonic_le_generic` — peel `j = 0` and transfer the weight `(Lj+a+1)^{-1} → L^{-1}j^{-1}`
  (`weight_transfer`), cost `(a+1)^{-1} + 2/L`;
* `window_gap_generic` — the gap between the rung's window `(0, A^{⌊log_A J⌋}]` and the cutoff
  `(0, J]` has harmonic mass `≤ 1 + log A` (`harmonic_gap_le_log`);
* `progression_sum_bound_generic` — their composition, the generic `progression_sum_bound`.

Only then does the `K`-dependence enter, through `multi_rung_spelling` (our weighted sum IS the
`K`-point correlation `kPointLogCorrelation` is stated with) and `inner_sum_multi_forms` (the
joint progression IS a single class, reindexed to linear forms).
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- **Weight transfer, generic in the phase.**  `joint_inner_harmonic_le` with an arbitrary
unimodular-bounded `G`; the two-shift proof never used the shape of the phase. -/
theorem inner_harmonic_le_generic {L a : ℕ} (hL : 0 < L) (haL : a + 1 ≤ L) (J : ℕ)
    (G : ℕ → ℂ) (hG : ∀ j, ‖G j‖ ≤ 1) :
    ‖∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ (((a : ℝ) + 1)⁻¹ + 2 / (L : ℝ))
        + (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
  classical
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hsplit : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
    ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 J := by simp
  rw [hsplit, Finset.sum_insert h0]
  have hwt : ∀ j : ℕ, (((L * j + a : ℕ) : ℝ) + 1)⁻¹ = (((L * j + (a + 1) : ℕ) : ℝ))⁻¹ := by
    intro j; push_cast; ring
  have hrw : ∑ j ∈ Finset.Icc 1 J, ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j
      = ∑ j ∈ Finset.Icc 1 J, ((((L * j + (a + 1) : ℕ) : ℝ))⁻¹ : ℝ) • G j :=
    Finset.sum_congr rfl fun j _ => by rw [hwt j]
  have htrans := weight_transfer (L := L) (a := a + 1) hL haL J G hG
  have hhead : ‖((((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G 0‖ ≤ ((a : ℝ) + 1)⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hcast : (((L * 0 + a : ℕ) : ℝ) + 1)⁻¹ = ((a : ℝ) + 1)⁻¹ := by norm_num
    rw [hcast, abs_of_nonneg (by positivity)]
    calc ((a : ℝ) + 1)⁻¹ * ‖G 0‖ ≤ ((a : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hG 0) (by positivity)
      _ = ((a : ℝ) + 1)⁻¹ := mul_one _
  have htail : ‖∑ j ∈ Finset.Icc 1 J, ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ 2 / (L : ℝ) + (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
    rw [hrw]
    have hsub := norm_sub_norm_le
      (∑ j ∈ Finset.Icc 1 J, ((((L * j + (a + 1) : ℕ) : ℝ))⁻¹ : ℝ) • G j)
      ((L : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j)
    have hnsm : ‖(L : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖
        = (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnsm] at hsub
    have := le_trans hsub htrans
    linarith
  refine le_trans (norm_add_le _ _) ?_
  linarith [hhead, htail]

/-- **The window gap, generic in the phase.**  Extending the rung's window `(0, A^{⌊log_A J⌋}]`
to the cutoff `(0, J]` costs at most `1 + log A`, an `N`-independent constant. -/
theorem window_gap_generic {A J : ℕ} (hA : 2 ≤ A) (hJ1 : 1 ≤ J) (G : ℕ → ℂ)
    (hG : ∀ j, ‖G j‖ ≤ 1) {R : ℝ}
    (hrung : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R) :
    ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R + (1 + Real.log A) := by
  set m := Nat.log A J with hm
  set Z : ℕ → ℂ := fun j => (((j : ℝ))⁻¹ : ℝ) • G j with hZ
  have hlow : A ^ m ≤ J := Nat.pow_log_le_self A (by omega)
  have hsplit := Finset.sum_Ioc_consecutive Z (Nat.zero_le (A ^ m)) hlow
  have hgap : ‖∑ j ∈ Finset.Ioc (A ^ m) J, Z j‖ ≤ 1 + Real.log A := by
    have hterm : ∀ j ∈ Finset.Ioc (A ^ m) J, ‖Z j‖ ≤ ((j : ℝ))⁻¹ := by
      intro j _
      rw [hZ]
      simp only []
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ((j : ℝ))⁻¹ * ‖G j‖ ≤ ((j : ℝ))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (hG j) (by positivity)
        _ = ((j : ℝ))⁻¹ := mul_one _
    exact le_trans (norm_sum_le _ _)
      (le_trans (Finset.sum_le_sum hterm) (harmonic_gap_le_log hA hJ1))
  have hset : Finset.Icc 1 J = Finset.Ioc 0 J := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hset, ← hsplit]
  exact le_trans (norm_add_le _ _) (add_le_add hrung hgap)

/-- **The generic `progression_sum_bound`.**  Weight transfer plus window gap. -/
theorem progression_sum_bound_generic {L a A J : ℕ} (hL : 0 < L) (haL : a + 1 ≤ L)
    (hA : 2 ≤ A) (hJ1 : 1 ≤ J) (G : ℕ → ℂ) (hG : ∀ j, ‖G j‖ ≤ 1) {R : ℝ}
    (hrung : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖ ≤ R) :
    ‖∑ j ∈ Finset.range (J + 1), ((((L * j + a : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j‖
      ≤ (((a : ℝ) + 1)⁻¹ + 2 / (L : ℝ)) + (L : ℝ)⁻¹ * (R + (1 + Real.log A)) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h1 := inner_harmonic_le_generic hL haL J G hG
  have h2 := window_gap_generic hA hJ1 G hG hrung
  have h3 : (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.Icc 1 J, (((j : ℝ))⁻¹ : ℝ) • G j‖
      ≤ (L : ℝ)⁻¹ * (R + (1 + Real.log A)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

#print axioms inner_harmonic_le_generic
#print axioms window_gap_generic
#print axioms progression_sum_bound_generic

end CastingOut

end NormalNumbers
