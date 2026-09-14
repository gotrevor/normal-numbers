/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyStable
import NormalNumbers.DigitInterval

/-!
# Normality is shift-invariant — and the room outside digit-locality

`G4EntropyDensityOne` + `G4EntropyStable` close the *digit-local* world: a satisfiable
hypothesis about the binary digits of `x` at a set `S` of positions implies normality iff `S`
has density one.  The expedition's sample is digit-local because of the quantizer
(`ZSample_eq_blockVal`), so this closes the route — *inside that world*.

This module measures the world outside it, and the answer is stark: the obstruction is
**quantization, not sparsity**.  The *unquantized* orbit point `{2^i x}` at a **single** time `i`
already carries a hypothesis that forces normality, namely "`{2^i x}` is normal".  That works
because `{2^i x}` sees all the digits of `x` from position `i` on, and

  **`isNormalSequence_shift_iff`**: normality of a digit sequence is invariant under shifting.

So the quantized sample at *every* time of a density-`< 1` set forces nothing, while the
unquantized sample at one time forces everything.  The entropy route's gap is exactly the
`m_K`-bit truncation.

The counting is the same style as `G4EntropyStable`: the length-`ℓ` windows of the shifted
sequence below `n` are the windows of the original below `n + r` minus at most `r` of them.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

open NormalNumbers

/-! ### Window counts under a shift -/

variable {s : ℕ → ℕ}

lemma matchesAt_shift (w : List ℕ) (r i : ℕ) :
    MatchesAt (fun j => s (r + j)) w i ↔ MatchesAt s w (r + i) := by
  simp only [MatchesAt, Nat.add_assoc]

/-- The shifted sequence has no more windows below `n` than the original has below `n + r`. -/
lemma countOcc_shift_le (w : List ℕ) (r n : ℕ) :
    countOccurrences w ((List.range n).map (fun j => s (r + j)))
      ≤ countOccurrences w ((List.range (n + r)).map s) := by
  classical
  rw [countOccurrences_range_map, countOccurrences_range_map]
  refine Finset.card_le_card_of_injOn (fun i => r + i) ?_ ?_
  · intro i hi
    obtain ⟨-, hfit, hm⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    show r + i ∈ _
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega, ?_⟩)
    exact (matchesAt_shift w r i).1 hm
  · intro i _ i' _ h
    simp only at h
    omega

/-- Conversely the original has at most `r` windows below `n + r` that the shifted sequence
does not see. -/
lemma countOcc_shift_ge (w : List ℕ) (r n : ℕ) :
    countOccurrences w ((List.range (n + r)).map s)
      ≤ countOccurrences w ((List.range n).map (fun j => s (r + j))) + r := by
  classical
  rw [countOccurrences_range_map, countOccurrences_range_map]
  have hsub : (Finset.range (n + r + 1)).filter
      (fun i => i + w.length ≤ n + r ∧ MatchesAt s w i)
      ⊆ (Finset.range r) ∪ (((Finset.range (n + 1)).filter
          (fun i => i + w.length ≤ n ∧ MatchesAt (fun j => s (r + j)) w i)).image
            (fun i => r + i)) := by
    intro i hi
    obtain ⟨-, hfit, hm⟩ := Finset.mem_filter.1 hi
    by_cases hlt : i < r
    · exact Finset.mem_union_left _ (Finset.mem_range.2 hlt)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨i - r, ?_, by omega⟩)
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega, ?_⟩
      refine (matchesAt_shift w r (i - r)).2 ?_
      rwa [show r + (i - r) = i by omega]
  calc ((Finset.range (n + r + 1)).filter
        (fun i => i + w.length ≤ n + r ∧ MatchesAt s w i)).card
      ≤ ((Finset.range r) ∪ (((Finset.range (n + 1)).filter
          (fun i => i + w.length ≤ n ∧ MatchesAt (fun j => s (r + j)) w i)).image
            (fun i => r + i))).card := Finset.card_le_card hsub
    _ ≤ (Finset.range r).card + (((Finset.range (n + 1)).filter
          (fun i => i + w.length ≤ n ∧ MatchesAt (fun j => s (r + j)) w i)).image
            (fun i => r + i)).card := Finset.card_union_le _ _
    _ ≤ r + ((Finset.range (n + 1)).filter
          (fun i => i + w.length ≤ n ∧ MatchesAt (fun j => s (r + j)) w i)).card := by
        rw [Finset.card_range]
        exact Nat.add_le_add_left (Finset.card_image_le) _
    _ = _ := by omega


/-! ### Normality is shift-invariant -/

private lemma tendsto_add_div_self (r : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + r) / (n : ℝ)) atTop (nhds 1) := by
  have h := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (r : ℝ)
  have h' := h.inv₀ (by norm_num)
  rw [inv_one] at h'
  refine h'.congr fun n => ?_
  rw [inv_div]

private lemma tendsto_const_div_add (r : ℕ) (c : ℝ) :
    Tendsto (fun n : ℕ => c / ((n : ℝ) + r)) atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + r) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.div_atTop tendsto_const_nhds h

/-- **Normality of a digit sequence is invariant under shifting the sequence.** -/
theorem isNormalSequence_shift_iff {b : ℕ} (s : ℕ → ℕ) (r : ℕ) :
    IsNormalSequence b (fun j => s (r + j)) ↔ IsNormalSequence b s := by
  constructor
  · intro h w hw hd
    have hA := h w hw hd
    set v : ℝ := ((b : ℝ) ^ w.length)⁻¹ with hv
    refine (Filter.tendsto_add_atTop_iff_nat r).1 ?_
    have hlow : Tendsto (fun n : ℕ =>
        (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ) / ((n : ℝ) + r))
        atTop (nhds v) := by
      have hmul := hA.mul (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (r : ℝ))
      rw [mul_one] at hmul
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hnr : (n : ℝ) + r ≠ 0 := by positivity
      field_simp
    have hhigh : Tendsto (fun n : ℕ =>
        (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ) / ((n : ℝ) + r)
          + (r : ℝ) / ((n : ℝ) + r)) atTop (nhds v) := by
      have := hlow.add (tendsto_const_div_add r (r : ℝ))
      rwa [add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnr : (0 : ℝ) < (n : ℝ) + r := by positivity
      have hc : (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ)
          ≤ (countOccurrences w ((List.range (n + r)).map s) : ℝ) := by
        exact_mod_cast countOcc_shift_le (s := s) w r n
      push_cast
      gcongr
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnr : (0 : ℝ) < (n : ℝ) + r := by positivity
      have hc : (countOccurrences w ((List.range (n + r)).map s) : ℝ)
          ≤ (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ) + r := by
        exact_mod_cast countOcc_shift_ge (s := s) w r n
      have hsplit : (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ)
            / ((n : ℝ) + r) + (r : ℝ) / ((n : ℝ) + r)
          = ((countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ) + r)
            / ((n : ℝ) + r) := by ring
      rw [hsplit]
      push_cast
      gcongr
  · intro h w hw hd
    have hB := h w hw hd
    set v : ℝ := ((b : ℝ) ^ w.length)⁻¹ with hv
    have hBr : Tendsto (fun n : ℕ =>
        (countOccurrences w ((List.range (n + r)).map s) : ℝ) / (((n + r : ℕ) : ℝ)))
        atTop (nhds v) := (Filter.tendsto_add_atTop_iff_nat r).2 hB
    have hBn : Tendsto (fun n : ℕ =>
        (countOccurrences w ((List.range (n + r)).map s) : ℝ) / (n : ℝ))
        atTop (nhds v) := by
      have hmul := hBr.mul (tendsto_add_div_self r)
      rw [mul_one] at hmul
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hnr : (n : ℝ) + r ≠ 0 := by positivity
      push_cast
      field_simp
    have hlow : Tendsto (fun n : ℕ =>
        (countOccurrences w ((List.range (n + r)).map s) : ℝ) / (n : ℝ)
          - (r : ℝ) / (n : ℝ)) atTop (nhds v) := by
      have := hBn.sub (tendsto_const_div_atTop_nhds_zero_nat (r : ℝ))
      rwa [sub_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hBn ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by positivity
      have hc : (countOccurrences w ((List.range (n + r)).map s) : ℝ) - r
          ≤ (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ) := by
        have := countOcc_shift_ge (s := s) w r n
        have : (countOccurrences w ((List.range (n + r)).map s) : ℝ)
            ≤ (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ) + r := by
          exact_mod_cast this
        linarith
      rw [div_sub_div_same]
      gcongr
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by positivity
      have hc : (countOccurrences w ((List.range n).map (fun j => s (r + j))) : ℝ)
          ≤ (countOccurrences w ((List.range (n + r)).map s) : ℝ) := by
        exact_mod_cast countOcc_shift_le (s := s) w r n
      gcongr


/-! ### The real-number form, and the room outside digit-locality -/

/-- Normality of a real is invariant along its own base-`b` orbit: `{b^i x}` is normal iff `x`
is.  (`digitOf_orbit` says the orbit shifts the digit string; `isNormalSequence_shift_iff` says
normality does not see a shift.) -/
theorem isNormal_orbit_iff {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    IsNormal b (orbit b x i) ↔ IsNormal b x := by
  have hmem : orbit b x i ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hfr : Int.fract (orbit b x i) = orbit b x i := Int.fract_eq_self.2 hmem
  have hx0 : Int.fract x = orbit b x 0 := by
    unfold orbit
    norm_num
  have hdig : digitOf b (Int.fract (orbit b x i))
      = fun j => digitOf b (Int.fract x) (i + j) := by
    funext j
    rw [hfr, digitOf_orbit b hb x hx i j, hx0, digitOf_orbit b hb x hx 0 (i + j),
      Nat.zero_add]
  unfold IsNormal
  rw [hdig, hx0]
  have hshift : (fun j => digitOf b (orbit b x 0) (i + j))
      = fun j => (digitOf b (orbit b x 0)) (i + j) := rfl
  rw [hshift]
  exact isNormalSequence_shift_iff _ i

/-- **The room outside digit-locality: quantization, not sparsity, is the obstruction.**

`G4EntropyDensityOne.forces_normal_iff_density_one` says that a hypothesis reading the binary
*digits* of `x` on a set of density `< 1` can never imply normality.  Here is the contrast: for
**every** time `i`, the single *unquantized* orbit value `{2^i x}` carries a satisfiable
hypothesis that does imply normality — namely "`{2^i x}` is normal".

The expedition's sample is the quantization `⌊2^{m} {4^k x}⌋` of exactly such orbit values
(`ZSample_eq_blockVal`), and it is that `m`-bit truncation — not the sparsity of the times `k` —
that destroys the transfer.  A repair must therefore keep information beyond any fixed number of
digits of the orbit point, not merely sample more times. -/
theorem exists_orbitLocal_forces_normal (i : ℕ) :
    ∃ P : ℝ → Prop,
      (∀ x y : ℝ, orbit 2 x i = orbit 2 y i → P x → P y)
      ∧ (∃ z : ℝ, 0 ≤ z ∧ z < 1 ∧ P z)
      ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) := by
  refine ⟨fun x => IsNormal 2 (orbit 2 x i), ?_, ?_, ?_⟩
  · intro x y heq hP
    rwa [← heq]
  · exact ⟨stoneham23, stoneham23_mem_Ico.1, stoneham23_mem_Ico.2,
      (isNormal_orbit_iff (by norm_num) stoneham23_mem_Ico.1 i).2 isNormal_two_stoneham23⟩
  · intro y hy0 _ hP
    exact (isNormal_orbit_iff (by norm_num) hy0 i).1 hP

end NormalNumbers.G4Entropy


