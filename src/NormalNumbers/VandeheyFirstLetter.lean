/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyTransportB

/-!
# The first emitted letter is the determinant's sign

The one structural fact that makes the emitted RUN count grow linearly:

> **the first letter of a nonempty emitted block is `L` exactly when `det M > 0`.**

Since `det (M · B_j) = − det M` (`det_lrDelta`), the phase alternates at every ingested digit,
so consecutive nonempty blocks START with opposite letters.  Hence over any two consecutive
steps there is at least one alternation: either the first block already alternates internally,
or it is constant, and then its last letter is its first letter — the opposite of the next
block's first letter, so the seam alternates.

    `altOut sᵢ jᵢ + altOut sᵢ₊₁ jᵢ₊₁ ≥ 1`

which is exactly the lower bound `outLenLimit_pos` needs, at window length 2 instead of 1.

The proof of the headline fact is short: `M · B_j = lrProd w · M'` with `M'` nonnegative, so if
`w` starts with `L = [[1,0],[1,1]]` then row 2 of `M · B_j` dominates row 1; reading off the
first column, `M.b ≤ M.d`, which excludes the balance branch `a < c, d < b`.  And a balanced
matrix has `det > 0` exactly on the other branch (`det_pos_iff_branch`).
-/

namespace NormalNumbers

namespace Mat2

/-- **The balance branch IS the determinant's sign.** -/
lemma det_pos_iff_branch {M : Mat2} (h : Balanced M) :
    0 < M.det ↔ (M.c < M.a ∧ M.b < M.d) := by
  obtain ⟨⟨ha, hb, hc, hd⟩, hbr⟩ := h
  constructor
  · intro hpos
    rcases hbr with h1 | h2
    · exact h1
    · exfalso
      rw [det] at hpos
      nlinarith [h2.1, h2.2]
  · intro h1
    rw [det]
    nlinarith [h1.1, h1.2]

end Mat2

namespace VandeheyLR

open Mat2 VandeheyOut

variable {D : ℕ}

/-- **The first emitted letter is determined by the phase.**  `L` iff the determinant is
positive. -/
theorem head_lrOut_eq_true_iff (hD : 0 < D) (M : RState D) (j : ℕ) {b : Bool}
    {rest : List Bool} (h : lrOut hD M j = b :: rest) :
    b = true ↔ 0 < M.val.det := by
  have hspec := lrStep_spec hD M j
  rw [h] at hspec
  set M' := (lrDelta hD M j).val with hM'
  have hM'nn : Nonneg M' := (lrDelta hD M j).2.2.1
  set X := lrProd rest * M' with hX
  have hXnn : Nonneg X := nonneg_lrProd_mul hM'nn
  have hb : (M.val * B j).a = M.val.b := by simp [mul_def, mul, B]
  have hd : (M.val * B j).c = M.val.d := by simp [mul_def, mul, B]
  have hbal := M.2.2
  cases b with
  | true =>
    have hfac : M.val * B j = lrL * X := by
      rw [hspec, lrProd_cons_true, mul_assoc']
    have h1 : M.val.b = X.a := by rw [← hb, hfac]; simp [mul_def, mul, lrL]
    have h2 : M.val.d = X.a + X.c := by rw [← hd, hfac]; simp [mul_def, mul, lrL]
    have hle : M.val.b ≤ M.val.d := by
      have := hXnn.2.2.1
      omega
    have hbr : M.val.c < M.val.a ∧ M.val.b < M.val.d := by
      rcases hbal.2 with h3 | h3
      · exact h3
      · exact absurd h3.2 (by omega)
    simp only [true_iff]
    exact (Mat2.det_pos_iff_branch hbal).mpr hbr
  | false =>
    have hfac : M.val * B j = lrR * X := by
      rw [hspec, lrProd_cons_false, mul_assoc']
    have h1 : M.val.b = X.a + X.c := by rw [← hb, hfac]; simp [mul_def, mul, lrR]
    have h2 : M.val.d = X.c := by rw [← hd, hfac]; simp [mul_def, mul, lrR]
    have hle : M.val.d ≤ M.val.b := by
      have := hXnn.1
      omega
    have hnbr : ¬ (M.val.c < M.val.a ∧ M.val.b < M.val.d) := by
      rintro ⟨-, h4⟩
      omega
    exact ⟨fun hcon => absurd hcon (by simp),
      fun hpos => absurd ((Mat2.det_pos_iff_branch hbal).mp hpos) hnbr⟩

/-! ## Blocks are nonempty for large digits -/

/-- For `j ≥ D` the emitted block is nonempty: `M · B_j` cannot already be balanced, because
the row comparison it would need is broken by `j` once `j` exceeds the entry bound `D`. -/
theorem lrOut_ne_nil_of_le (hD : 0 < D) (M : RState D) {j : ℕ} (hj : D ≤ j) :
    lrOut hD M j ≠ [] := by
  intro hnil
  have hspec := lrStep_spec hD M j
  rw [hnil] at hspec
  have hbal : Balanced (M.val * B j) := by
    rw [hspec, lrProd]
    simpa using (lrDelta hD M j).2.2
  obtain ⟨ha0, haD, hb0, hbD, hc0, hcD, hd0, hdD⟩ := raneyEntry_le M.2
  have hja : (D : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have ea : (M.val * B j).a = M.val.b := by simp [mul_def, mul, B]
  have eb : (M.val * B j).b = M.val.a + M.val.b * (j : ℤ) := by simp [mul_def, mul, B]
  have ec : (M.val * B j).c = M.val.d := by simp [mul_def, mul, B]
  have ed : (M.val * B j).d = M.val.c + M.val.d * (j : ℤ) := by simp [mul_def, mul, B]
  rcases hbal.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ea, ec] at h1
    rw [eb, ed] at h2
    nlinarith
  · rw [ea, ec] at h1
    rw [eb, ed] at h2
    nlinarith

/-! ## Two consecutive steps always alternate -/

variable {α : Type*} [DecidableEq α]

lemma numAlt_le_cons (b : α) : ∀ w : List α, numAlt w ≤ numAlt (b :: w)
  | [] => by simp
  | (c :: w) => by rw [numAlt]; omega

/-- A word with no alternation is constant, so it ends where it starts. -/
lemma getLast?_of_numAlt_eq_zero : ∀ (c : α) (w : List α), numAlt (c :: w) = 0 →
    (c :: w).getLast? = some c
  | c, [], _ => rfl
  | c, (e :: w), h => by
      rw [numAlt] at h
      have hce : c = e := by
        by_contra hne
        rw [if_neg hne] at h
        omega
      have h0 : numAlt (e :: w) = 0 := by
        rw [if_pos hce] at h
        omega
      rw [List.getLast?_cons_of_ne_nil (by simp), getLast?_of_numAlt_eq_zero e w h0, hce]

/-- **The two-step alternation bound.**  Consecutive nonempty blocks start with opposite
letters (`head_lrOut_eq_true_iff` + `det_lrDelta`), so either the first block alternates
internally or the seam does. -/
theorem one_le_altOut_add (hD : 0 < D) (s : RState D × Bool) {j₁ j₂ : ℕ}
    (h₁ : lrOut hD s.1 j₁ ≠ []) (h₂ : lrOut hD (lrDelta hD s.1 j₁) j₂ ≠ []) :
    1 ≤ altOut hD s j₁ + altOut hD (lrB hD s j₁) j₂ := by
  obtain ⟨c, u, hu⟩ : ∃ c u, lrOut hD s.1 j₁ = c :: u := by
    cases hcases : lrOut hD s.1 j₁ with
    | nil => exact absurd hcases h₁
    | cons c u => exact ⟨c, u, rfl⟩
  obtain ⟨e, v, hv⟩ : ∃ e v, lrOut hD (lrDelta hD s.1 j₁) j₂ = e :: v := by
    cases hcases : lrOut hD (lrDelta hD s.1 j₁) j₂ with
    | nil => exact absurd hcases h₂
    | cons e v => exact ⟨e, v, rfl⟩
  -- the two heads are opposite, because the determinant flips
  have hdet : (lrDelta hD s.1 j₁).val.det = - s.1.val.det := det_lrDelta hD s.1 j₁
  have hD0 : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
  have hne : c ≠ e := by
    have hc := head_lrOut_eq_true_iff hD s.1 j₁ hu
    have he := head_lrOut_eq_true_iff hD (lrDelta hD s.1 j₁) j₂ hv
    rcases s.1.2.1 with hd | hd <;> cases c <;> cases e <;>
      simp_all <;> omega
  by_cases hconst : numAlt (lrOut hD s.1 j₁) = 0
  · -- constant first block: the SEAM alternates
    have hlast : (lrOut hD s.1 j₁).getLast? = some c := by
      rw [hu] at hconst ⊢
      exact getLast?_of_numAlt_eq_zero c u hconst
    have hb : (lrB hD s j₁).2 = c := by
      show (((lrOut hD s.1 j₁).getLast?).getD s.2) = c
      rw [hlast]; rfl
    have : 1 ≤ altOut hD (lrB hD s j₁) j₂ := by
      show 1 ≤ numAlt ((lrB hD s j₁).2 :: lrOut hD (lrB hD s j₁).1 j₂)
      have hfst : (lrB hD s j₁).1 = lrDelta hD s.1 j₁ := rfl
      rw [hb, hfst, hv, numAlt, if_neg hne]
      omega
    omega
  · have : 1 ≤ altOut hD s j₁ := by
      have := numAlt_le_cons s.2 (lrOut hD s.1 j₁)
      show 1 ≤ numAlt (s.2 :: lrOut hD s.1 j₁)
      omega
    omega

/-! ## `hc`: the run rate is positive -/

open Filter VandeheyAut

lemma stateAt_lrB_succ (hD : 0 < D) (s₀ : RState D × Bool) (x : ℝ) (i : ℕ) :
    stateAt (lrB hD) s₀ x (i + 1) = lrB hD (stateAt (lrB hD) s₀ x i) (cfDigit x i) := by
  rw [stateAt, stateAt, cfWord_succ'', runState_append]
  simp [runState]

lemma cfWindow_two (x : ℝ) (i : ℕ) : cfWindow x i 2 = [cfDigit x i, cfDigit x (i + 1)] := by
  have h := cfWindow_succ x i 1
  rw [cfWindow_one] at h
  simpa using h

/-- **The counting step.**  Every position whose 2-digit window is `[D, D]` forces an
alternation in its own step or the next, and each step is charged at most twice. -/
theorem winCard_le_two_mul_numAlt (hD : 0 < D) (s₀ : RPlus D × Bool) (x : ℝ) (n : ℕ) :
    VandeheyOut.winCard [D, D] x n
      ≤ 2 * numAlt (s₀.2 :: lrWord hD s₀.1.toRState x (n + 1)) := by
  classical
  set f : ℕ → ℕ := fun k =>
    altOut hD (stateAt (lrB hD) (toRStateB s₀) x k) (cfDigit x k) with hf
  set W : Finset ℕ := (Finset.range n).filter (fun i => ([D, D] : List ℕ) = cfWindow x i 2)
    with hW
  have hkey : ∀ i ∈ W, 1 ≤ f i + f (i + 1) := by
    intro i hi
    rw [hW, Finset.mem_filter] at hi
    have hwin : ([D, D] : List ℕ) = [cfDigit x i, cfDigit x (i + 1)] := by
      rw [hi.2, cfWindow_two]
    have hd1 : cfDigit x i = D := by
      have := congrArg (fun l => l.headI) hwin
      simpa using this.symm
    have hd2 : cfDigit x (i + 1) = D := by
      have := congrArg (fun l => (l.tail).headI) hwin
      simpa using this.symm
    set s := stateAt (lrB hD) (toRStateB s₀) x i with hs
    have h1 : lrOut hD s.1 (cfDigit x i) ≠ [] := by
      rw [hd1]; exact lrOut_ne_nil_of_le hD s.1 le_rfl
    have h2 : lrOut hD (lrDelta hD s.1 (cfDigit x i)) (cfDigit x (i + 1)) ≠ [] := by
      rw [hd2]; exact lrOut_ne_nil_of_le hD _ le_rfl
    have hstep : stateAt (lrB hD) (toRStateB s₀) x (i + 1) = lrB hD s (cfDigit x i) :=
      stateAt_lrB_succ hD (toRStateB s₀) x i
    rw [hf]
    simp only
    rw [hstep]
    exact one_le_altOut_add hD s h1 h2
  have hcard : W.card ≤ ∑ i ∈ W, (f i + f (i + 1)) := by
    calc W.card = ∑ _i ∈ W, 1 := by simp
      _ ≤ ∑ i ∈ W, (f i + f (i + 1)) := Finset.sum_le_sum hkey
  have hsplit : ∑ i ∈ W, (f i + f (i + 1)) = (∑ i ∈ W, f i) + ∑ i ∈ W, f (i + 1) :=
    Finset.sum_add_distrib
  have hA : ∑ i ∈ W, f i ≤ ∑ k ∈ Finset.range (n + 1), f k := by
    refine Finset.sum_le_sum_of_subset ?_
    intro i hi
    rw [hW, Finset.mem_filter, Finset.mem_range] at hi
    exact Finset.mem_range.mpr (by omega)
  have hB : ∑ i ∈ W, f (i + 1) ≤ ∑ k ∈ Finset.range (n + 1), f k := by
    have himg : ∑ i ∈ W, f (i + 1) = ∑ k ∈ W.image (· + 1), f k := by
      rw [Finset.sum_image]
      intro a _ b _ h
      simpa using h
    rw [himg]
    refine Finset.sum_le_sum_of_subset ?_
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    rw [hW, Finset.mem_filter, Finset.mem_range] at hi
    exact Finset.mem_range.mpr (by omega)
  have hsum : ∑ k ∈ Finset.range (n + 1), f k
      = numAlt (s₀.2 :: lrWord hD s₀.1.toRState x (n + 1)) :=
    (numAlt_lrWord_eq_sum hD s₀.1.toRState s₀.2 x (n + 1)).symm
  have : VandeheyOut.winCard [D, D] x n = W.card := by
    rw [VandeheyOut.winCard, hW]
    rfl
  rw [this, ← hsum]
  calc W.card ≤ ∑ i ∈ W, (f i + f (i + 1)) := hcard
    _ = (∑ i ∈ W, f i) + ∑ i ∈ W, f (i + 1) := hsplit
    _ ≤ (∑ k ∈ Finset.range (n + 1), f k) + ∑ k ∈ Finset.range (n + 1), f k :=
        Nat.add_le_add hA hB
    _ = 2 * ∑ k ∈ Finset.range (n + 1), f k := by ring

/-- **`hc` for the Raney transducer: the run rate is STRICTLY positive.**  Every position whose
2-digit window is `[D, D]` forces an alternation within two steps, and those positions have
positive Gauss frequency. -/
theorem zero_lt_runRate (D : ℕ) [Fact (Nat.Prime D)] (hD : 0 < D) (s₀ : RPlus D × Bool) :
    0 < ∑ t : RState D × Bool, VandeheyOut.wLimit (rhoLRB hD s₀) t (altWeight hD t) 1 := by
  classical
  set c : ℝ := ∑ t : RState D × Bool, VandeheyOut.wLimit (rhoLRB hD s₀) t (altWeight hD t) 1
    with hc
  obtain ⟨x, hx⟩ := exists_isCFNormal
  set A : ℕ → ℕ := fun n => numAlt (s₀.2 :: lrWord hD s₀.1.toRState x n) with hA
  have hlim : Tendsto (fun n => (A n : ℝ) / n) atTop (nhds c) :=
    tendsto_numAlt_lrWord_div D hD s₀ hx
  -- the shifted sequence has the same limit
  have hshift : Tendsto (fun n : ℕ => (A (n + 1) : ℝ) / n) atTop (nhds c) := by
    have h1 : Tendsto (fun n : ℕ => (A (n + 1) : ℝ) / (n + 1 : ℕ)) atTop (nhds c) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (nhds 1) := by
      have h0 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    have h3 := h1.mul h2
    rw [mul_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    push_cast
    field_simp
  -- the window frequency
  have hwin : Tendsto (fun n => (VandeheyOut.winCard [D, D] x n : ℝ) / n) atTop
      (nhds (gaussMeasure (cfCylinder [D, D])).toReal) := by
    have hne : ([D, D] : List ℕ) ≠ [] := by simp
    have hpos : ∀ a ∈ ([D, D] : List ℕ), 1 ≤ a := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    simpa [VandeheyOut.winCard] using tendsto_windowFreq hx [D, D] hne hpos
  have hle : (gaussMeasure (cfCylinder [D, D])).toReal ≤ 2 * c := by
    refine le_of_tendsto_of_tendsto' hwin (hshift.const_mul 2) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ hn0.le
      have := winCard_le_two_mul_numAlt hD s₀ x n
      exact_mod_cast this
  have hγ : 0 < (gaussMeasure (cfCylinder [D, D])).toReal := by
    refine gaussMeasure_cfCylinder_toReal_pos _ (by simp) ?_
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  linarith

end VandeheyLR

end NormalNumbers

section
#print axioms NormalNumbers.Mat2.det_pos_iff_branch
#print axioms NormalNumbers.VandeheyLR.head_lrOut_eq_true_iff
#print axioms NormalNumbers.VandeheyLR.lrOut_ne_nil_of_le
#print axioms NormalNumbers.VandeheyLR.one_le_altOut_add
#print axioms NormalNumbers.VandeheyLR.winCard_le_two_mul_numAlt
#print axioms NormalNumbers.VandeheyLR.zero_lt_runRate
end
