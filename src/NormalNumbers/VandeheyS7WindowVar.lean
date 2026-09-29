/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WV: the window average at scale `T` concentrates along a CF-normal orbit

The input half of the crux's locality (S7-CK), assembled from S7-PF.  For a CF-normal `y` write

    B m = blockCount (I_w) T (Gᵐ y) / T

for the frequency of `w` in the window of length `T` starting at time `m`.  Expanding the square
turns the Cesàro average of `(B m − γ(I_w))²` into the orbit's PAIR frequencies, which S7-PF bounds
by the pair masses and S7-PC prices as `γ² + 4(9/10)^{gap−|w|}`.  The off-diagonal terms are
summable, so

    limsup (1/p) Σ_{m<p} (B m − γ(I_w))²  ≤  2(|w| + 40)/T ,

and by Cauchy–Schwarz the `L¹` form is `≤ √(2(|w|+40)/T)` — window concentration with an explicit
rate, for every CF-normal input.

## Guard rule

**Content locator.**  `sum_sq_window_le` is where the double sum becomes pair counts (each `(j, j')`
pair is a shifted pair event, absorbed into a count over `p + T` times); the analytic content is
entirely S7-PC's geometric decay, which enters through `sum_pairBound_le`.

**Degenerate cases.**  `T = 0` makes `B m = 0/0 = 0` and the bound trivial; the statement is for
`0 < T`.  `w = []` has `γ = 1` and every window average is `1`, so the variance is `0` and the
bound is slack.
-/
import NormalNumbers.VandeheyS7PairFreq

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers Finset

/-- The error term of the pair bound at gap `g`: trivial below `|w|`, geometric above. -/
noncomputable def pairErr (w : List ℕ) (g : ℕ) : ℝ :=
  if g < w.length then 1 else 4 * (9 / 10 : ℝ) ^ (g - w.length)

lemma pairErr_nonneg (w : List ℕ) (g : ℕ) : 0 ≤ pairErr w g := by
  rw [pairErr]
  split <;> positivity

/-- **The pair bound, uniformly in the gap.**  Eventually, every gap's pair count is at most
`(γ² + pairErr + ε)·p`. -/
theorem blockCount_pairSet_le_err {w : List ℕ} (hw : w ≠ []) (hwpos : ∀ a ∈ w, 1 ≤ a)
    {y : ℝ} (hy : IsCFNormal y) (hyorb : ∀ k : ℕ, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1)
    (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (pairSet w g) p y
        ≤ ((gaussMeasure (cfCylinder w)).toReal ^ 2 + pairErr w g + ε) * (p : ℝ) := by
  by_cases hg : g < w.length
  · -- the trivial branch: the count is at most `p`, and `pairErr = 1`
    filter_upwards [eventually_gt_atTop 0] with p hp0
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hle : blockCount (pairSet w g) p y ≤ (p : ℝ) := by
      refine le_trans (blockCount_mono (fun z hz => hz.1) p y) ?_
      exact blockCount_le_card _ _ _
    have hγ : (0:ℝ) ≤ (gaussMeasure (cfCylinder w)).toReal ^ 2 := by positivity
    have herr : pairErr w g = 1 := by rw [pairErr, if_pos hg]
    rw [herr]
    nlinarith
  · -- the geometric branch
    push_neg at hg
    obtain ⟨h, rfl⟩ : ∃ h, g = w.length + h := ⟨g - w.length, by omega⟩
    have herr : pairErr w (w.length + h) = 4 * (9 / 10 : ℝ) ^ h := by
      rw [pairErr, if_neg (by omega), Nat.add_sub_cancel_left]
    rw [herr]
    exact blockCount_pairSet_le_sq hw hwpos hy hyorb h hε

/-- The total error over all gaps in a window: `Σ_{g<T} pairErr ≤ |w| + 40`. -/
theorem sum_pairErr_le (w : List ℕ) (T : ℕ) :
    ∑ g ∈ range T, pairErr w g ≤ (w.length : ℝ) + 40 := by
  classical
  have hsplit : ∑ g ∈ range T, pairErr w g
      = (∑ g ∈ (range T).filter (fun g => g < w.length), pairErr w g)
        + ∑ g ∈ (range T).filter (fun g => ¬ g < w.length), pairErr w g :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  have hlow : ∑ g ∈ (range T).filter (fun g => g < w.length), pairErr w g ≤ (w.length : ℝ) := by
    have hterm : ∀ g ∈ (range T).filter (fun g => g < w.length), pairErr w g = 1 := by
      intro g hg
      rw [pairErr, if_pos (Finset.mem_filter.1 hg).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((range T).filter (fun g => g < w.length)).card ≤ w.length := by
      have hsub : (range T).filter (fun g => g < w.length) ⊆ range w.length := by
        intro g hg
        exact Finset.mem_range.2 (Finset.mem_filter.1 hg).2
      simpa using Finset.card_le_card hsub
    exact_mod_cast hcard
  have hhigh : ∑ g ∈ (range T).filter (fun g => ¬ g < w.length), pairErr w g ≤ 40 := by
    have hterm : ∀ g ∈ (range T).filter (fun g => ¬ g < w.length),
        pairErr w g = 4 * (9 / 10 : ℝ) ^ (g - w.length) := by
      intro g hg
      rw [pairErr, if_neg (Finset.mem_filter.1 hg).2]
    rw [Finset.sum_congr rfl hterm]
    -- reindex by the gap above `|w|` and sum the geometric series
    have hinj : ∀ a ∈ (range T).filter (fun g => ¬ g < w.length),
        ∀ b ∈ (range T).filter (fun g => ¬ g < w.length), a - w.length = b - w.length → a = b := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.1 ha).2
      have hb' := (Finset.mem_filter.1 hb).2
      omega
    have himg : ∑ g ∈ (range T).filter (fun g => ¬ g < w.length),
        4 * (9 / 10 : ℝ) ^ (g - w.length)
        = ∑ h ∈ ((range T).filter (fun g => ¬ g < w.length)).image (fun g => g - w.length),
            4 * (9 / 10 : ℝ) ^ h :=
      (Finset.sum_image (f := fun h : ℕ => 4 * (9 / 10 : ℝ) ^ h) hinj).symm
    rw [himg]
    have hsub : ((range T).filter (fun g => ¬ g < w.length)).image (fun g => g - w.length)
        ⊆ range T := by
      intro h hh
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      exact Finset.mem_range.2 (by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hg).1
        omega)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => by positivity)) ?_
    have hgeom : ∑ h ∈ range T, (9 / 10 : ℝ) ^ h ≤ 10 := by
      have heq : ∑ h ∈ range T, (9 / 10 : ℝ) ^ h
          = ((9 / 10 : ℝ) ^ T - 1) / ((9 / 10 : ℝ) - 1) := geom_sum_eq (by norm_num) T
      have hpow0 : (0:ℝ) ≤ (9 / 10 : ℝ) ^ T := by positivity
      have hpow1 : (9 / 10 : ℝ) ^ T ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hval : ((9 / 10 : ℝ) ^ T - 1) / ((9 / 10 : ℝ) - 1)
          = (1 - (9 / 10 : ℝ) ^ T) * 10 := by
        field_simp
        ring
      rw [heq, hval]
      nlinarith
    calc ∑ h ∈ range T, 4 * (9 / 10 : ℝ) ^ h = 4 * ∑ h ∈ range T, (9 / 10 : ℝ) ^ h := by
          rw [Finset.mul_sum]
      _ ≤ 4 * 10 := by linarith
      _ = 40 := by norm_num
  linarith

/-! ## The double sum -/

/-- One `(j, j')` term of the expanded square is a shifted pair count. -/
theorem sum_pair_shift_le (w : List ℕ) (y : ℝ) (p T j j' : ℕ) (hj : j ≤ j') (hj' : j' < T) :
    ∑ m ∈ range p, blockIndic (cfCylinder w) (gaussMap^[m + j] y)
        * blockIndic (cfCylinder w) (gaussMap^[m + j'] y)
      ≤ blockCount (pairSet w (j' - j)) (p + T) y := by
  classical
  have hterm : ∀ m ∈ range p,
      blockIndic (cfCylinder w) (gaussMap^[m + j] y)
          * blockIndic (cfCylinder w) (gaussMap^[m + j'] y)
        = blockIndic (pairSet w (j' - j)) (gaussMap^[m + j] y) := by
    intro m _
    by_cases h1 : gaussMap^[m + j] y ∈ cfCylinder w
    · by_cases h2 : gaussMap^[m + j'] y ∈ cfCylinder w
      · have hmem : gaussMap^[m + j] y ∈ pairSet w (j' - j) := by
          refine ⟨h1, ?_⟩
          have : gaussMap^[j' - j] (gaussMap^[m + j] y) = gaussMap^[m + j'] y := by
            rw [← Function.iterate_add_apply]
            congr 1
            omega
          rw [Set.mem_preimage, this]
          exact h2
        rw [blockIndic_eq_one' h1, blockIndic_eq_one' h2, blockIndic_eq_one' hmem, mul_one]
      · have hnot : gaussMap^[m + j] y ∉ pairSet w (j' - j) := by
          intro hmem
          refine h2 ?_
          have hiter : gaussMap^[j' - j] (gaussMap^[m + j] y) = gaussMap^[m + j'] y := by
            rw [← Function.iterate_add_apply]
            congr 1
            omega
          have := hmem.2
          rw [Set.mem_preimage, hiter] at this
          exact this
        rw [blockIndic_eq_zero' h2, blockIndic_eq_zero' hnot, mul_zero]
    · have hnot : gaussMap^[m + j] y ∉ pairSet w (j' - j) := fun hmem => h1 hmem.1
      rw [blockIndic_eq_zero' h1, blockIndic_eq_zero' hnot, zero_mul]
  rw [Finset.sum_congr rfl hterm, blockCount_apply]
  -- the shifted window sits inside `range (p + T)`
  have hsub : (range p).image (fun m => m + j) ⊆ range (p + T) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.mem_range.2 (by
      have := Finset.mem_range.1 hm
      omega)
  have hinj : ∀ a ∈ range p, ∀ b ∈ range p, a + j = b + j → a = b := by
    intro a _ b _ h; omega
  have himg : ∑ m ∈ range p, blockIndic (pairSet w (j' - j)) (gaussMap^[m + j] y)
      = ∑ n ∈ (range p).image (fun m => m + j),
          blockIndic (pairSet w (j' - j)) (gaussMap^[n] y) :=
    (Finset.sum_image (f := fun n => blockIndic (pairSet w (j' - j)) (gaussMap^[n] y)) hinj).symm
  rw [himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => blockIndic_nonneg _ _)

/-- **The expanded square, as pair counts.** -/
theorem sum_sq_window_le (w : List ℕ) (y : ℝ) (p T : ℕ) :
    ∑ m ∈ range p, (blockCount (cfCylinder w) T (gaussMap^[m] y)) ^ 2
      ≤ ∑ j ∈ range T, ∑ j' ∈ range T,
          blockCount (pairSet w (max j j' - min j j')) (p + T) y := by
  classical
  have hexp : ∀ m : ℕ, (blockCount (cfCylinder w) T (gaussMap^[m] y)) ^ 2
      = ∑ j ∈ range T, ∑ j' ∈ range T,
          blockIndic (cfCylinder w) (gaussMap^[m + j] y)
            * blockIndic (cfCylinder w) (gaussMap^[m + j'] y) := by
    intro m
    have hshift : ∀ j : ℕ, blockIndic (cfCylinder w) (gaussMap^[j] (gaussMap^[m] y))
        = blockIndic (cfCylinder w) (gaussMap^[m + j] y) := by
      intro j
      rw [← Function.iterate_add_apply, Nat.add_comm]
    rw [blockCount_apply, pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
      rw [hshift j, hshift j']
  rw [Finset.sum_congr rfl (fun m _ => hexp m)]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjT : j < T := Finset.mem_range.1 hj
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j' hj' => ?_
  have hj'T : j' < T := Finset.mem_range.1 hj'
  rcases le_total j j' with h | h
  · have hmm : max j j' - min j j' = j' - j := by
      rw [max_eq_right h, min_eq_left h]
    rw [hmm]
    exact sum_pair_shift_le w y p T j j' h hj'T
  · have hmm : max j j' - min j j' = j - j' := by
      rw [max_eq_left h, min_eq_right h]
    rw [hmm]
    have hswap : ∀ m : ℕ, blockIndic (cfCylinder w) (gaussMap^[m + j] y)
        * blockIndic (cfCylinder w) (gaussMap^[m + j'] y)
        = blockIndic (cfCylinder w) (gaussMap^[m + j'] y)
          * blockIndic (cfCylinder w) (gaussMap^[m + j] y) := fun m => by ring
    rw [Finset.sum_congr rfl (fun m _ => hswap m)]
    exact sum_pair_shift_le w y p T j' j h hjT

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.blockCount_pairSet_le_err
#print axioms NormalNumbers.VandeheyS7.sum_pairErr_le
#print axioms NormalNumbers.VandeheyS7.sum_pair_shift_le
#print axioms NormalNumbers.VandeheyS7.sum_sq_window_le

end Audit
