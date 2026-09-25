/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowSets

/-!
# Window laws are stable under sparse digit changes

The multi-scale half of C4 (`c4_realizable_of_mem_one` for an `S` whose complement is infinite)
cannot be realized by a single block length: a `blockSeq` of period `q` has an eventually
`q`-periodic abelian set.  The construction therefore builds a sequence `s` as a limit of block
sequences `T n` of growing period, where `T n` is obtained from `T (n+1)` by deleting the
finest layer of gadgets, so `s` and `T n` differ on a set of positions of density `→ 0` as
`n → ∞`.

This file supplies the estimate that makes such a limit legitimate, and it is the *only*
analysis the multi-scale construction needs:

* `card_diffWin_le` — one changed digit spoils at most `L` windows of length `L`;
* `abs_onesFreq_sub_le` — hence
  `|onesFreq s L j N − onesFreq t L j N| ≤ L · diffCount s t (N+L) / N`;
* `tendsto_onesFreq_of_approx` — a 3ε transfer: if for every `ε > 0` some `t` has the window law
  `v` at `(L, j)` and eventual difference density `≤ ε`, then `s` has window law `v` too;
* `tendsto_onesFreq_of_linear_diff` — the packaged form used by the construction, with
  `diffCount s (T n) M ≤ c n + η n · M` and `η n → 0`.

Note both directions are covered at once: the transferred value `v` is *arbitrary*, so the same
lemma proves `IsAbelianAt s L` when `v` is the Binomial weight and refutes it when it is not.
-/

open Finset Filter Topology

namespace NormalNumbers.Abelian

open NormalNumbers.Walsh

/-- The number of positions below `N` at which the two sequences differ. -/
def diffCount (s t : ℕ → ℕ) (N : ℕ) : ℕ := ((range N).filter (fun m => s m ≠ t m)).card

/-- Windows on which the two sequences agree have the same one-count. -/
theorem onesCount_congr (s t : ℕ → ℕ) (L n : ℕ) (h : ∀ i, i < L → s (n + i) = t (n + i)) :
    onesCount s L n = onesCount t L n := by
  unfold onesCount windowSet
  congr 1
  refine Finset.filter_congr (fun i hi => ?_)
  rw [h i (Finset.mem_range.mp hi)]

/-- **One changed digit spoils at most `L` windows.**  The window positions below `N` whose
length-`L` one-count differs are covered by the `L` positions ending at each changed digit. -/
theorem card_diffWin_le (s t : ℕ → ℕ) (L N : ℕ) :
    ((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card
      ≤ L * diffCount s t (N + L) := by
  classical
  have hsub : (range N).filter (fun n => onesCount s L n ≠ onesCount t L n)
      ⊆ ((range (N + L)).filter (fun m => s m ≠ t m)).biUnion
          (fun m => (range L).image (fun i => m - i)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hne⟩ := hn
    have hex : ∃ i, i < L ∧ s (n + i) ≠ t (n + i) := by
      by_contra hc
      push_neg at hc
      exact hne (onesCount_congr s t L n hc)
    obtain ⟨i, hiL, hi⟩ := hex
    refine Finset.mem_biUnion.mpr ⟨n + i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hi⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hiL, by omega⟩
  calc ((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card
      ≤ (((range (N + L)).filter (fun m => s m ≠ t m)).biUnion
          (fun m => (range L).image (fun i => m - i))).card := Finset.card_le_card hsub
    _ ≤ ∑ _m ∈ (range (N + L)).filter (fun m => s m ≠ t m), L := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun m _ => ?_))
        exact (Finset.card_image_le).trans (by simp)
    _ = L * diffCount s t (N + L) := by
        rw [Finset.sum_const, diffCount, smul_eq_mul, Nat.mul_comm]

/-- **The perturbation estimate.**  The length-`L` weight-`j` window frequencies of two sequences
differ by at most `L` times the density of positions where they differ. -/
theorem abs_onesFreq_sub_le (s t : ℕ → ℕ) (L j N : ℕ) :
    |onesFreq s L j N - onesFreq t L j N| ≤ (L * diffCount s t (N + L) : ℝ) / N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [onesFreq]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : ∀ u v : ℕ → ℕ, ((range N).filter (fun n => onesCount u L n = j)).card
      ≤ ((range N).filter (fun n => onesCount v L n = j)).card
        + ((range N).filter (fun n => onesCount u L n ≠ onesCount v L n)).card := by
    intro u v
    refine le_trans (Finset.card_le_card (?_ :
      (range N).filter (fun n => onesCount u L n = j)
        ⊆ ((range N).filter (fun n => onesCount v L n = j))
            ∪ ((range N).filter (fun n => onesCount u L n ≠ onesCount v L n))))
      (Finset.card_union_le _ _)
    intro n hn
    rw [Finset.mem_filter] at hn
    by_cases h : onesCount v L n = j
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn.1, h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn.1, ?_⟩)
      rw [hn.2]
      exact fun hc => h hc.symm
  have hsym : ((range N).filter (fun n => onesCount t L n ≠ onesCount s L n)).card
      = ((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card := by
    congr 1
    refine Finset.filter_congr (fun n _ => ?_)
    exact ⟨fun h hc => h hc.symm, fun h hc => h hc.symm⟩
  have h1 := hAB s t
  have h2 := hAB t s
  rw [hsym] at h2
  have key : |(((range N).filter (fun n => onesCount s L n = j)).card : ℝ)
      - (((range N).filter (fun n => onesCount t L n = j)).card : ℝ)|
      ≤ (((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card : ℝ) := by
    have c1 : (((range N).filter (fun n => onesCount s L n = j)).card : ℝ)
        ≤ (((range N).filter (fun n => onesCount t L n = j)).card : ℝ)
          + (((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card : ℝ) := by
      exact_mod_cast h1
    have c2 : (((range N).filter (fun n => onesCount t L n = j)).card : ℝ)
        ≤ (((range N).filter (fun n => onesCount s L n = j)).card : ℝ)
          + (((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card : ℝ) := by
      exact_mod_cast h2
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hcount : (((range N).filter (fun n => onesCount s L n ≠ onesCount t L n)).card : ℝ)
      ≤ (L * diffCount s t (N + L) : ℝ) := by
    exact_mod_cast card_diffWin_le s t L N
  calc |onesFreq s L j N - onesFreq t L j N|
      = |(((range N).filter (fun n => onesCount s L n = j)).card : ℝ)
          - (((range N).filter (fun n => onesCount t L n = j)).card : ℝ)| / N := by
        rw [onesFreq, onesFreq, div_sub_div_same, abs_div, abs_of_pos hNR]
    _ ≤ (L * diffCount s t (N + L) : ℝ) / N := by
        apply div_le_div_of_nonneg_right (key.trans hcount) hNR.le

/-- **The limit transfer.**  If the window law `v` at `(L, j)` is attained by sequences
arbitrarily close to `s` in difference density, then `s` attains it. -/
theorem tendsto_onesFreq_of_approx (s : ℕ → ℕ) (L j : ℕ) (v : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t : ℕ → ℕ, Tendsto (onesFreq t L j) atTop (𝓝 v) ∧
      ∀ᶠ N in atTop, (L * diffCount s t (N + L) : ℝ) / N ≤ ε) :
    Tendsto (onesFreq s L j) atTop (𝓝 v) := by
  refine Metric.tendsto_nhds.mpr (fun ε hε => ?_)
  obtain ⟨t, htlim, hden⟩ := h (ε / 2) (by positivity)
  have h2 := Metric.tendsto_nhds.mp htlim (ε / 2) (by positivity)
  filter_upwards [hden, h2] with N hN1 hN2
  have hd : |onesFreq s L j N - onesFreq t L j N| ≤ ε / 2 :=
    (abs_onesFreq_sub_le s t L j N).trans hN1
  rw [Real.dist_eq] at hN2 ⊢
  calc |onesFreq s L j N - v|
      ≤ |onesFreq s L j N - onesFreq t L j N| + |onesFreq t L j N - v| := abs_sub_le _ _ _
    _ < ε := by linarith

/-- **The packaged transfer.**  `T n` is an approximating family whose difference from `s` grows
at most linearly with slope `η n → 0`; then `s` inherits the common window law `v`. -/
theorem tendsto_onesFreq_of_linear_diff (s : ℕ → ℕ) (L j : ℕ) (v : ℝ) (T : ℕ → ℕ → ℕ)
    (c η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0))
    (hlim : ∀ n, Tendsto (onesFreq (T n) L j) atTop (𝓝 v))
    (hdiff : ∀ n M, (diffCount s (T n) M : ℝ) ≤ c n + η n * M) :
    Tendsto (onesFreq s L j) atTop (𝓝 v) := by
  refine tendsto_onesFreq_of_approx s L j v (fun ε hε => ?_)
  obtain ⟨n, hn⟩ : ∃ n, (L : ℝ) * η n ≤ ε / 2 := by
    have hmul : Tendsto (fun n => (L : ℝ) * η n) atTop (𝓝 0) := by
      simpa using hηlim.const_mul (L : ℝ)
    have := (hmul.eventually_lt_const (by positivity : (0 : ℝ) < ε / 2)).exists
    obtain ⟨n, hn⟩ := this
    exact ⟨n, hn.le⟩
  refine ⟨T n, hlim n, ?_⟩
  have hbig : Tendsto (fun N : ℕ => ((L : ℝ) * (c n + η n * (N + L))) / N) atTop
      (𝓝 ((L : ℝ) * η n)) := by
    have hrw : ∀ N : ℕ, 0 < N → ((L : ℝ) * (c n + η n * (N + L))) / N
        = ((L : ℝ) * c n) / N + (L : ℝ) * η n + ((L : ℝ) * η n * L) / N := by
      intro N hNpos
      have hNR : (N : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have h0 : Tendsto (fun N : ℕ => ((L : ℝ) * c n) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h1 : Tendsto (fun N : ℕ => ((L : ℝ) * η n * L) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have := (h0.add (tendsto_const_nhds (x := (L : ℝ) * η n) (f := atTop (α := ℕ)))).add h1
    rw [zero_add, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hNpos
    exact (hrw N hNpos).symm
  have hlt : ∀ᶠ N : ℕ in atTop, ((L : ℝ) * (c n + η n * (N + L))) / N < ε :=
    hbig.eventually_lt_const (by linarith)
  filter_upwards [hlt, eventually_gt_atTop 0] with N hN hNpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstep : (L * diffCount s (T n) (N + L) : ℝ) / N
      ≤ ((L : ℝ) * (c n + η n * (N + L))) / N := by
    apply div_le_div_of_nonneg_right _ hNR.le
    have := hdiff n (N + L)
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    push_cast at this ⊢
    nlinarith [this]
  linarith

end NormalNumbers.Abelian
