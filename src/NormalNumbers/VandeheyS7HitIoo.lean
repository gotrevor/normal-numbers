/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7HitCell

/-!
# S7-HI: the per-window interval hit bound

The assembly of laps 51–54, for one window.  For a CF-normal `x`, a window cylinder `I_v` and a
target interval `(a,b) ⊆ [0,1]`, the frequency of the times at which the orbit is in `I_v` and,
`|v|` steps later, in `(a,b)`, is at most

    (1 + 8 log 2) · ((b − a)/log 2 + δ) · γ(I_v) + δ .

Three inputs: `cellCover_inv_log_two` covers the interval by cells with total mass
`≤ (b−a)/log 2 + δ` and misses no irrational; `mem_cellSet_append_iff` turns each covering cell
into the cell `v ++ c`, whose frequency `blockCount_freq_cellSet_mass` pins; and
`gaussMeasure_cellSet_append_le` bounds each such cell's mass by `(1+8log2) γ(I_v) γ(cellSet c)`.

The `γ(I_v)` factor is the point: summing over a same-length window family costs nothing
(`sum_gaussMeasure_le_one_of_length`), so the constant stays absolute however many windows the
predictor distinguishes.

## Guard rule

Content locator: at `v = [1]` and `(a,b) = (0,1)` the bound is `≈ 9.0 · γ(I_1)`, i.e. not vacuous
but not sharp — the constant is absolute, which is all the crux needs.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The per-window interval hit bound.** -/
theorem blockCount_hit_Ioo_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) (v : List ℕ) (hv : v ≠ []) (hvpos : ∀ e ∈ v, 1 ≤ e)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop,
      blockCount (cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (Set.Ioo a b)) p x / (p:ℝ)
        ≤ (1 + 8 * Real.log 2) * ((b - a) / Real.log 2 + δ) *
            (gaussMeasure (cfCylinder v)).toReal + δ := by
  classical
  obtain ⟨F, hFpos, hFcov, hFmass⟩ := cellCover_inv_log_two a b ha hab hb δ hδ
  set X : Set ℝ := cfCylinder v ∩ (gaussMap^[v.length]) ⁻¹' (Set.Ioo a b) with hX
  -- pointwise domination by the covering cells
  have hpt : ∀ n : ℕ, blockIndic X (gaussMap^[n] x)
      ≤ ∑ c ∈ F, blockIndic (cellSet (v ++ c.1) c.2) (gaussMap^[n] x) := by
    intro n
    by_cases hn : gaussMap^[n] x ∈ X
    · obtain ⟨hirr', hmem'⟩ := irrational_orbit x hirr hmem n
      obtain ⟨hvmem, hIoo⟩ := id hn
      have hshift := irrational_orbit (gaussMap^[n] x) hirr' hmem' v.length
      obtain ⟨c, hcF, hc⟩ := hFcov (gaussMap^[v.length] (gaussMap^[n] x)) hshift.1 hshift.2
        (by simpa using hIoo)
      have hin : gaussMap^[n] x ∈ cellSet (v ++ c.1) c.2 :=
        (mem_cellSet_append_iff hirr' hmem' v c.1 c.2).2 ⟨hvmem, hc⟩
      have hone : blockIndic X (gaussMap^[n] x) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hn]; rfl
      rw [hone]
      have hterm : blockIndic (cellSet (v ++ c.1) c.2) (gaussMap^[n] x) = 1 := by
        rw [blockIndic, Set.indicator_of_mem hin]; rfl
      calc (1:ℝ) = blockIndic (cellSet (v ++ c.1) c.2) (gaussMap^[n] x) := hterm.symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun c : List ℕ × ℕ => blockIndic (cellSet (v ++ c.1) c.2) (gaussMap^[n] x))
            (fun i _ => blockIndic_nonneg _ _) hcF
    · rw [blockIndic, Set.indicator_of_notMem hn]
      exact Finset.sum_nonneg fun i _ => blockIndic_nonneg _ _
  have hcount : ∀ p : ℕ, blockCount X p x ≤ ∑ c ∈ F, blockCount (cellSet (v ++ c.1) c.2) p x := by
    intro p
    simp only [blockCount_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun n _ => hpt n
  -- the covering cells' frequencies
  have hfreq : ∀ c ∈ F, Tendsto (fun p => blockCount (cellSet (v ++ c.1) c.2) p x / (p:ℝ)) atTop
      (nhds (gaussMeasure (cellSet (v ++ c.1) c.2)).toReal) := by
    intro c hc
    refine blockCount_freq_cellSet_mass hirr hmem hx _ (by simp [hv]) ?_ (hFpos c hc).2
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact hvpos e h
    · exact (hFpos c hc).1 e h
  have hsum := tendsto_finsetSum F (fun c hc => hfreq c hc)
  -- the covering cells' masses
  have hmass : (∑ c ∈ F, (gaussMeasure (cellSet (v ++ c.1) c.2)).toReal)
      ≤ (1 + 8 * Real.log 2) * ((b - a) / Real.log 2 + δ) *
          (gaussMeasure (cfCylinder v)).toReal := by
    have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hgv : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have hstep : ∀ c ∈ F, (gaussMeasure (cellSet (v ++ c.1) c.2)).toReal
        ≤ (1 + 8 * Real.log 2) * (gaussMeasure (cfCylinder v)).toReal *
            (gaussMeasure (cellSet c.1 c.2)).toReal := by
      intro c hc
      have h := gaussMeasure_cellSet_append_le v c.1 hvpos c.2
      linarith [h]
    calc (∑ c ∈ F, (gaussMeasure (cellSet (v ++ c.1) c.2)).toReal)
        ≤ ∑ c ∈ F, (1 + 8 * Real.log 2) * (gaussMeasure (cfCylinder v)).toReal *
            (gaussMeasure (cellSet c.1 c.2)).toReal := Finset.sum_le_sum hstep
      _ = (1 + 8 * Real.log 2) * (gaussMeasure (cfCylinder v)).toReal *
            ∑ c ∈ F, (gaussMeasure (cellSet c.1 c.2)).toReal := by rw [Finset.mul_sum]
      _ ≤ (1 + 8 * Real.log 2) * (gaussMeasure (cfCylinder v)).toReal *
            ((b - a) / Real.log 2 + δ) := by
          have hc0 : (0:ℝ) ≤ (1 + 8 * Real.log 2) * (gaussMeasure (cfCylinder v)).toReal := by
            positivity
          refine mul_le_mul_of_nonneg_left ?_ hc0
          simpa [one_div, div_eq_inv_mul] using hFmass
      _ = _ := by ring
  -- combine
  have hlim := hsum.eventually (eventually_lt_nhds
    (show (∑ c ∈ F, (gaussMeasure (cellSet (v ++ c.1) c.2)).toReal) <
      (∑ c ∈ F, (gaussMeasure (cellSet (v ++ c.1) c.2)).toReal) + δ by linarith))
  filter_upwards [hlim, eventually_gt_atTop 0] with p hp hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  have hdiv : blockCount X p x / (p:ℝ)
      ≤ (∑ c ∈ F, blockCount (cellSet (v ++ c.1) c.2) p x) / (p:ℝ) := by
    gcongr
    exact hcount p
  have hrw : (∑ c ∈ F, blockCount (cellSet (v ++ c.1) c.2) p x) / (p:ℝ)
      = ∑ c ∈ F, blockCount (cellSet (v ++ c.1) c.2) p x / (p:ℝ) := by
    rw [Finset.sum_div]
  rw [hrw] at hdiv
  linarith

/-- **The window-hit theorem for interval targets.**  Summing the per-window bound over a
same-length window family costs nothing: the constant `(1 + 8 log 2)/log 2` is absolute, and in
particular independent of the window length `k` and of the number of windows. -/
theorem windowHit_Ioo_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {k : ℕ} (V : Finset (List ℕ))
    (hVlen : ∀ v ∈ V, v.length = k) (hVne : ∀ v ∈ V, v ≠ [])
    (hVpos : ∀ v ∈ V, ∀ e ∈ v, 1 ≤ e) (A B : List ℕ → ℝ)
    (hA : ∀ v ∈ V, 0 ≤ A v ∧ A v ≤ B v ∧ B v ≤ 1)
    {L : ℝ} (hL : ∀ v ∈ V, B v - A v ≤ L) (hL0 : 0 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      (∑ v ∈ V, blockCount (cfCylinder v ∩ (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p x) / (p:ℝ)
        ≤ (1 + 8 * Real.log 2) * (L / Real.log 2) + ε := by
  classical
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (0:ℝ) < 1 + 8 * Real.log 2 := by positivity
  set N : ℝ := (V.card : ℝ) with hN
  have hN0 : (0:ℝ) ≤ N := by positivity
  set δ : ℝ := min (ε / (2 * (1 + 8 * Real.log 2))) (ε / (2 * (N + 1))) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : (1 + 8 * Real.log 2) * δ ≤ ε / 2 := by
    have h := min_le_left (ε / (2 * (1 + 8 * Real.log 2))) (ε / (2 * (N + 1)))
    rw [← hδdef] at h
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (1 + 8 * Real.log 2))] at h
    nlinarith
  have hδ2 : N * δ ≤ ε / 2 := by
    have h := min_le_right (ε / (2 * (1 + 8 * Real.log 2))) (ε / (2 * (N + 1)))
    rw [← hδdef] at h
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (N + 1))] at h
    nlinarith
  have hper : ∀ v ∈ V, ∀ᶠ p : ℕ in atTop,
      blockCount (cfCylinder v ∩ (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p x / (p:ℝ)
        ≤ (1 + 8 * Real.log 2) * ((B v - A v) / Real.log 2 + δ) *
            (gaussMeasure (cfCylinder v)).toReal + δ := by
    intro v hv
    obtain ⟨ha, hab, hb⟩ := hA v hv
    have h := blockCount_hit_Ioo_le hirr hmem hx v (hVne v hv) (hVpos v hv) ha hab hb hδ
    rw [hVlen v hv] at h
    exact h
  filter_upwards [(eventually_all_finset V).2 hper, eventually_gt_atTop 0] with p hp hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  have hsplit : (∑ v ∈ V,
      blockCount (cfCylinder v ∩ (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p x) / (p:ℝ)
      = ∑ v ∈ V,
        blockCount (cfCylinder v ∩ (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p x / (p:ℝ) := by
    rw [Finset.sum_div]
  rw [hsplit]
  have hbound : ∑ v ∈ V,
      blockCount (cfCylinder v ∩ (gaussMap^[k]) ⁻¹' (Set.Ioo (A v) (B v))) p x / (p:ℝ)
      ≤ ∑ v ∈ V, ((1 + 8 * Real.log 2) * (L / Real.log 2 + δ) *
          (gaussMeasure (cfCylinder v)).toReal + δ) := by
    refine Finset.sum_le_sum fun v hv => ?_
    refine (hp v hv).trans ?_
    have hgv : (0:ℝ) ≤ (gaussMeasure (cfCylinder v)).toReal := ENNReal.toReal_nonneg
    have hmono : (B v - A v) / Real.log 2 + δ ≤ L / Real.log 2 + δ := by
      have := hL v hv
      gcongr
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmono hK.le) hgv
    linarith
  refine hbound.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hmassV : ∑ v ∈ V, (gaussMeasure (cfCylinder v)).toReal ≤ 1 :=
    NormalNumbers.VandeheyOut.sum_gaussMeasure_le_one_of_length (m := k) V hVlen
  have hcoef : (0:ℝ) ≤ (1 + 8 * Real.log 2) * (L / Real.log 2 + δ) := by positivity
  have h1 : (1 + 8 * Real.log 2) * (L / Real.log 2 + δ) *
      (∑ v ∈ V, (gaussMeasure (cfCylinder v)).toReal)
      ≤ (1 + 8 * Real.log 2) * (L / Real.log 2 + δ) :=
    (mul_le_mul_of_nonneg_left hmassV hcoef).trans (le_of_eq (by ring))
  have h2 : (1 + 8 * Real.log 2) * (L / Real.log 2 + δ)
      = (1 + 8 * Real.log 2) * (L / Real.log 2) + (1 + 8 * Real.log 2) * δ := by ring
  have h3 : (V.card : ℝ) * δ ≤ ε / 2 := by rw [hN] at hδ2; exact hδ2
  linarith


section Audit

#print axioms blockCount_hit_Ioo_le
#print axioms windowHit_Ioo_le

end Audit

end NormalNumbers.VandeheyS7
