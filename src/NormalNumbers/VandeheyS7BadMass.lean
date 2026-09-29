/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7BadSet
import NormalNumbers.VandeheyS7Sep

/-!
# S7-BM: the bad set of lap 48, measured

`VandeheyS7Sep` introduced `nearInv η` — the `η`-neighbourhood of the reciprocals `1/k` — as the
set of positions where the state's bounded distortion fails (directive fact 2), and controlled its
*frequency* only through the chain's second hypothesis `ImageTight`
(`exists_nearInv_freq_le`).

Lap 61 measured the same set.  This module joins the two: `nearInv η` is measurable and

* `volume_nearInv_le` — `|nearInv η| ≤ 7√η`,
* `gaussMeasure_nearInv_le` — `γ(nearInv η) ≤ 7√η / log 2`,

both unconditional.  So the bad set is *small in measure* with no hypothesis at all; what
`ImageTight` was being spent on is only the passage from measure to frequency, and that passage is
the one the moving-target refutations (`not_gappedHitPrinciple`) say cannot be soft.  Naming the
split this precisely is the point: the measure half is now free.

## Guard rule

Content locator: the `√` is inherited from `volume_badSet_le` and is forced by the accumulation of
`1/k` at `0`; a `C·η` bound here would be false.  Degenerate case: `η ≥ 1` makes both bounds
weaker than the trivial `γ ≤ 1`, so all content is at small `η`.
-/

namespace NormalNumbers.VandeheyS7

open MeasureTheory NormalNumbers

theorem nearInv_eq_iUnion (η : ℝ) :
    nearInv η = ⋃ k ∈ {k : ℕ | 1 ≤ k}, Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η) := by
  ext t
  simp only [nearInv, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioo, exists_prop]
  constructor
  · rintro ⟨k, hk, habs⟩
    exact ⟨k, hk, by have := abs_lt.1 habs; constructor <;> linarith [this.1, this.2]⟩
  · rintro ⟨k, hk, h1, h2⟩
    exact ⟨k, hk, abs_lt.2 ⟨by linarith, by linarith⟩⟩

theorem measurableSet_nearInv (η : ℝ) : MeasurableSet (nearInv η) := by
  rw [nearInv_eq_iUnion]
  exact MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_Ioo

/-- **The bad set is small.**  Lebesgue version. -/
theorem volume_nearInv_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    volume (nearInv η) ≤ ENNReal.ofReal (7 * Real.sqrt η) := by
  classical
  set s := Real.sqrt η with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hη
  have hss : s * s = η := Real.mul_self_sqrt hη.le
  have hs1 : s ≤ 1 := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hη1
  have hηs : η ≤ s := by nlinarith
  set K : ℕ := ⌈1 / s⌉₊ with hKdef
  have hKpos : 0 < K := by rw [hKdef, Nat.ceil_pos]; positivity
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hKlow : 1 / s ≤ (K : ℝ) := Nat.le_ceil _
  have hKhigh : (K : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsub : nearInv η ⊆ Set.Ioo (-η) (1 / (K : ℝ) + η) ∪
      ⋃ k ∈ Finset.Icc 1 K, Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η) := by
    rintro x ⟨k, hk1, habs⟩
    rcases le_or_gt k K with hk | hk
    · right
      simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop]
      exact ⟨k, ⟨hk1, hk⟩, by
        have := abs_lt.1 habs
        exact ⟨by linarith [this.1], by linarith [this.2]⟩⟩
    · left
      have hkR : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.le
      have hk0 : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := lt_of_lt_of_le hKpos hk.le
        exact_mod_cast this
      have hinv : 1 / (k : ℝ) ≤ 1 / (K : ℝ) := one_div_le_one_div_of_le hKR hkR
      have h1 := (abs_lt.1 habs).1
      have h2 := (abs_lt.1 habs).2
      have hpos : (0 : ℝ) < 1 / (k : ℝ) := by positivity
      exact ⟨by linarith, by linarith⟩
  have hcov := measure_mono (μ := (volume : Measure ℝ)) hsub
  have hunion : volume (Set.Ioo (-η) (1 / (K : ℝ) + η) ∪
      ⋃ k ∈ Finset.Icc 1 K, Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η))
      ≤ volume (Set.Ioo (-η) (1 / (K : ℝ) + η))
        + ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η)) := by
    refine le_trans (measure_union_le _ _) (by
      gcongr
      exact measure_biUnion_finset_le _ _)
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      volume (Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η)) ≤ ENNReal.ofReal (2 * η) := by
    intro k _
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hsum : ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η))
      ≤ ENNReal.ofReal (2 * η * (K : ℝ)) := by
    calc ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η))
        ≤ ∑ _k ∈ Finset.Icc 1 K, ENNReal.ofReal (2 * η) := Finset.sum_le_sum hterm
      _ = (K : ENNReal) * ENNReal.ofReal (2 * η) := by
          rw [Finset.sum_const, Nat.card_Icc]
          simp [nsmul_eq_mul]
      _ = ENNReal.ofReal ((K : ℝ) * (2 * η)) := by
          conv_rhs => rw [ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (2 * η * (K : ℝ)) := by rw [mul_comm]
  have hfirst : volume (Set.Ioo (-η) (1 / (K : ℝ) + η))
      = ENNReal.ofReal (1 / (K : ℝ) + 2 * η) := by
    rw [Real.volume_Ioo]; ring_nf
  have hreal : 1 / (K : ℝ) + 2 * η + 2 * η * (K : ℝ) ≤ 7 * s := by
    have h1 : 1 / (K : ℝ) ≤ s := by
      rw [div_le_iff₀ hKR]
      have h := hKlow
      rw [div_le_iff₀ hs0] at h
      linarith
    have h2 : 2 * η * (K : ℝ) ≤ 2 * s + 2 * η := by
      have hKb : (K : ℝ) ≤ 1 / s + 1 := hKhigh.le
      have hstep : 2 * η * (K : ℝ) ≤ 2 * η * (1 / s + 1) := by nlinarith
      have hds : η * (1 / s) = s := by field_simp; nlinarith
      nlinarith [hstep, hds]
    linarith
  calc volume (nearInv η) ≤ _ := hcov
    _ ≤ volume (Set.Ioo (-η) (1 / (K : ℝ) + η))
        + ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - η) (1 / (k : ℝ) + η)) := hunion
    _ ≤ ENNReal.ofReal (1 / (K : ℝ) + 2 * η) + ENNReal.ofReal (2 * η * (K : ℝ)) := by
        rw [hfirst]; gcongr
    _ = ENNReal.ofReal (1 / (K : ℝ) + 2 * η + 2 * η * (K : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (7 * Real.sqrt η) := ENNReal.ofReal_le_ofReal hreal

/-- **The bad set is small, in Gauss measure.**  Unconditional: no `ImageTight`. -/
theorem gaussMeasure_nearInv_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    gaussMeasure (nearInv η) ≤ ENNReal.ofReal (7 * Real.sqrt η / Real.log 2) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := gaussMeasure_le_volume (nearInv η) (measurableSet_nearInv η)
  refine le_trans h1 ?_
  have h2 : ENNReal.ofReal (Real.log 2)⁻¹ * volume (nearInv η)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * ENNReal.ofReal (7 * Real.sqrt η) := by
    gcongr
    exact volume_nearInv_le hη hη1
  refine le_trans h2 ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_mul_eq_div]

section Audit

#print axioms measurableSet_nearInv
#print axioms volume_nearInv_le
#print axioms gaussMeasure_nearInv_le

end Audit

end NormalNumbers.VandeheyS7
