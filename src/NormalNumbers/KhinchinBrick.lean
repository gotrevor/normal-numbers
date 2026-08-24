/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFLogTail
import NormalNumbers.TBrick

/-!
# The Khinchin log-tail bad zone in Lebesgue measure (route C′)

Bridges `CFLogTail.lean`'s `gaussMeasure`-valued `markov_logBadZone_brick` bound into
Lebesgue `volume`, exactly mirroring the `cfBadZone` bridge
(`volume_iUnion_cfBadZone_le`/`_le_vol`, `TBrick.lean`) via the density-window
factor `2 log 2`. This is what lets `logBadZone` be unioned into the
`exists_mem_notMem_union_of_bounds` combine alongside the CF and d-ary bad
zones, all three now expressed as `ENNReal.ofReal (coeff) * volume (cfCylinder w)`.

## Main results

* `volume_logBadZone_le_vol` — `volume (logBadZone w n K η) ≤ ofReal (14 * (∫
  logTailFn K dγ)/η) * volume (cfCylinder w)`, uniform in `n`.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- **The Khinchin bad zone in Lebesgue, as a fraction of `|I_w|`.** Same two-step
bridge as `volume_iUnion_cfBadZone_le_vol`: `volume ≤ 2 log 2 · γ` on `(0,1)`,
then `γ(I_w) ≤ (log 2)⁻¹ · |I_w|`, so the `2 log 2` and `(log 2)⁻¹` factors
combine to a clean `2`, doubling the `gaussMeasure`-side coefficient `7` to `14`
— matching the CF bad zone's `14 · (…)/(δ²n)` shape exactly. -/
theorem volume_logBadZone_le_vol
    (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (n K : ℕ) {η : ℝ} (hη : 0 < η) :
    volume (logBadZone w n K η)
      ≤ ENNReal.ofReal (14 * (∫ x, logTailFn K x ∂gaussMeasure) / η)
          * volume (cfCylinder w) := by
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hwfin : volume (cfCylinder w) ≠ ⊤ := by
    have h1 : volume (cfCylinder w) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
      measure_mono (fun x hx => hx.1)
    rw [Real.volume_Ioo] at h1
    exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
  set μw : ℝ := (volume (cfCylinder w)).toReal with hμw
  have hmeas : MeasurableSet (logBadZone w n K η) := measurableSet_logBadZone w n K η
  have hsub : logBadZone w n K η ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  set T : ℝ := (∫ x, logTailFn K x ∂gaussMeasure) / η with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact div_nonneg (MeasureTheory.integral_nonneg fun x =>
      logTailFn_nonneg_pointwise K x) hη.le
  -- γ(bad) ≤ ofReal (7 T · γ(I_w))
  have hγle : gaussMeasure (logBadZone w n K η) ≤ ENNReal.ofReal (7 * T * (gaussMeasure (cfCylinder w)).toReal) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top gaussMeasure _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := markov_logBadZone_brick w hposw n K hη
    rwa [hT]
  -- volume(bad) ≤ ofReal (2 log 2) * γ(bad)
  have hstep1 : volume (logBadZone w n K η)
      ≤ ENNReal.ofReal (2 * Real.log 2) * gaussMeasure (logBadZone w n K η) :=
    volume_le_ofReal_mul_gaussMeasure _ hmeas hsub
  have hlog0' : (0 : ℝ) ≤ 2 * Real.log 2 := by linarith
  have hγw : (gaussMeasure (cfCylinder w)).toReal ≤ (Real.log 2)⁻¹ * μw := by
    have h := gaussMeasure_le_volume (cfCylinder w) (measurableSet_cfCylinder w)
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwfin) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← hμw] at h2
  have hγw0 : 0 ≤ (gaussMeasure (cfCylinder w)).toReal := ENNReal.toReal_nonneg
  have hcoeff : 2 * Real.log 2 * (7 * T * (gaussMeasure (cfCylinder w)).toReal)
      ≤ 14 * T / η * 0 + 14 * T * μw := by
    have h7T0 : 0 ≤ 7 * T := by positivity
    calc 2 * Real.log 2 * (7 * T * (gaussMeasure (cfCylinder w)).toReal)
        = (7 * T) * (2 * Real.log 2) * (gaussMeasure (cfCylinder w)).toReal := by ring
      _ ≤ (7 * T) * (2 * Real.log 2) * ((Real.log 2)⁻¹ * μw) := by
          gcongr
      _ = 14 * T * μw := by
          field_simp
          ring
      _ ≤ 14 * T / η * 0 + 14 * T * μw := by
          have : 14 * T / η * 0 = 0 := by ring
          linarith
  calc volume (logBadZone w n K η)
      ≤ ENNReal.ofReal (2 * Real.log 2) * gaussMeasure (logBadZone w n K η) := hstep1
    _ ≤ ENNReal.ofReal (2 * Real.log 2) * ENNReal.ofReal (7 * T * (gaussMeasure (cfCylinder w)).toReal) := by
        gcongr
    _ = ENNReal.ofReal (2 * Real.log 2 * (7 * T * (gaussMeasure (cfCylinder w)).toReal)) :=
        (ENNReal.ofReal_mul hlog0').symm
    _ ≤ ENNReal.ofReal (14 * T * μw) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [hcoeff]
    _ = ENNReal.ofReal (14 * T) * ENNReal.ofReal μw := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (14 * T) * volume (cfCylinder w) := by
        rw [hμw, ENNReal.ofReal_toReal hwfin]
    _ = ENNReal.ofReal (14 * (∫ x, logTailFn K x ∂gaussMeasure) / η) * volume (cfCylinder w) := by
        rw [hT]; ring_nf

/-- **The three-zone combine** (route C′): mirrors `exists_good_avoiding_bad`
(`TBrick.lean:470`) with the Khinchin `logBadZone` folded into the d-ary
bad-zone union via `measure_union_le` subadditivity, so the abstract two-zone
`exists_mem_notMem_union_of_bounds` still applies with `B₂' = dary ∪ log ∪
ℚ`. Coefficients are tightened from the original `<¼` each to `<⅙` each so
all THREE (CF, d-ary, log) sum below `½`. -/
theorem exists_good_avoiding_bad_khinchin {t : ℕ} (B : TBrick t)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a)
    (n kmin K : ℕ) (hn : 0 < n) {δ ε η : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hη : 0 < η)
    (hεt : (t : ℝ) * ε ≤ 1) (hpos : volume (cfCylinder B.w) ≠ 0)
    {C : ℝ}
    (hhalf : volume (cfCylinder B.w) ≤ 2 * volume (goodExtSet B.w C n))
    (hCF : 14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n) < 1 / 6)
    (hdary : (∑ d ∈ Finset.Icc 2 t,
        24 * (d : ℝ) ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
      < 1 / 6)
    (hlog : 14 * (∫ x, logTailFn K x ∂gaussMeasure) / η < 1 / 6) :
    ∃ x ∈ goodExtSet B.w C n, Irrational x ∧
      x ∉ (⋃ v ∈ F, cfBadZone B.w v n δ) ∪
        ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
          ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          ∪ logBadZone B.w n K η) := by
  have hwfin : volume (cfCylinder B.w) ≠ ⊤ := by
    have h1 : volume (cfCylinder B.w) ≤ volume (Set.Ioo (0 : ℝ) 1) :=
      measure_mono (fun x hx => hx.1)
    rw [Real.volume_Ioo] at h1
    exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
  have hxd : ∀ d ∈ Finset.Icc 2 t, 0 ≤ 24 * (d : ℝ) ^ 2
      * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := le_trans (by norm_num) hd.1
    exact div_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (daryBadRatio_pos d ε).le _))
      (by linarith [daryBadRatio_lt_one hd1 hε0])
  have hqD : 0 ≤ ∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
      * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) :=
    Finset.sum_nonneg hxd
  set qlog : ℝ := 14 * (∫ x, logTailFn K x ∂gaussMeasure) / η with hqlog
  have hqlog0 : 0 ≤ qlog := by
    rw [hqlog]
    have := volume_logBadZone_le_vol B.w B.hw_pos n K hη
    have hT0 : 0 ≤ (∫ x, logTailFn K x ∂gaussMeasure) :=
      MeasureTheory.integral_nonneg fun x => logTailFn_nonneg_pointwise K x
    positivity
  have hpCF : 0 ≤ 14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n) :=
    div_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun v _ => by positivity)) (by positivity)
  -- the combined d-ary ∪ log ∪ ℚ zone, in `ofReal(q+qlog) * vol0` form
  have hB₂dary := TBrick.volume_aggregate_bad_le B hε0 hεt kmin
  rw [← ENNReal.ofReal_sum_of_nonneg hxd] at hB₂dary
  have hB₂log := volume_logBadZone_le_vol B.w B.hw_pos n K hη
  have hB₂' : volume (((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
        ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
        ∪ logBadZone B.w n K η)
        ∪ Set.range ((↑) : ℚ → ℝ))
      ≤ ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
          * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) + qlog)
        * volume (cfCylinder B.w) := by
    calc volume (((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
          ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          ∪ logBadZone B.w n K η) ∪ Set.range ((↑) : ℚ → ℝ))
        ≤ volume ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
            ∪ logBadZone B.w n K η)
          + volume (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
      _ = volume ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
            ∪ logBadZone B.w n K η) := by
          rw [(Set.countable_range _).measure_zero, add_zero]
      _ ≤ volume (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          + volume (logBadZone B.w n K η) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
            * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε)) * volume (cfCylinder B.w)
          + ENNReal.ofReal qlog * volume (cfCylinder B.w) := add_le_add hB₂dary hB₂log
      _ = ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
            * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) + qlog)
          * volume (cfCylinder B.w) := by
          rw [← add_mul, ← ENNReal.ofReal_add hqD hqlog0]
  obtain ⟨x, hxG, hxB⟩ := exists_mem_notMem_union_of_bounds hpCF (by linarith [hqD, hqlog0])
    (by linarith) hpos hwfin hhalf
    (volume_iUnion_cfBadZone_le_vol B.w B.hw_pos F hF n hn hδ) hB₂'
  refine ⟨x, hxG, fun hrat => hxB (Or.inr (Or.inr hrat)), fun hmem => ?_⟩
  rcases hmem with h | h
  · exact hxB (Or.inl h)
  · rcases h with h | h
    · exact hxB (Or.inr (Or.inl (Or.inl h)))
    · exact hxB (Or.inr (Or.inl (Or.inr h)))

end NormalNumbers
