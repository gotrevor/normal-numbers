/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.KhinchinBrick

/-!
# A summable family of log-tail zones (route C′ — corrected design)

**Design correction.** The natural first attempt (`KFn t`/`schedEps t` in
`CFSchedule.lean`, ties the log-cutoff `K` to the level `t` via a SHRINKING
slack `η_t = schedEps t → 0`) does NOT assemble into `xstar_log_tail_uniform`:
Markov forces `K_t → ∞` to compensate `η_t → 0`, so for any FIXED external
cutoff `K`, eventually (`K_t > K`) the level's own guarantee bounds a
STRICTLY SMALLER quantity (`tail-past-K_t ≤ tail-past-K`) than the one we
need (`tail-past-K`), and this happens for a COFINITE set of levels — so the
per-level bound never transfers to a fixed `K` uniformly in `n`.

**Fix**: use a GLOBAL (level-independent) countable family of cutoffs
`(Kj j, ηj j)`, `j : ℕ`, with `ηj j → 0` and a SUMMABLE coefficient budget
`cj j` (`∑ⱼ cj j ≤ 1/7`, geometric). At level `t`, the schedule makes the
extension word avoid ALL `j < t` zones SIMULTANEOUSLY (a FINITE union whose
total measure is bounded by the FULL geometric sum `1/7`, uniform in `t` —
no re-derivation of `K` per level). For a target `ε`, pick `j(ε)` with
`ηj j(ε) ≤ ε`; the FIXED cutoff `K₀ := Kj j(ε)` then works for every level
`t > j(ε)` (i.e. eventually in `n`) — the level's own guarantee at
`Kj j(ε)` is available VERBATIM (not chasing a growing `K_t`).
-/

namespace NormalNumbers

open MeasureTheory Filter

/-- The `j`-th target slack: `ηj j = 1/(j+1) → 0`. -/
noncomputable def khinchinEta (j : ℕ) : ℝ := 1 / (j + 1)

theorem khinchinEta_pos (j : ℕ) : 0 < khinchinEta j := by
  unfold khinchinEta; positivity

/-- The `j`-th coefficient budget: `cj j = (1/7)·(1/2)^{j+1}`, geometric —
summable with total `≤ 1/7`, leaving room alongside the CF/d-ary `<1/6` each
(`1/6+1/6+1/7 < 1/2`). -/
noncomputable def khinchinCoeff (j : ℕ) : ℝ := (1 / 7) * (1 / 2 : ℝ) ^ (j + 1)

theorem khinchinCoeff_pos (j : ℕ) : 0 < khinchinCoeff j := by
  unfold khinchinCoeff; positivity

/-- Closed form for the partial sums: `∑_{j<t} cj j = (1/7)·(1 − (1/2)^t)`. -/
theorem sum_khinchinCoeff_eq (t : ℕ) :
    ∑ j ∈ Finset.range t, khinchinCoeff j = (1 / 7) * (1 - (1 / 2 : ℝ) ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      unfold khinchinCoeff
      rw [pow_succ]
      ring

/-- The partial sums are `≤ 1/7` uniformly in `t`. -/
theorem sum_khinchinCoeff_le (t : ℕ) :
    ∑ j ∈ Finset.range t, khinchinCoeff j ≤ 1 / 7 := by
  rw [sum_khinchinCoeff_eq]
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ t := by positivity
  linarith

/-- The `j`-th cutoff: the smallest-by-choice `K` making the Markov
coefficient at slack `ηj j` drop below the budget `cj j`. -/
noncomputable def khinchinK (j : ℕ) : ℕ :=
  (exists_K_logCoeff_lt (khinchinEta j) (khinchinEta_pos j) (khinchinCoeff_pos j)).choose

theorem khinchinK_spec (j : ℕ) :
    14 * (∫ x, logTailFn (khinchinK j) x ∂gaussMeasure) / khinchinEta j < khinchinCoeff j :=
  (exists_K_logCoeff_lt (khinchinEta j) (khinchinEta_pos j) (khinchinCoeff_pos j)).choose_spec
    (khinchinK j) (le_refl _)

/-- Each individual zone in the family, in `ofReal(coeff) * vol` form. -/
theorem volume_logBadZone_khinchinK_le (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (n j : ℕ) :
    volume (logBadZone w n (khinchinK j) (khinchinEta j))
      ≤ ENNReal.ofReal (khinchinCoeff j) * volume (cfCylinder w) := by
  calc volume (logBadZone w n (khinchinK j) (khinchinEta j))
      ≤ ENNReal.ofReal (14 * (∫ x, logTailFn (khinchinK j) x ∂gaussMeasure) / khinchinEta j)
          * volume (cfCylinder w) :=
        volume_logBadZone_le_vol w hposw n (khinchinK j) (khinchinEta_pos j)
    _ ≤ ENNReal.ofReal (khinchinCoeff j) * volume (cfCylinder w) := by
        gcongr
        exact (khinchinK_spec j).le

/-- **The summable family bound** (route C′ fix): the union of the first `t`
log-tail zones has Lebesgue measure at most `(1/7)·|I_w|`, UNIFORM IN `t`
(the geometric budget never exceeds its infinite sum). This is what lets a
schedule avoid EVERY `j < t` zone at level `t` without the per-level
coefficient blowing up as `t → ∞`. -/
theorem volume_iUnion_logBadZone_khinchinK_le_vol
    (w : List ℕ) (hposw : ∀ a ∈ w, 1 ≤ a) (n t : ℕ) :
    volume (⋃ j ∈ Finset.range t, logBadZone w n (khinchinK j) (khinchinEta j))
      ≤ ENNReal.ofReal (1 / 7 : ℝ) * volume (cfCylinder w) := by
  have hstep : volume (⋃ j ∈ Finset.range t, logBadZone w n (khinchinK j) (khinchinEta j))
      ≤ ∑ j ∈ Finset.range t, ENNReal.ofReal (khinchinCoeff j) * volume (cfCylinder w) := by
    calc volume (⋃ j ∈ Finset.range t, logBadZone w n (khinchinK j) (khinchinEta j))
        ≤ ∑ j ∈ Finset.range t, volume (logBadZone w n (khinchinK j) (khinchinEta j)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range t, ENNReal.ofReal (khinchinCoeff j) * volume (cfCylinder w) :=
          Finset.sum_le_sum fun j _ => volume_logBadZone_khinchinK_le w hposw n j
  refine hstep.trans ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun j _ => (khinchinCoeff_pos j).le]
  gcongr
  exact sum_khinchinCoeff_le t

/-- **The three-zone combine, FAMILY form** (route C′, corrected design):
mirrors `exists_good_avoiding_bad_khinchin` (`KhinchinBrick.lean`) with the
SINGLE log zone replaced by the union of the first `tK` family zones — this
is what avoids the level-tied-cutoff assembly bug (see module docstring).
The log budget `1/7` is a FIXED constant (no hypothesis needed): CF/d-ary
stay `< 1/6` each, and `1/6 + 1/6 + 1/7 < 1/2`. -/
theorem exists_good_avoiding_bad_khinchin_family {t : ℕ} (B : TBrick t)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a)
    (n kmin tK : ℕ) (hn : 0 < n) {δ ε : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε)
    (hεt : (t : ℝ) * ε ≤ 1) (hpos : volume (cfCylinder B.w) ≠ 0)
    {C : ℝ}
    (hhalf : volume (cfCylinder B.w) ≤ 2 * volume (goodExtSet B.w C n))
    (hCF : 14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n) < 1 / 6)
    (hdary : (∑ d ∈ Finset.Icc 2 t,
        24 * (d : ℝ) ^ 2 * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε))
      < 1 / 6) :
    ∃ x ∈ goodExtSet B.w C n, Irrational x ∧
      x ∉ (⋃ v ∈ F, cfBadZone B.w v n δ) ∪
        ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
          ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          ∪ (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j))) := by
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
  have hpCF : 0 ≤ 14 * (∑ v ∈ F, (8 * (v.length : ℝ) + 80)) / (δ ^ 2 * n) :=
    div_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun v _ => by positivity)) (by positivity)
  have hB₂dary := TBrick.volume_aggregate_bad_le B hε0 hεt kmin
  rw [← ENNReal.ofReal_sum_of_nonneg hxd] at hB₂dary
  have hB₂log := volume_iUnion_logBadZone_khinchinK_le_vol B.w B.hw_pos n tK
  have hB₂' : volume (((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
        ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
        ∪ (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j)))
        ∪ Set.range ((↑) : ℚ → ℝ))
      ≤ ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
          * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) + 1 / 7)
        * volume (cfCylinder B.w) := by
    calc volume (((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
          ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          ∪ (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j)))
          ∪ Set.range ((↑) : ℚ → ℝ))
        ≤ volume ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
            ∪ (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j)))
          + volume (Set.range ((↑) : ℚ → ℝ)) := measure_union_le _ _
      _ = volume ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
            ∪ (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j))) := by
          rw [(Set.countable_range _).measure_zero, add_zero]
      _ ≤ volume (⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
          + volume (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j)) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
            * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε)) * volume (cfCylinder B.w)
          + ENNReal.ofReal (1 / 7 : ℝ) * volume (cfCylinder B.w) := add_le_add hB₂dary hB₂log
      _ = ENNReal.ofReal (∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
            * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) + 1 / 7)
          * volume (cfCylinder B.w) := by
          rw [← add_mul, ← ENNReal.ofReal_add hqD (by norm_num : (0:ℝ) ≤ 1/7)]
  obtain ⟨x, hxG, hxB⟩ := exists_mem_notMem_union_of_bounds hpCF
    (by linarith [hqD] : (0:ℝ) ≤ ∑ d ∈ Finset.Icc 2 t, 24 * (d : ℝ) ^ 2
        * daryBadRatio d ε ^ kmin / (1 - daryBadRatio d ε) + 1 / 7)
    (by linarith) hpos hwfin hhalf
    (volume_iUnion_cfBadZone_le_vol B.w B.hw_pos F hF n hn hδ) hB₂'
  refine ⟨x, hxG, fun hrat => hxB (Or.inr (Or.inr hrat)), fun hmem => ?_⟩
  rcases hmem with h | h
  · exact hxB (Or.inl h)
  · rcases h with h | h
    · exact hxB (Or.inr (Or.inl (Or.inl h)))
    · exact hxB (Or.inr (Or.inl (Or.inr h)))

/-- **Lemma-13 measure core, FAMILY form, unconditional for large `n`,
`kmin`.** Mirrors `exists_good_avoiding_bad_of_large_khinchin`
(`KhinchinBrick.lean`) but the log budget is FIXED (`1/7`, no `K`/`η`
hypothesis needed) so there is no third threshold to extract — `tK` is a
FREE parameter at call sites (the caller picks how many family zones to
avoid, e.g. `tK = level`). -/
theorem exists_good_avoiding_bad_of_large_khinchin_family (t : ℕ)
    (F : Finset (List ℕ)) (hF : ∀ v ∈ F, ∀ a ∈ v, 1 ≤ a) {δ ε : ℝ}
    (hδ : 0 < δ) (hε0 : 0 < ε) (hεt : (t : ℝ) * ε ≤ 1)
    {C : ℝ}
    (hhalf : ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
      volume (cfCylinder w) ≤ 2 * volume (goodExtSet w C n)) :
    ∃ N kmin₀ : ℕ, ∀ (B : TBrick t), ∀ n, N ≤ n → 0 < n → ∀ kmin ≥ kmin₀, ∀ tK : ℕ,
      ∃ x ∈ goodExtSet B.w C n, Irrational x ∧
        x ∉ (⋃ v ∈ F, cfBadZone B.w v n δ) ∪
          ((⋃ d ∈ Finset.Icc 2 t, ⋃ i ∈ Finset.range 2, ⋃ k : ℕ,
            ⋃ (_ : kmin ≤ k), daryBadZoneWide d (B.m d) (B.j d + i) ε k)
            ∪ (⋃ j ∈ Finset.range tK, logBadZone B.w n (khinchinK j) (khinchinEta j))) := by
  obtain ⟨N, hN⟩ := exists_N_cfCoeff_lt' (∑ v ∈ F, (8 * (v.length : ℝ) + 80))
    (Finset.sum_nonneg fun v _ => by positivity) hδ (by norm_num : (0:ℝ) < 1/6)
  obtain ⟨kmin₀, hkmin⟩ := exists_kmin_daryCoeff_lt' t hε0 (by norm_num : (0:ℝ) < 1/6)
  refine ⟨N, kmin₀, fun B n hn hn0 kmin hk tK => ?_⟩
  exact exists_good_avoiding_bad_khinchin_family B F hF n kmin tK hn0 hδ hε0 hεt
    (volume_cfCylinder_ne_zero B.w B.hw_ne B.hw_pos)
    (hhalf B.w B.hw_ne B.hw_pos n) (hN n hn hn0) (hkmin kmin hk)

end NormalNumbers
