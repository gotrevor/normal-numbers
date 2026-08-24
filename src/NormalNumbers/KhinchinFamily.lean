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

end NormalNumbers
