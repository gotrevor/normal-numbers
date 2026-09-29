/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-BX: the reduced state set is a COMPACT BOX — directive fact (δ)

Directive fact (α) says the only two ways past predictability are *finiteness of the predictor's
range* and genuine arithmetic of `Φ`.  This module supplies the first, unconditionally, and the
whole of it is elementary algebra on `MapState`.

* `width_eq` — **exactly** `width s = |det s| / (d·(c+d))`.  No inequality, no distortion input.
* `denRatio s := (c+d)/d` — the square root of the distortion `mob'(0)/mob'(1)`.
* `entries_abs_le_of_den_le`, `den_sq_le_of_width` — **the box lemma**: `|det| ≤ D`, `width ≥ η`
  and `denRatio ∈ [1/K, K]` force `d ≤ √(KD/η)` and `c+d ≤ √(KD/η)`, and the four `MapState`
  inequalities (`0 ≤ b ≤ d`, `0 ≤ a+b ≤ c+d`) then put **all four entries in `[−M, M]`**.
  Compactness needs bounded DISTORTION, not a width floor: that is why lap 74's hunt for a
  uniform width floor stalled — the floor is only half of the input, and the other half is free.
* `denRatio_comp_readMap` — reading a digit is the recursion `r ↦ (r+a)/(r+a−1) = 1 + 1/(r+a−1)`,
  so a read lands in `(1, 1+1/r]` *uniformly in the digit `a`*: reads CONTRACT the distortion.
* `denRatio_emit_comparable` — an emission moves `r` by a factor in `[b/(b+1), (b+1)/b] ⊆ [1/2,2]`,
  because `0 ≤ a+b ≤ c+d` and `0 ≤ b ≤ d` are exactly what the comparison needs.
* `denRatio_run_gt_half` / `denRatio_run_le_six` — hence along **any** run, from step 1 on
  `r > 1/2` and from step 2 on `r ≤ 6`.  No hypothesis on `x`, none on `Φ`, no normality.
* `absDet_runState` — `|det|` is a conserved quantity of the run (`det` is multiplicative and both
  a read and an emission contribute `±1`).
* `runState_entries_abs_le` — **the headline**: from step 2 on, every run state of width `≥ η` has
  all four entries in `[−M, M]` with `M = √(6·|det Φ|/η)`.

So the predictor `n ↦ (runState Φ x n)⁻¹(I_w)` has PRECOMPACT range, and — up to a precision `ρ`
— takes finitely many values.  That is the hypothesis directive fact (α) leaves room for.
-/
import NormalNumbers.VandeheyS7Run

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-! ## The determinant, and the exact width -/

/-- The determinant of the state's matrix. -/
def det (s : MapState) : ℝ := s.a * s.d - s.b * s.c

lemma det_ne_zero (s : MapState) : s.det ≠ 0 := s.hdet

/-- `det` is multiplicative. -/
theorem det_comp (s t : MapState) : (s.comp t).det = s.det * t.det := by
  simp only [det, comp_a, comp_b, comp_c, comp_d]
  ring

@[simp] theorem det_readMap (a : ℝ) (ha : 1 ≤ a) : (readMap a ha).det = -1 := by
  show (0:ℝ) * a - 1 * 1 = -1
  ring

/-- **The width, exactly.**  `|mob 1 − mob 0| = |det| / (d·(c+d))`. -/
theorem width_eq (s : MapState) : s.width = |s.det| / (s.d * (s.c + s.d)) := by
  have hd := s.hd
  have hcd := s.hcd
  have hpos : (0:ℝ) < s.d * (s.c + s.d) := mul_pos hd hcd
  have h : s.mob 1 - s.mob 0 = s.det / (s.d * (s.c + s.d)) := by
    show (s.a * 1 + s.b) / (s.c * 1 + s.d) - (s.a * 0 + s.b) / (s.c * 0 + s.d) = _
    rw [show s.a * 1 + s.b = s.a + s.b from by ring, show s.c * 1 + s.d = s.c + s.d from by ring,
      show s.a * 0 + s.b = s.b from by ring, show s.c * 0 + s.d = s.d from by ring, det]
    field_simp
    ring
  rw [width, h, abs_div, abs_of_pos hpos]

lemma width_pos (s : MapState) : 0 < s.width := by
  rw [width_eq]
  exact div_pos (abs_pos.mpr s.hdet) (mul_pos s.hd s.hcd)

/-! ## The denominator ratio -/

/-- The **denominator ratio** `(c+d)/d`.  Its square is the distortion `mob'(0)/mob'(1)`. -/
noncomputable def denRatio (s : MapState) : ℝ := (s.c + s.d) / s.d

lemma denRatio_pos (s : MapState) : 0 < s.denRatio := div_pos s.hcd s.hd

lemma denRatio_ne_zero (s : MapState) : s.denRatio ≠ 0 := (s.denRatio_pos).ne'

lemma c_add_d_eq (s : MapState) : s.c + s.d = s.denRatio * s.d := by
  rw [denRatio, div_mul_cancel₀ _ s.hd.ne']

/-! ## The box lemma -/

/-- Half one of the box lemma: the two denominators are bounded by `√(KD/η)`. -/
theorem den_sq_le_of_width {s : MapState} {D η K : ℝ} (hη : 0 < η)
    (hdet : |s.det| ≤ D) (hw : η ≤ s.width)
    (hr : s.denRatio ≤ K) (hr' : 1 / K ≤ s.denRatio) (hK : 0 < K) :
    s.d ^ 2 ≤ K * D / η ∧ (s.c + s.d) ^ 2 ≤ K * D / η := by
  have hd := s.hd
  have hcd := s.hcd
  have hprod : 0 < s.d * (s.c + s.d) := by positivity
  -- `d·(c+d) ≤ D/η`
  have hkey : s.d * (s.c + s.d) ≤ D / η := by
    have hwe : s.width = |s.det| / (s.d * (s.c + s.d)) := s.width_eq
    rw [hwe] at hw
    rw [le_div_iff₀ hη]
    have h1 : η * (s.d * (s.c + s.d)) ≤ |s.det| := by
      rw [le_div_iff₀ hprod] at hw
      linarith
    linarith [hdet, h1]
  have hDη : 0 ≤ D / η := le_trans hprod.le hkey
  constructor
  · -- `d ≤ K(c+d)` from `denRatio ≥ 1/K`
    have h : s.d ≤ K * (s.c + s.d) := by
      have := s.c_add_d_eq
      have hle : 1 / K * s.d ≤ s.denRatio * s.d := by
        exact mul_le_mul_of_nonneg_right hr' hd.le
      rw [← this] at hle
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK] at hle
      linarith
    have hA : s.d * s.d ≤ K * (s.d * (s.c + s.d)) := by nlinarith [h, hd]
    calc s.d ^ 2 = s.d * s.d := sq s.d
      _ ≤ K * (s.d * (s.c + s.d)) := hA
      _ ≤ K * (D / η) := mul_le_mul_of_nonneg_left hkey hK.le
      _ = K * D / η := by ring
  · -- `c+d ≤ K d` from `denRatio ≤ K`
    have h : s.c + s.d ≤ K * s.d := by
      have := s.c_add_d_eq
      rw [this]
      exact mul_le_mul_of_nonneg_right hr hd.le
    have hA : (s.c + s.d) * (s.c + s.d) ≤ K * (s.d * (s.c + s.d)) := by nlinarith [h, hcd]
    calc (s.c + s.d) ^ 2 = (s.c + s.d) * (s.c + s.d) := sq (s.c + s.d)
      _ ≤ K * (s.d * (s.c + s.d)) := hA
      _ ≤ K * (D / η) := mul_le_mul_of_nonneg_left hkey hK.le
      _ = K * D / η := by ring

/-- Half two of the box lemma: bounds on the two denominators bound **all four entries**. -/
theorem entries_abs_le_of_den_le {s : MapState} {M : ℝ}
    (hd : s.d ≤ M) (hcd : s.c + s.d ≤ M) :
    |s.a| ≤ M ∧ |s.b| ≤ M ∧ |s.c| ≤ M ∧ |s.d| ≤ M := by
  have hd0 := s.hd
  have hcd0 := s.hcd
  have hM : 0 ≤ M := le_trans hd0.le hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · linarith [s.hab0, s.hb0, s.hbd]
    · linarith [s.habcd, s.hb0]
  · rw [abs_le]; constructor <;> linarith [s.hb0, s.hbd]
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- **The box lemma (directive fact (δ)).**  A state of determinant at most `D`, width at least
`η` and denominator ratio in `[1/K, K]` has all four matrix entries in `[−M, M]`,
`M = √(K·D/η)`.  So the reduced states of width `≥ η` form a **precompact** family. -/
theorem entries_abs_le_of_width {s : MapState} {D η K : ℝ} (hη : 0 < η) (hK : 0 < K)
    (hdet : |s.det| ≤ D) (hw : η ≤ s.width)
    (hr : s.denRatio ≤ K) (hr' : 1 / K ≤ s.denRatio) :
    |s.a| ≤ Real.sqrt (K * D / η) ∧ |s.b| ≤ Real.sqrt (K * D / η) ∧
      |s.c| ≤ Real.sqrt (K * D / η) ∧ |s.d| ≤ Real.sqrt (K * D / η) := by
  obtain ⟨h1, h2⟩ := den_sq_le_of_width hη hdet hw hr hr' hK
  have hnn : 0 ≤ K * D / η := le_trans (sq_nonneg s.d) h1
  have hsq : Real.sqrt (K * D / η) ^ 2 = K * D / η := Real.sq_sqrt hnn
  have hs0 : 0 ≤ Real.sqrt (K * D / η) := Real.sqrt_nonneg _
  refine entries_abs_le_of_den_le ?_ ?_
  · nlinarith [s.hd, h1, hsq, hs0]
  · nlinarith [s.hcd, h2, hsq, hs0]

/-! ## The read step contracts the denominator ratio -/

lemma comp_readMap_c (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).c = s.d := by
  show s.c * 0 + s.d * 1 = s.d
  ring

lemma comp_readMap_d (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).d = s.c + s.d * a := by
  show s.c * 1 + s.d * a = s.c + s.d * a
  ring

/-- **The read recursion.**  `r ↦ 1 + 1/(r + a − 1)`. -/
theorem denRatio_comp_readMap (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).denRatio = 1 + 1 / (s.denRatio + a - 1) := by
  have hd := s.hd
  have hT : (0:ℝ) < s.c + s.d * a := by
    have h := (s.comp (readMap a ha)).hd
    rwa [comp_readMap_d] at h
  have hTne : (s.c + s.d * a) ≠ 0 := hT.ne'
  have h1 : (s.comp (readMap a ha)).denRatio = 1 + s.d / (s.c + s.d * a) := by
    rw [denRatio, comp_readMap_c, comp_readMap_d]
    field_simp
    ring
  have h2 : s.denRatio + a - 1 = (s.c + s.d * a) / s.d := by
    rw [denRatio]; field_simp; ring
  rw [h1, h2, one_div_div]

lemma denRatio_add_sub_pos (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    0 < s.denRatio + a - 1 := by linarith [s.denRatio_pos]

/-- **Reads land above `1`.** -/
theorem one_lt_denRatio_comp_readMap (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    1 < (s.comp (readMap a ha)).denRatio := by
  rw [denRatio_comp_readMap]
  have h : 0 < 1 / (s.denRatio + a - 1) := by
    exact one_div_pos.mpr (s.denRatio_add_sub_pos ha)
  linarith

/-- **Reads contract, uniformly in the digit.**  The bound does not see `a` at all. -/
theorem denRatio_comp_readMap_le (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).denRatio ≤ 1 + 1 / s.denRatio := by
  rw [denRatio_comp_readMap]
  have hr := s.denRatio_pos
  have h : s.denRatio ≤ s.denRatio + a - 1 := by linarith
  have := one_div_le_one_div_of_le hr h
  linarith

/-! ## The emit step moves the ratio by a factor in `[1/2, 2]` -/

/-- **The emission comparison.**  An emitted state's denominator ratio is within a factor `2` of
its parent's — because `0 ≤ b ≤ d` and `0 ≤ a+b ≤ c+d` are exactly the needed inequalities. -/
theorem denRatio_emit_comparable {t : MapState} {b : ℕ} {u : MapState} (h : EmitStep t b u) :
    t.denRatio ≤ 2 * u.denRatio ∧ u.denRatio ≤ 2 * t.denRatio := by
  obtain ⟨hb, hcu, hdu, hct, hdt⟩ := h
  have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  have hQ : 0 < u.d := u.hd
  have hP : 0 < u.c + u.d := u.hcd
  have htd : 0 < t.d := t.hd
  have hA0 : 0 ≤ u.a + u.b := u.hab0
  have hAP : u.a + u.b ≤ u.c + u.d := u.habcd
  have hB0 : 0 ≤ u.b := u.hb0
  have hBQ : u.b ≤ u.d := u.hbd
  have htcd : t.c + t.d = (u.a + u.b) + (b:ℝ) * (u.c + u.d) := by rw [hct, hdt, hcu, hdu]; ring
  have htd2 : t.d = u.b + (b:ℝ) * u.d := by rw [hdt, hdu]
  have hden : 0 < u.b + (b:ℝ) * u.d := by rw [← htd2]; exact htd
  constructor
  · have hrw : 2 * ((u.c + u.d) / u.d) = (2 * (u.c + u.d)) / u.d := by ring
    rw [denRatio, denRatio, htcd, htd2, hrw, div_le_div_iff₀ hden hQ]
    nlinarith [mul_le_mul_of_nonneg_right hAP hQ.le, mul_nonneg hP.le hB0,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (b:ℝ) - 1) hP.le) hQ.le]
  · have hrw : 2 * (((u.a + u.b) + (b:ℝ) * (u.c + u.d)) / (u.b + (b:ℝ) * u.d))
        = (2 * ((u.a + u.b) + (b:ℝ) * (u.c + u.d))) / (u.b + (b:ℝ) * u.d) := by ring
    rw [denRatio, denRatio, htcd, htd2, hrw, div_le_div_iff₀ hQ hden]
    nlinarith [mul_le_mul_of_nonneg_left hBQ hP.le, mul_nonneg hA0 hQ.le,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (b:ℝ) - 1) hP.le) hQ.le]

/-! ## `|det|` is conserved by the run -/

theorem absDet_step (t : MapState) : |(step t).1.det| = |t.det| := by
  by_cases h : Emittable t
  · obtain ⟨b, hemit, -⟩ := step_emitStep h
    have hb : 1 ≤ b := hemit.1
    have heq := (emitStep_iff hb).1 hemit
    have h2 := congrArg MapState.det heq
    rw [det_comp, det_readMap] at h2
    have h3 : t.det = -(step t).1.det := by linarith
    rw [h3, abs_neg]
  · rw [step_of_not_emittable h]

theorem absDet_runState (Φ : MapState) (x : ℝ) (n : ℕ) :
    |(runState Φ x n).det| = |Φ.det| := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hst : runState Φ x (n + 1) = (step ((runState Φ x n).comp (readAt x n))).1 := rfl
      rw [hst, absDet_step, det_comp]
      rw [readAt, det_readMap, abs_mul]
      simpa using ih

/-! ## The band: `denRatio` along any run -/

/-- **From step 1 on, `denRatio > 1/2`** — with no hypothesis whatsoever. -/
theorem half_lt_denRatio_runState_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    1 / 2 < (runState Φ x (n + 1)).denRatio := by
  set t := (runState Φ x n).comp (readAt x n) with ht
  have hone : 1 < t.denRatio := by
    rw [ht, readAt]; exact one_lt_denRatio_comp_readMap _ (one_le_inDigit_real x n)
  have hst : runState Φ x (n + 1) = (step t).1 := rfl
  by_cases h : Emittable t
  · obtain ⟨b, hemit, -⟩ := step_emitStep h
    obtain ⟨h1, -⟩ := denRatio_emit_comparable hemit
    rw [hst]; linarith
  · rw [hst, step_of_not_emittable h]; linarith

/-- **From step 2 on, `denRatio ≤ 6`** — again with no hypothesis. -/
theorem denRatio_runState_le_six (Φ : MapState) (x : ℝ) (n : ℕ) :
    (runState Φ x (n + 2)).denRatio ≤ 6 := by
  have hprev : 1 / 2 < (runState Φ x (n + 1)).denRatio := half_lt_denRatio_runState_succ Φ x n
  set t := (runState Φ x (n + 1)).comp (readAt x (n + 1)) with ht
  have hle : t.denRatio ≤ 3 := by
    have h1 : t.denRatio ≤ 1 + 1 / (runState Φ x (n + 1)).denRatio := by
      rw [ht, readAt]; exact denRatio_comp_readMap_le _ (one_le_inDigit_real x (n + 1))
    have h2 : 1 / (runState Φ x (n + 1)).denRatio ≤ 2 := by
      rw [div_le_iff₀ (denRatio_pos _)]; linarith
    linarith
  have hst : runState Φ x (n + 2) = (step t).1 := rfl
  by_cases h : Emittable t
  · obtain ⟨b, hemit, -⟩ := step_emitStep h
    obtain ⟨-, h2⟩ := denRatio_emit_comparable hemit
    rw [hst]; linarith
  · rw [hst, step_of_not_emittable h]; linarith

/-! ## Fact (δ): the run's states of width `≥ η` lie in a fixed box -/

/-- **Directive fact (δ), the headline.**  From step 2 on, any run state whose width is at least
`η` has all four matrix entries in `[−M, M]` with `M = √(6·|det Φ|/η)`.  The bound depends on
`Φ` only through `|det Φ|`, and on nothing else — not on `x`, not on normality, not on the
emitted word.  So the predictor `n ↦ (runState Φ x n)⁻¹(I_w)` has **precompact range**. -/
theorem runState_entries_abs_le {Φ : MapState} {x η : ℝ} (hη : 0 < η) (n : ℕ)
    (hw : η ≤ (runState Φ x (n + 2)).width) :
    |(runState Φ x (n + 2)).a| ≤ Real.sqrt (6 * |Φ.det| / η) ∧
      |(runState Φ x (n + 2)).b| ≤ Real.sqrt (6 * |Φ.det| / η) ∧
      |(runState Φ x (n + 2)).c| ≤ Real.sqrt (6 * |Φ.det| / η) ∧
      |(runState Φ x (n + 2)).d| ≤ Real.sqrt (6 * |Φ.det| / η) := by
  refine entries_abs_le_of_width hη (by norm_num) (le_of_eq (absDet_runState Φ x (n + 2))) hw
    (denRatio_runState_le_six Φ x n) ?_
  have h := half_lt_denRatio_runState_succ Φ x (n + 1)
  have : (1:ℝ) / 6 ≤ 1 / 2 := by norm_num
  linarith

end MapState

section Audit

#print axioms MapState.width_eq
#print axioms MapState.entries_abs_le_of_width
#print axioms MapState.denRatio_comp_readMap
#print axioms MapState.denRatio_emit_comparable
#print axioms MapState.absDet_runState
#print axioms MapState.half_lt_denRatio_runState_succ
#print axioms MapState.denRatio_runState_le_six
#print axioms MapState.runState_entries_abs_le

end Audit

end NormalNumbers.VandeheyS7
