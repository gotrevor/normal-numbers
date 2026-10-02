/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-HT: the width IS a height, and the height is a two-sided ledger of digits

The remaining input to fact (δ) is the **width floor in frequency form**.  This module changes what
that question is about.  Combining `width_eq` (`width = |det|/(d·(c+d))`, S7-BX), the denominator
band `denRatio ∈ (1/2, 6]` (S7-BX) and the conservation of `|det|` (S7-BX):

    |det Φ| / (6·d²)  ≤  width  ≤  2·|det Φ| / d²      (`width_runState_bounds`)

so **the width is `d^{-2}`, up to absolute constants** — a height, not an analytic accident.  And
`d` moves by an explicit factor at each half-step:

* a read multiplies it by `denRatio + a − 1 ∈ (a − 1/2, a + 5]` (`d_comp_readMap`), so
  `log d` gains `≈ log a`;
* an emission multiplies it by `mob 0 ∈ [1/(b+1), 1/b]` (`d_emit`, `emit_mob_zero_mem`), so
  `log d` loses `≈ log b`.

Hence `log d_n ≈ Σ_{k<n} log a_k − Σ_{m<N_n} log b_m`: **the state's height is the input
log-continuant minus the output log-continuant**, and the width floor asks how often the output
falls behind the input.  One half of that ledger is already unconditional: `runState_minDen_ge`
(S7-NR) says `d_n ≥ √(|det Φ|/6)`, i.e. *the output can never get ahead* — which is the
transducer's version of `q_n(y) ≲ φ·q_n(x)`.

So the open half is exactly: `freq{n : d_n > R} → 0` as `R → ∞`.  That is a Birkhoff question
about a difference of two digit-sums, not a geometric question about intervals, and it is the
shape in which CF-normality of `x` can actually be applied to one of the two sums.
-/
import NormalNumbers.VandeheyS7Near

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-! ## The width is `d^{-2}` -/

/-- With the denominator ratio in a band, the width is pinned to `|det|/d²` up to the band. -/
theorem width_bounds_of_denRatio {s : MapState} {K : ℝ} (hK : 0 < K)
    (hr : s.denRatio ≤ K) (hr' : 1 / K ≤ s.denRatio) :
    |s.det| / (K * s.d ^ 2) ≤ s.width ∧ s.width ≤ K * |s.det| / s.d ^ 2 := by
  have hd := s.hd
  have hcd := s.hcd
  have hc : s.c + s.d = s.denRatio * s.d := s.c_add_d_eq
  have hrp := s.denRatio_pos
  have hdet : 0 < |s.det| := abs_pos.mpr s.hdet
  have hprod : s.d * (s.c + s.d) = s.denRatio * s.d ^ 2 := by rw [hc]; ring
  rw [width_eq, hprod]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hdet.le (sq_nonneg s.d)) (sub_nonneg.mpr hr)]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hKr : 1 ≤ K * s.denRatio := by
      rw [div_le_iff₀ hK] at hr'
      linarith
    nlinarith [mul_nonneg (mul_nonneg hdet.le (sq_nonneg s.d))
      (by linarith : (0:ℝ) ≤ K * s.denRatio - 1)]

/-- **The width of a run state IS its height.**  From step 2 on. -/
theorem width_runState_bounds (Φ : MapState) (x : ℝ) (n : ℕ) :
    |Φ.det| / (6 * (runState Φ x (n + 2)).d ^ 2) ≤ (runState Φ x (n + 2)).width ∧
      (runState Φ x (n + 2)).width ≤ 6 * |Φ.det| / (runState Φ x (n + 2)).d ^ 2 := by
  have hband : (runState Φ x (n + 2)).denRatio ≤ 6 := denRatio_runState_le_six Φ x n
  have hband' : (1:ℝ) / 6 ≤ (runState Φ x (n + 2)).denRatio := by
    have h := half_lt_denRatio_runState_succ Φ x (n + 1)
    linarith
  have h := width_bounds_of_denRatio (show (0:ℝ) < 6 by norm_num) hband hband'
  rwa [absDet_runState Φ x (n + 2)] at h

/-! ## The height ledger, half-step by half-step -/

/-- **A read multiplies the height by `denRatio + a − 1`.** -/
theorem d_comp_readMap (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).d = s.d * (s.denRatio + a - 1) := by
  rw [comp_readMap_d]
  have hc : s.c + s.d = s.denRatio * s.d := s.c_add_d_eq
  have : s.c = s.denRatio * s.d - s.d := by linarith
  rw [this]; ring

/-- The read factor is bounded in terms of the digit alone, given the band. -/
theorem d_comp_readMap_factor_bounds (s : MapState) {a : ℝ} (_ha : 1 ≤ a)
    {K : ℝ} (hr : s.denRatio ≤ K) :
    a - 1 < s.denRatio + a - 1 ∧ s.denRatio + a - 1 ≤ a - 1 + K := by
  exact ⟨by linarith [s.denRatio_pos], by linarith⟩

/-- **An emission multiplies the height by `mob 0`.** -/
theorem d_emit {t : MapState} {b : ℕ} {u : MapState} (h : EmitStep t b u) :
    u.d = t.mob 0 * t.d := by
  obtain ⟨-, -, hdu, -, -⟩ := h
  have hmob : t.mob 0 = t.b / t.d := by
    show (t.a * 0 + t.b) / (t.c * 0 + t.d) = t.b / t.d
    ring_nf
  rw [hdu, hmob, div_mul_cancel₀ _ t.hd.ne']

/-- **And that factor is `≍ 1/b`.**  The image of an emitting state lies in the cylinder `I_b`. -/
theorem emit_mob_zero_mem {t : MapState} {b : ℕ} {u : MapState} (h : EmitStep t b u) :
    1 / ((b : ℝ) + 1) ≤ t.mob 0 ∧ t.mob 0 ≤ 1 / (b : ℝ) := by
  have hb : 1 ≤ b := h.1
  have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  have heq := (emitStep_iff hb).1 h
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hval : t.mob 0 = 1 / (u.mob 0 + (b:ℝ)) := by
    rw [← heq, mob_comp _ _ hz, readMap_mob]
  have hu := u.mapsTo hz
  have hpos : 0 < u.mob 0 + (b:ℝ) := by linarith [hu.1]
  rw [hval]
  constructor
  · rw [div_le_div_iff₀ (by linarith) hpos]
    linarith [hu.2]
  · rw [div_le_div_iff₀ hpos (by linarith)]
    linarith [hu.1]

/-! ## The unconditional half of the ledger -/

/-- **The output can never get ahead of the input.**  `d_n` is bounded below along the run, so the
image's convergent denominators never outrun the input's by more than `|det Φ|`. -/
theorem d_runState_ge (Φ : MapState) (x : ℝ) (n : ℕ) :
    Real.sqrt (|Φ.det| / 6) ≤ (runState Φ x (n + 2)).d :=
  le_trans (runState_minDen_ge Φ x n) (min_le_left _ _)

/-- **The width floor, restated as a height cap.**  For a run state, `width ≥ η` is implied by
`d ≤ R` whenever `6·|det Φ|/R² ≥ η` — so the width-frequency question is exactly
`freq{n : d_n > R} → 0`. -/
theorem width_ge_of_d_le {Φ : MapState} {x : ℝ} {n : ℕ} {R η : ℝ} (hR : 0 < R)
    (hd : (runState Φ x (n + 2)).d ≤ R) (hη : η ≤ |Φ.det| / (6 * R ^ 2)) :
    η ≤ (runState Φ x (n + 2)).width := by
  have hdpos := (runState Φ x (n + 2)).hd
  have hlow := (width_runState_bounds Φ x n).1
  have hmono : |Φ.det| / (6 * R ^ 2) ≤ |Φ.det| / (6 * (runState Φ x (n + 2)).d ^ 2) := by
    refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    nlinarith [hdpos, hd, hR]
  linarith

end MapState

section Audit

#print axioms MapState.width_bounds_of_denRatio
#print axioms MapState.width_runState_bounds
#print axioms MapState.d_comp_readMap
#print axioms MapState.d_emit
#print axioms MapState.emit_mob_zero_mem
#print axioms MapState.d_runState_ge
#print axioms MapState.width_ge_of_d_le

end Audit

end NormalNumbers.VandeheyS7
