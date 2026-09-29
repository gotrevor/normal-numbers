/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-NR: nearby states have nearby maps — step 1 of the finite-cell decomposition

Fact (δ) (S7-BX) puts the run's states of width `≥ η` in a fixed box of `ℝ⁴`.  To USE a finite
`ρ`-net of that box, one needs the map `s ↦ s.mob` to be Lipschitz in the matrix entries, uniformly
over the states that occur.  That is this module, and — the surprise — **the width floor is not
needed for it**:

* `det_le_den_mul` — `|det| ≤ d·(c+d)`, from `width ≤ 1` (S7-CM) and `width_eq`.
* `minDen_sq_ge` — hence `d·(c+d) = |det|/width ≥ |det|`, and with `denRatio ∈ [1/K, K]` that gives
  `minDen² ≥ |det|/K`.  **A lower bound on the denominators from the distortion band alone.**
* `abs_mob_sub_le_of_entries` — if two states agree entrywise to `ρ` then their maps agree to
  `4ρ / minDen` on `[0,1]`.  The proof is the single algebraic identity
  `N_s D_t − N_t D_s = (N_s − N_t) D_t + N_t (D_t − D_s)` together with `0 ≤ N_t ≤ D_t`, which is
  exactly the `MapState` interval condition.
* `preimage_subset_cthickening` — so a pullback moves into a `δ`-thickening of the target.
* `runState_minDen_ge`, `abs_mob_sub_runState_le` — the run form: from step 2 on,
  `minDen ≥ √(|det Φ|/6)` *unconditionally*, so states within `ρ` have maps within
  `4ρ·√(6/|det Φ|)`.

Together with S7-BX this says: the map `n ↦ (runState Φ x n).mob` factors, to precision `ε`,
through a FINITE set — on the times when the width is at least `η`.  The width floor buys the
box; the distortion band buys the modulus of continuity, and it is free.
-/
import NormalNumbers.VandeheyS7Box

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-- The product of the two denominators is at least `|det|` — no hypothesis at all. -/
theorem det_le_den_mul (s : MapState) : |s.det| ≤ s.d * (s.c + s.d) := by
  have hpos : (0:ℝ) < s.d * (s.c + s.d) := mul_pos s.hd s.hcd
  have hw := s.width_le_one
  rw [width_eq, div_le_one hpos] at hw
  exact hw

/-- **The denominators are bounded BELOW by the distortion band alone.** -/
theorem minDen_sq_ge {s : MapState} {K : ℝ} (hK : 0 < K)
    (hr : s.denRatio ≤ K) (hr' : 1 / K ≤ s.denRatio) :
    |s.det| / K ≤ s.minDen ^ 2 := by
  have hd := s.hd
  have hcd := s.hcd
  have hkey := s.det_le_den_mul
  -- `c+d ≤ K d` and `d ≤ K (c+d)`
  have h1 : s.c + s.d ≤ K * s.d := by
    have := s.c_add_d_eq
    rw [this]; exact mul_le_mul_of_nonneg_right hr hd.le
  have h2 : s.d ≤ K * (s.c + s.d) := by
    have hc := s.c_add_d_eq
    have hle : 1 / K * s.d ≤ s.denRatio * s.d := mul_le_mul_of_nonneg_right hr' hd.le
    rw [← hc] at hle
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK] at hle
    linarith
  have hdsq : |s.det| / K ≤ s.d ^ 2 := by
    rw [div_le_iff₀ hK]
    nlinarith [hkey, h1, hd, hcd]
  have hcdsq : |s.det| / K ≤ (s.c + s.d) ^ 2 := by
    rw [div_le_iff₀ hK]
    nlinarith [hkey, h2, hd, hcd]
  rcases min_cases s.d (s.c + s.d) with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [minDen, hm]
  · exact hdsq
  · exact hcdsq

/-! ## Nearby entries, nearby maps -/

/-- **The modulus of continuity in the matrix entries.**  Two states agreeing entrywise to `ρ`
have maps agreeing to `4ρ / minDen` on `[0,1]`. -/
theorem abs_mob_sub_le_of_entries {s t : MapState} {ρ z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (ha : |s.a - t.a| ≤ ρ) (hb : |s.b - t.b| ≤ ρ) (hc : |s.c - t.c| ≤ ρ) (hd : |s.d - t.d| ≤ ρ) :
    |s.mob z - t.mob z| ≤ 4 * ρ / s.minDen := by
  have hρ : 0 ≤ ρ := le_trans (abs_nonneg _) ha
  have hz0 := hz.1
  have hz1 := hz.2
  have hDs : 0 < s.c * z + s.d := s.den_pos hz
  have hDt : 0 < t.c * z + t.d := t.den_pos hz
  have hNt0 : 0 ≤ t.a * z + t.b := t.num_nonneg hz
  have hNtD : t.a * z + t.b ≤ t.c * z + t.d := t.num_le_den hz
  have key : s.mob z - t.mob z
      = ((s.a * z + s.b) * (t.c * z + t.d) - (t.a * z + t.b) * (s.c * z + s.d))
        / ((s.c * z + s.d) * (t.c * z + t.d)) := by
    rw [mob, mob, div_sub_div _ _ hDs.ne' hDt.ne']
    congr 1
    ring
  have hid : (s.a * z + s.b) * (t.c * z + t.d) - (t.a * z + t.b) * (s.c * z + s.d)
      = ((s.a - t.a) * z + (s.b - t.b)) * (t.c * z + t.d)
        + (t.a * z + t.b) * ((t.c - s.c) * z + (t.d - s.d)) := by ring
  have hA : |(s.a - t.a) * z + (s.b - t.b)| ≤ 2 * ρ := by
    calc |(s.a - t.a) * z + (s.b - t.b)| ≤ |(s.a - t.a) * z| + |s.b - t.b| := abs_add_le _ _
      _ = |s.a - t.a| * |z| + |s.b - t.b| := by rw [abs_mul]
      _ ≤ ρ * 1 + ρ := by
          have hzabs : |z| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
          exact add_le_add (mul_le_mul ha hzabs (abs_nonneg _) hρ) hb
      _ = 2 * ρ := by ring
  have hB : |(t.c - s.c) * z + (t.d - s.d)| ≤ 2 * ρ := by
    calc |(t.c - s.c) * z + (t.d - s.d)| ≤ |(t.c - s.c) * z| + |t.d - s.d| := abs_add_le _ _
      _ = |t.c - s.c| * |z| + |t.d - s.d| := by rw [abs_mul]
      _ ≤ ρ * 1 + ρ := by
          have hzabs : |z| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
          have hc' : |t.c - s.c| ≤ ρ := by rwa [abs_sub_comm]
          have hd' : |t.d - s.d| ≤ ρ := by rwa [abs_sub_comm]
          exact add_le_add (mul_le_mul hc' hzabs (abs_nonneg _) hρ) hd'
      _ = 2 * ρ := by ring
  have hnum : |(s.a * z + s.b) * (t.c * z + t.d) - (t.a * z + t.b) * (s.c * z + s.d)|
      ≤ 4 * ρ * (t.c * z + t.d) := by
    rw [hid]
    calc |((s.a - t.a) * z + (s.b - t.b)) * (t.c * z + t.d)
            + (t.a * z + t.b) * ((t.c - s.c) * z + (t.d - s.d))|
        ≤ |((s.a - t.a) * z + (s.b - t.b)) * (t.c * z + t.d)|
          + |(t.a * z + t.b) * ((t.c - s.c) * z + (t.d - s.d))| := abs_add_le _ _
      _ = |(s.a - t.a) * z + (s.b - t.b)| * (t.c * z + t.d)
          + (t.a * z + t.b) * |(t.c - s.c) * z + (t.d - s.d)| := by
          rw [abs_mul, abs_mul, abs_of_pos hDt, abs_of_nonneg hNt0]
      _ ≤ 2 * ρ * (t.c * z + t.d) + (t.c * z + t.d) * (2 * ρ) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hA hDt.le)
            (mul_le_mul hNtD hB (abs_nonneg _) hDt.le)
      _ = 4 * ρ * (t.c * z + t.d) := by ring
  have hmin : s.minDen ≤ s.c * z + s.d := s.minDen_le hz
  rw [key, abs_div, abs_of_pos (mul_pos hDs hDt)]
  rw [div_le_div_iff₀ (mul_pos hDs hDt) s.minDen_pos]
  have h1 := mul_le_mul_of_nonneg_right hnum s.minDen_pos.le
  have h2 := mul_le_mul_of_nonneg_left hmin
    (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * ρ) hDt.le)
  linarith [h1, h2]

/-- A pullback under a nearby state lands in a thickening of the target. -/
theorem preimage_subset_cthickening {s t : MapState} {ρ : ℝ}
    (ha : |s.a - t.a| ≤ ρ) (hb : |s.b - t.b| ≤ ρ) (hc : |s.c - t.c| ≤ ρ) (hd : |s.d - t.d| ≤ ρ)
    (A : Set ℝ) :
    s.mob ⁻¹' A ∩ Icc (0:ℝ) 1 ⊆ t.mob ⁻¹' (Metric.cthickening (4 * ρ / s.minDen) A) := by
  rintro z ⟨hzA, hz⟩
  have hdist : dist (t.mob z) (s.mob z) ≤ 4 * ρ / s.minDen := by
    rw [Real.dist_eq, abs_sub_comm]
    exact abs_mob_sub_le_of_entries hz ha hb hc hd
  exact Metric.mem_cthickening_of_dist_le _ _ _ _ hzA hdist

/-! ## The run form -/

/-- **From step 2 on the denominators of the run are bounded below** — unconditionally. -/
theorem runState_minDen_ge (Φ : MapState) (x : ℝ) (n : ℕ) :
    Real.sqrt (|Φ.det| / 6) ≤ (runState Φ x (n + 2)).minDen := by
  have hband : (runState Φ x (n + 2)).denRatio ≤ 6 := denRatio_runState_le_six Φ x n
  have hband' : (1:ℝ) / 6 ≤ (runState Φ x (n + 2)).denRatio := by
    have h := half_lt_denRatio_runState_succ Φ x (n + 1)
    linarith
  have hsq := minDen_sq_ge (show (0:ℝ) < 6 by norm_num) hband hband'
  rw [absDet_runState Φ x (n + 2)] at hsq
  have hpos := (runState Φ x (n + 2)).minDen_pos
  have hnn : 0 ≤ |Φ.det| / 6 := by positivity
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (|Φ.det| / 6), hsq, hpos]

/-- **The run's modulus of continuity.**  From step 2 on, a state entrywise within `ρ` of any
`MapState` `t` has its map within `4ρ·√(6/|det Φ|)` of `t`'s. -/
theorem abs_mob_sub_runState_le {Φ : MapState} (hΦ : Φ.det ≠ 0) (x : ℝ) (n : ℕ) {t : MapState}
    {ρ z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (ha : |(runState Φ x (n + 2)).a - t.a| ≤ ρ) (hb : |(runState Φ x (n + 2)).b - t.b| ≤ ρ)
    (hc : |(runState Φ x (n + 2)).c - t.c| ≤ ρ) (hd : |(runState Φ x (n + 2)).d - t.d| ≤ ρ) :
    |(runState Φ x (n + 2)).mob z - t.mob z| ≤ 4 * ρ / Real.sqrt (|Φ.det| / 6) := by
  have hρ : 0 ≤ ρ := le_trans (abs_nonneg _) ha
  have hlow := runState_minDen_ge Φ x n
  have hspos : 0 < Real.sqrt (|Φ.det| / 6) := Real.sqrt_pos.mpr (by positivity)
  refine le_trans (abs_mob_sub_le_of_entries hz ha hb hc hd) ?_
  exact div_le_div_of_nonneg_left (by linarith) hspos hlow

end MapState

section Audit

#print axioms MapState.det_le_den_mul
#print axioms MapState.minDen_sq_ge
#print axioms MapState.abs_mob_sub_le_of_entries
#print axioms MapState.preimage_subset_cthickening
#print axioms MapState.runState_minDen_ge
#print axioms MapState.abs_mob_sub_runState_le

end Audit

end NormalNumbers.VandeheyS7
