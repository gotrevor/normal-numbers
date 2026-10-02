/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Good

/-!
# S7-SH: the SHAPE of the state is a window function; only its LOCATION is not

Lap 56 left one obligation, `WindowedPullback`, whose decisive component is whether the
transducer's target interval is determined — to accuracy `ε` — by a bounded window of input
digits.  `no_window_function` refutes the exact version.  This module proves the exact half that
IS true, and thereby pins the wall.

## The statement

A state reading a word of length `k` acts on the future through `M ∘ Q`, where `Q` is the word's
matrix and `M` the prefix-dependent part.  `Q([0,1])` is a cylinder, of length `≤ 2/2ᵏ`.  On such
a short interval a Möbius map of bounded distortion is nearly affine:

    (M v − M u)/(M β − M α)  ≍  (v − u)/(β − α)   within a factor `1 + distortion·(β−α)`

(`mob_ratio_near_affine`).  Therefore the *relative* length of the pullback of any target — the
only thing the crux's mass estimate needs — is determined by the last `k` digits up to
`1 + O(K·2^{−k})`, uniformly over the prefix.  What is NOT determined is where inside `(0,1)` the
image sits: that is the `position` coordinate, and it is what selects the emitted digit.

## Consequence for the route

`WindowedPullback` asks for a window-determined *interval*, i.e. both coordinates.  This module
says the length coordinate is free and the location coordinate is the entire remaining content —
so any future attack must either (i) supply the location (the `Γ\SL₂(ℝ)` equidistribution wall of
directive fact γ), or (ii) restate the crux so that only relative lengths enter.  Route (ii) is
the newly visible option and is what lap 58 should test.

## Guard rule

Content locator: at `β − α = 1` the bound degenerates to `mob_ratio_comparable`, so the content is
entirely in the shortness of the interval.  Degenerate case: `distortion = 1` (the identity state)
makes the factor `1 + (β−α)`, still not `1`, because the estimate is one-sided in `c/d` only.
-/

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- **Near-affinity on a short interval.**  A Möbius state distorts relative lengths inside an
interval of length `ε` by at most a factor `1 + distortion · ε`. -/
theorem mob_ratio_near_affine (s : MobState) {α β u v : ℝ} (hα : 0 ≤ α) (hαu : α ≤ u)
    (huv : u ≤ v) (hvβ : v ≤ β) (hβ : β ≤ 1) (hlt : α < β) :
    (s.mob v - s.mob u) / (s.mob β - s.mob α)
        ≤ (v - u) / (β - α) * (1 + s.distortion * (β - α)) ∧
      (v - u) / (β - α) / (1 + s.distortion * (β - α))
        ≤ (s.mob v - s.mob u) / (s.mob β - s.mob α) := by
  have hu0 : (0:ℝ) ≤ u := le_trans hα hαu
  have hv0 : (0:ℝ) ≤ v := le_trans hu0 huv
  have hβ0 : (0:ℝ) ≤ β := le_trans hv0 hvβ
  have hpα := s.den_pos hα
  have hpβ := s.den_pos hβ0
  have hpu := s.den_pos hu0
  have hpv := s.den_pos hv0
  have hdet : s.a * s.d - s.b * s.c ≠ 0 := s.hdet
  have hβα : (0:ℝ) < β - α := by linarith
  -- the exact ratio
  have hratio : (s.mob v - s.mob u) / (s.mob β - s.mob α)
      = (v - u) / (β - α) * (((s.c * β + s.d) * (s.c * α + s.d)) /
          ((s.c * v + s.d) * (s.c * u + s.d))) := by
    rw [s.mob_sub hu0 hv0, s.mob_sub hα hβ0]
    field_simp
    try ring
  -- the bracket is between `(cα+d)/(cβ+d)` and `(cβ+d)/(cα+d)`
  have hmonoU : s.c * α + s.d ≤ s.c * u + s.d := by nlinarith [s.hc]
  have hmonoV : s.c * v + s.d ≤ s.c * β + s.d := by nlinarith [s.hc]
  have hmonoU' : s.c * u + s.d ≤ s.c * β + s.d := by nlinarith [s.hc]
  have hmonoV' : s.c * α + s.d ≤ s.c * v + s.d := by nlinarith [s.hc]
  have hdist : s.c * (β - α) ≤ s.distortion * (β - α) * s.d := by
    have hd := s.hd
    have : s.distortion * s.d = s.c + s.d := by
      rw [distortion]; field_simp
    nlinarith [s.hc, s.hd, hβα]
  have hupper : ((s.c * β + s.d) * (s.c * α + s.d)) / ((s.c * v + s.d) * (s.c * u + s.d))
      ≤ 1 + s.distortion * (β - α) := by
    rw [div_le_iff₀ (mul_pos hpv hpu)]
    have h1 : (s.c * β + s.d) * (s.c * α + s.d) ≤ (s.c * β + s.d) * (s.c * u + s.d) := by
      nlinarith
    have h2 : (s.c * β + s.d) ≤ (1 + s.distortion * (β - α)) * (s.c * v + s.d) := by
      have hvα : s.c * β + s.d ≤ (s.c * v + s.d) + s.c * (β - α) := by nlinarith [s.hc]
      have hdd : s.c * (β - α) ≤ s.distortion * (β - α) * (s.c * v + s.d) := by
        nlinarith [s.le_den hv0, s.hd]
      nlinarith
    nlinarith [hpu, hpv, hpα, hpβ]
  have hlower : 1 / (1 + s.distortion * (β - α))
      ≤ ((s.c * β + s.d) * (s.c * α + s.d)) / ((s.c * v + s.d) * (s.c * u + s.d)) := by
    have hpos : (0:ℝ) < 1 + s.distortion * (β - α) := by
      have := s.distortion_pos
      positivity
    rw [div_le_div_iff₀ hpos (mul_pos hpv hpu)]
    have h1 : (s.c * v + s.d) * (s.c * u + s.d) ≤ (s.c * β + s.d) * (s.c * β + s.d) := by
      nlinarith
    have h2 : (s.c * β + s.d) ≤ (1 + s.distortion * (β - α)) * (s.c * α + s.d) := by
      have hvα : s.c * β + s.d ≤ (s.c * α + s.d) + s.c * (β - α) := by nlinarith [s.hc]
      have hdd : s.c * (β - α) ≤ s.distortion * (β - α) * (s.c * α + s.d) := by
        nlinarith [s.le_den hα, s.hd]
      nlinarith
    nlinarith [hpα, hpβ, hpu, hpv]
  have hfrac0 : (0:ℝ) ≤ (v - u) / (β - α) := by
    apply div_nonneg (by linarith) hβα.le
  have hpos : (0:ℝ) < 1 + s.distortion * (β - α) := by
    have := s.distortion_pos; positivity
  constructor
  · rw [hratio]
    exact mul_le_mul_of_nonneg_left hupper hfrac0
  · rw [hratio, div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hlower hfrac0
    calc (v - u) / (β - α)
        = (v - u) / (β - α) * (1 / (1 + s.distortion * (β - α))) *
            (1 + s.distortion * (β - α)) := by
          rw [mul_assoc, one_div, inv_mul_cancel₀ hpos.ne', mul_one]
      _ ≤ (v - u) / (β - α) * (((s.c * β + s.d) * (s.c * α + s.d)) /
            ((s.c * v + s.d) * (s.c * u + s.d))) * (1 + s.distortion * (β - α)) := by
          exact mul_le_mul_of_nonneg_right this hpos.le

/-- The uniform form: a distortion bound `K` makes the shape error depend only on the length of
the interval the recent word produces. -/
theorem mob_ratio_near_affine_le (s : MobState) {K α β u v : ℝ} (hK : s.distortion ≤ K)
    (hα : 0 ≤ α) (hαu : α ≤ u) (huv : u ≤ v) (hvβ : v ≤ β) (hβ : β ≤ 1) (hlt : α < β) :
    (s.mob v - s.mob u) / (s.mob β - s.mob α) ≤ (v - u) / (β - α) * (1 + K * (β - α)) := by
  refine (s.mob_ratio_near_affine hα hαu huv hvβ hβ hlt).1.trans ?_
  have hfrac0 : (0:ℝ) ≤ (v - u) / (β - α) := div_nonneg (by linarith) (by linarith)
  have : 1 + s.distortion * (β - α) ≤ 1 + K * (β - α) := by
    have : s.distortion * (β - α) ≤ K * (β - α) :=
      mul_le_mul_of_nonneg_right hK (by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left this hfrac0

end MobState

/-- The window error vanishes: a cylinder of depth `k` has length `≤ 2/2ᵏ`, so a state of
distortion `≤ K` reading it distorts relative lengths by `1 + 2K/2ᵏ → 1`.  **This is the precise
sense in which the SHAPE of the state is a window function.** -/
theorem tendsto_windowShapeError (K : ℝ) :
    Filter.Tendsto (fun k : ℕ => 1 + K * (2 / 2 ^ k)) Filter.atTop (nhds 1) := by
  have hhalf : Filter.Tendsto (fun k : ℕ => ((1:ℝ)/2) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h : Filter.Tendsto (fun k : ℕ => (2:ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
    have := (tendsto_const_nhds (X := ℝ) (x := (2:ℝ)) (f := Filter.atTop (α := ℕ))).mul hhalf
    simpa [div_pow, one_div, div_eq_mul_inv, mul_comm] using this
  simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop (α := ℕ))).add
    ((tendsto_const_nhds (x := K)).mul h)

namespace MobState

end MobState

section Audit

#print axioms MobState.mob_ratio_near_affine
#print axioms MobState.mob_ratio_near_affine_le
#print axioms tendsto_windowShapeError

end Audit

end NormalNumbers.VandeheyS7
