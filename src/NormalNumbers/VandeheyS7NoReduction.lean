/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-NR: the crux WITHOUT the absolute values is the headline itself

S7-RR showed the reference run is the Gauss shift, so route A's crux compares the run's local
digit statistics with the INPUT's own.  This module measures exactly how much of route A's front is
a reduction and how much is a restatement.

Two identities already in hand bound both halves of the comparison by the window length:

* `abs_slotCount_sub_sum_blockAvg_le` (S7-BF) — `|slotCount − Σ blockAvg (runState m)| ≤ T`;
* `abs_sum_blockAvg_refState_sub_blockCount_le` (S7-RV) — `|Σ blockAvg refState − blockCount| ≤ T`.

Hence the SIGNED Cesàro sum of the crux's summand is, to within `2T`, the difference of the two
counting functions (`abs_signedSum_sub_countDiff_le`), and therefore

    `signedForget_iff` :  SignedForget Φ x w  ↔  (slotCount Φ x w p − blockCount (I_w) p x)/p → 0 .

For a CF-normal input the second count has frequency `γ(I_w)`, so the right-hand side says
`slotCount Φ x w p / p → γ(I_w)` — which with the clock is exactly the conclusion route A is trying
to prove (`tendsto_slotCountFreq_gauss`, S7-RV).  **The signed crux is the headline, restated.**

So the entire surplus of route A's front over its own conclusion sits in the ABSOLUTE VALUES: the
crux asks for the two statistics to agree *locally*, time by time, and only that is more than the
headline.  Any attack on `BlockForgetAll` (S7-AW) must therefore exploit local cancellation-free
structure — a pointwise comparison of the run's window with the input's window — because the
signed version cannot be proved without proving the theorem itself.

## Guard rule

**Content locator.**  `abs_signedSum_sub_countDiff_le` is the whole content; the equivalence is
`ε`-bookkeeping with `T = 1` in the easy direction.

**Degenerate cases.**  `p = 0`: both sides vanish.  `w = []`: `blockCount (I_[]) p x = p` and the
statement becomes the clock identity of S7-CO, consistently.
-/
import NormalNumbers.VandeheyS7ArchWidthFree

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- The crux's Cesàro sum WITHOUT the absolute value inside. -/
noncomputable def signedSum (Φ : MapState) (x : ℝ) (w : List ℕ) (T p : ℕ) : ℝ :=
  ∑ m ∈ range p,
    (blockAvg (runState Φ x m) T w (gaussMap^[m] x) - blockAvg refState T w (gaussMap^[m] x))

/-- **The signed sum is the difference of the two counting functions, up to the window length.** -/
theorem abs_signedSum_sub_countDiff_le (Φ : MapState) (x : ℝ) (w : List ℕ) {T : ℕ} (hT : 0 < T)
    (p : ℕ) :
    |signedSum Φ x w T p
      - (slotCount Φ x w p - blockCount (cfCylinder w) p x)| ≤ 2 * (T : ℝ) := by
  have h1 := abs_slotCount_sub_sum_blockAvg_le Φ x w hT p
  have h2 := abs_sum_blockAvg_refState_sub_blockCount_le w hT x p
  have hsplit : signedSum Φ x w T p
      = (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x))
        - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) := by
    rw [signedSum, Finset.sum_sub_distrib]
  rw [hsplit]
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- The signed form of the crux, for one run and one word. -/
def SignedForget (Φ : MapState) (x : ℝ) (w : List ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 0 < T ∧
    ∀ᶠ p : ℕ in atTop, |signedSum Φ x w T p| ≤ ε * (p : ℝ)

/-- **S7-NR.**  The signed crux says exactly that the two counting functions have the same
frequency — i.e. it IS the headline for this run and word. -/
theorem signedForget_iff (Φ : MapState) (x : ℝ) (w : List ℕ) :
    SignedForget Φ x w ↔
      Tendsto (fun p => (slotCount Φ x w p - blockCount (cfCylinder w) p x) / (p : ℝ))
        atTop (nhds 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨T, hT, hev⟩ := h (δ / 4) (by linarith)
    have hTsmall : ∀ᶠ p : ℕ in atTop, 2 * (T : ℝ) ≤ (δ / 4) * (p : ℝ) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (2 * (T : ℝ))).eventually
        (eventually_lt_nhds (show (0:ℝ) < δ / 4 by linarith))
      filter_upwards [this, eventually_gt_atTop 0] with p hp hp0
      have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
      rw [div_lt_iff₀ hpR] at hp
      linarith
    have := (hev.and (hTsmall.and (eventually_gt_atTop 0)))
    rw [eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    refine ⟨N, fun p hp => ?_⟩
    obtain ⟨hs, hTp, hp0⟩ := hN p hp
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hb := abs_signedSum_sub_countDiff_le Φ x w hT p
    have hcd : |slotCount Φ x w p - blockCount (cfCylinder w) p x| ≤ (δ / 2) * (p : ℝ) := by
      have t := abs_add_le (signedSum Φ x w T p
        - (slotCount Φ x w p - blockCount (cfCylinder w) p x)) (signedSum Φ x w T p)
      have habs : |(slotCount Φ x w p - blockCount (cfCylinder w) p x)|
          ≤ |signedSum Φ x w T p - (slotCount Φ x w p - blockCount (cfCylinder w) p x)|
            + |signedSum Φ x w T p| := by
        have := abs_sub_abs_le_abs_sub
          (slotCount Φ x w p - blockCount (cfCylinder w) p x) (signedSum Φ x w T p)
        have h2 := abs_sub_le (slotCount Φ x w p - blockCount (cfCylinder w) p x)
          (signedSum Φ x w T p) 0
        simp only [sub_zero, abs_zero] at h2
        rw [abs_sub_comm (slotCount Φ x w p - blockCount (cfCylinder w) p x)] at h2
        linarith
      linarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpR, div_lt_iff₀ hpR]
    nlinarith
  · intro h ε hε
    refine ⟨1, one_pos, ?_⟩
    have hev := h.eventually (eventually_abs_sub_lt (0:ℝ) (show (0:ℝ) < ε / 2 by linarith))
    have hTsmall : ∀ᶠ p : ℕ in atTop, 2 * ((1:ℕ) : ℝ) ≤ (ε / 2) * (p : ℝ) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (2 * ((1:ℕ) : ℝ))).eventually
        (eventually_lt_nhds (show (0:ℝ) < ε / 2 by linarith))
      filter_upwards [this, eventually_gt_atTop 0] with p hp hp0
      have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
      rw [div_lt_iff₀ hpR] at hp
      linarith
    filter_upwards [hev, hTsmall, eventually_gt_atTop 0] with p hp hTp hp0
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
    have hb := abs_signedSum_sub_countDiff_le Φ x w one_pos p
    have hcd : |slotCount Φ x w p - blockCount (cfCylinder w) p x| ≤ (ε / 2) * (p : ℝ) := by
      rw [sub_zero, abs_div, abs_of_pos hpR, div_lt_iff₀ hpR] at hp
      linarith
    have key : |signedSum Φ x w 1 p|
        ≤ |signedSum Φ x w 1 p - (slotCount Φ x w p - blockCount (cfCylinder w) p x)|
          + |slotCount Φ x w p - blockCount (cfCylinder w) p x| := by
      calc |signedSum Φ x w 1 p|
          = |(signedSum Φ x w 1 p - (slotCount Φ x w p - blockCount (cfCylinder w) p x))
              + (slotCount Φ x w p - blockCount (cfCylinder w) p x)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hTp' : (2:ℝ) ≤ (ε / 2) * (p : ℝ) := by norm_num at hTp; linarith
    have hb' : |signedSum Φ x w 1 p - (slotCount Φ x w p - blockCount (cfCylinder w) p x)|
        ≤ 2 := by norm_num at hb; linarith
    linarith

/-- **The restatement, spelled out.**  For a CF-normal input and a genuine word the signed crux is
equivalent to the conclusion route A is after: the crux's frequency is `γ(I_w)`. -/
theorem signedForget_iff_slotCountFreq {w : List ℕ} (hne : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) :
    SignedForget Φ x w ↔
      Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder w)).toReal) := by
  have hbc := blockCount_tendsto_of_isCFNormal hx horb w hne hpos
  rw [signedForget_iff]
  constructor
  · intro h
    have := h.add hbc
    simp only [zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
    rw [← add_div, sub_add_cancel]
  · intro h
    have := h.sub hbc
    simp only [sub_self] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
    rw [← sub_div]

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.abs_signedSum_sub_countDiff_le
#print axioms NormalNumbers.VandeheyS7.MapState.signedForget_iff
#print axioms NormalNumbers.VandeheyS7.MapState.signedForget_iff_slotCountFreq

end Audit
