/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RV: the architecture's constant IS `γ(I_w)`, and `RefCesaro` is not needed

S7-RR computed the reference run: `pairStep (refState, z) = (refState, gaussMap z)`, so
`blockAvg refState T w z` is the empirical `w`-frequency of the first `T` digits of `z`.  Summing
that over the orbit of `x` telescopes into the ordinary block count, up to the window length:

    |∑_{m<p} blockAvg refState T w (Gᵐx) − blockCount (I_w) p x| ≤ T.

So for a CF-normal `x` the reference Cesàro average converges — to `γ(I_w)`, for EVERY `T`.  Three
consequences.

* `refCesaro_value` — `RefCesaro`'s existential constant is `γ(I_w)`; the S7-RC machinery
  (`refLevel`, relative equidistribution, the level limits) proved existence the hard way, and the
  value now comes for free from S7-RR.  `RefCesaro w` itself re-proves in two lines.
* `abs_slotCountFreq_sub_gauss_le` — the architecture theorem with the constant IDENTIFIED and
  `RefCesaro` DROPPED from its hypotheses: `BlockForgetRun` plus an affordable width floor put the
  crux's frequency within `4ε` of `γ(I_w)`.
* `tendsto_slotCountFreq_gauss` — hence the crux's frequency converges to `γ(I_w)` exactly.  That
  is stronger than `exists_uniform_slotCountFreq` (which only got SOME common constant) and is the
  shape `SampledUniformCount` wants: the value, not just universality.

## Guard rule

**Content locator.**  The only inequality is the window shift `abs_sum_shift_sub_le` (S7-BF),
applied `T` times and divided by `T`; everything else is S7-RR's identity.  With `T = 1` the
bound is `≤ 1` and the statement is `blockAvg refState 1 w z = blockIndic (I_w) z`.

**Degenerate cases.** `w = []` is excluded (`γ(I_{[]})` is `1` and `blockCount` counts every time,
so the identity still holds, but `IsCFNormal` says nothing at the empty word).  `T = 0`: both
sides are `0` and the bound reads `≤ 0`.
-/
import NormalNumbers.VandeheyS7RefRun
import NormalNumbers.VandeheyS7RefCesaro
import NormalNumbers.VandeheyS7WindowFreq

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## The reference Cesàro sum is the block count -/

/-- **The reference Cesàro sum telescopes.**  Summing the reference block average along the orbit
recovers the ordinary block count, up to the window length. -/
theorem abs_sum_blockAvg_refState_sub_blockCount_le (w : List ℕ) {T : ℕ} (hT : 0 < T) (x : ℝ)
    (p : ℕ) :
    |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x))
      - blockCount (cfCylinder w) p x| ≤ (T : ℝ) := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  set f : ℕ → ℝ := fun n => blockIndic (cfCylinder w) (gaussMap^[n] x) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => blockIndic_nonneg _ _
  have hf1 : ∀ n, f n ≤ 1 := by
    intro n
    rw [hf, blockIndic]
    by_cases hm : gaussMap^[n] x ∈ cfCylinder w
    · simp [Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hm]
  have hshiftpt : ∀ m j : ℕ, blockIndic (cfCylinder w) (gaussMap^[j] (gaussMap^[m] x)) = f (m + j) := by
    intro m j
    rw [hf, ← Function.iterate_add_apply, Nat.add_comm j m]
  have hsum : ∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)
      = (∑ j ∈ range T, ∑ m ∈ range p, f (m + j)) / T := by
    have hswap : (∑ j ∈ range T, ∑ m ∈ range p, f (m + j))
        = ∑ m ∈ range p, ∑ j ∈ range T, f (m + j) := Finset.sum_comm
    rw [hswap, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [blockAvg_refState]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hshiftpt m j
  have hbc : blockCount (cfCylinder w) p x = ∑ n ∈ range p, f n := blockCount_apply _ _ _
  have hkey : (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x))
      - blockCount (cfCylinder w) p x
      = (∑ j ∈ range T, (∑ m ∈ range p, f (m + j) - ∑ n ∈ range p, f n)) / T := by
    rw [hsum, hbc, Finset.sum_sub_distrib, sub_div]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    field_simp
  rw [hkey, abs_div, abs_of_pos hTR, div_le_iff₀ hTR]
  calc |∑ j ∈ range T, (∑ m ∈ range p, f (m + j) - ∑ n ∈ range p, f n)|
      ≤ ∑ j ∈ range T, |∑ m ∈ range p, f (m + j) - ∑ n ∈ range p, f n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range T, (T : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine (abs_sum_shift_sub_le hf0 hf1 p j).trans ?_
        exact_mod_cast (Finset.mem_range.1 hj).le
    _ = (T : ℝ) * T := by simp

/-- **The reference Cesàro limit, with its value.** -/
theorem tendsto_cesaro_blockAvg_refState {w : List ℕ} {T : ℕ} (hT : 0 < T) {x : ℝ}
    (hbc : Tendsto (fun p => blockCount (cfCylinder w) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal)) :
    Tendsto (fun p => (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal) := by
  have hdiff : Tendsto (fun p : ℕ =>
      (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)
        - blockCount (cfCylinder w) p x / (p : ℝ)) atTop (nhds 0) := by
    have hb : ∀ p : ℕ, |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)
        - blockCount (cfCylinder w) p x / (p : ℝ)| ≤ (T : ℝ) / (p : ℝ) := by
      intro p
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp
      · have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp
        rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_div_iff_of_pos_right hpR]
        exact abs_sum_blockAvg_refState_sub_blockCount_le w hT x p
    refine squeeze_zero_norm hb ?_
    exact tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  have := hdiff.add hbc
  simpa using this

/-- **`RefCesaro`'s constant is `γ(I_w)`.**  The S7-RC existence proof is superseded for genuine
words: the value is forced. -/
theorem refCesaro_value {w : List ℕ} (hne : w ≠ []) (hpos : ∀ a ∈ w, 1 ≤ a) {T : ℕ} (hT : 0 < T)
    {x : ℝ} (hx : IsCFNormal x) (horb : ∀ k : ℕ, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) {L : ℝ}

    (hL : Tendsto (fun p => (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ))
      atTop (nhds L)) : L = (gaussMeasure (cfCylinder w)).toReal :=
  tendsto_nhds_unique hL
    (tendsto_cesaro_blockAvg_refState hT (blockCount_tendsto_of_isCFNormal hx horb w hne hpos))

/-! ## The architecture, with the constant identified and `RefCesaro` dropped -/

/-- **The architecture theorem, sharpened.**  No `RefCesaro` hypothesis and no anonymous constant:
`BlockForgetRun` plus an affordable width floor put the crux's frequency within `4ε` of the Gauss
mass of the cylinder. -/
theorem abs_slotCountFreq_sub_gauss_le {w : List ℕ}
    (hBF : BlockForgetRun w) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hbc : Tendsto (fun p => blockCount (cfCylinder w) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal))
    (hbad : WidthBadFreq Φ x η ε) :
    ∀ᶠ p : ℕ in atTop,
      |slotCount Φ x w p / (p : ℝ) - (gaussMeasure (cfCylinder w)).toReal| ≤ 4 * ε := by
  classical
  obtain ⟨T, hT, hfor⟩ := hBF ε hε η hη
  set γw := (gaussMeasure (cfCylinder w)).toReal with hγ
  have hrun := hfor Φ x hx horb
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have hA : ∀ᶠ p : ℕ in atTop, (T : ℝ) / (p : ℝ) ≤ ε := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually (eventually_lt_nhds hε)
    filter_upwards [this] with p hp using hp.le
  have hB := (tendsto_cesaro_blockAvg_refState hT hbc).eventually
    (eventually_abs_sub_lt γw hε)
  filter_upwards [hA, hB, hbad, hrun, eventually_gt_atTop 0] with p hA' hB' hbad' hrun' hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have h1 : |slotCount Φ x w p / (p : ℝ)
      - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)| ≤ ε := by
    have hid := abs_slotCount_sub_sum_blockAvg_le Φ x w hT p
    have hTp : (T:ℝ) ≤ ε * (p:ℝ) := by rw [div_le_iff₀ hpR] at hA'; exact hA'
    rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR]
    linarith
  have h2 : |(∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
      - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)| ≤ 2 * ε := by
    rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    set g : ℕ → ℝ := fun m => |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
      - blockAvg refState T w (gaussMap^[m] x)| with hg
    have hsplit := Finset.sum_filter_add_sum_filter_not (range p)
      (fun m => (runState Φ x m).width < η) g
    have hbadpart : ∑ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m
        ≤ (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ) := by
      have hone : ∀ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m ≤ 1 := by
        intro m _
        have h0 := blockAvg_nonneg (runState Φ x m) T w (gaussMap^[m] x)
        have h1' := blockAvg_le_one (runState Φ x m) hT w (gaussMap^[m] x)
        have h0' := blockAvg_nonneg refState T w (gaussMap^[m] x)
        have h1'' := blockAvg_le_one refState hT w (gaussMap^[m] x)
        rw [hg, abs_le]
        constructor <;> linarith
      calc ∑ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m
          ≤ ∑ _m ∈ (range p).filter (fun m => (runState Φ x m).width < η), (1:ℝ) :=
            Finset.sum_le_sum hone
        _ = (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ) := by simp
    calc ∑ m ∈ range p, g m
        = ∑ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m
          + ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η), g m := hsplit.symm
      _ ≤ ε * (p:ℝ) + ε * (p:ℝ) := by
          have := hbad'
          linarith [hbadpart, hrun']
      _ = 2 * ε * (p : ℝ) := by ring
  have h3 : |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - γw| ≤ ε := hB'.le
  calc |slotCount Φ x w p / (p : ℝ) - γw|
      ≤ |slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)|
        + |(∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)|
        + |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - γw| := by
        have t1 := abs_add_le (slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ))
          ((∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ))
        have t2 := abs_add_le ((slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)))
          ((∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - γw)
        simp only [sub_add_sub_cancel] at t1 t2
        linarith
    _ ≤ ε + 2 * ε + ε := by linarith
    _ = 4 * ε := by ring

/-- **S7-RV, the sharpened route-A architecture.**  `BlockForgetRun` + an affordable width floor
give the crux's frequency EXACTLY: it converges to `γ(I_w)`, for every CF-normal input and every
map.  No cited input, no `RefCesaro`, no anonymous constant. -/
theorem tendsto_slotCountFreq_gauss {w : List ℕ}
    (hBF : BlockForgetRun w) (Φ : MapState) {x : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hbc : Tendsto (fun p => blockCount (cfCylinder w) p x / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal)) (hwf : WidthAfford Φ x) :
    Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder w)).toReal) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨η, hη, -, hbad⟩ := hwf (δ / 8) (by linarith)
  have h := abs_slotCountFreq_sub_gauss_le hBF (show (0:ℝ) < δ / 8 by linarith) hη
    Φ hx horb hbc hbad
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun p hp => ?_⟩
  have := hN p hp
  rw [Real.dist_eq]
  linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.abs_sum_blockAvg_refState_sub_blockCount_le
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_cesaro_blockAvg_refState
#print axioms NormalNumbers.VandeheyS7.MapState.abs_slotCountFreq_sub_gauss_le
#print axioms NormalNumbers.VandeheyS7.MapState.tendsto_slotCountFreq_gauss

end Audit
