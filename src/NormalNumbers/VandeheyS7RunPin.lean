/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RP: the run IS the coupling — the §7 front collapses to one hypothesis

The machine is built (S7-RN), it satisfies the pinned recursion (S7-RN2), it realizes the image
orbit (S7-RO), and its clock is unbounded (S7-RC3).  Assembling:

* `runClock_ratio_tendsto` — `N(n+1)/N n → 1` is a THEOREM, not a hypothesis: the one-digit
  schedule gives `N n ≤ N (n+1) ≤ N n + 1`, and `N → ∞` squeezes the ratio.
* `runBlockCoupling` — the S7-C3 coupling for the explicitly constructed sets
  `mapBlockSet (runState Φ x n) w j`.
* `orbitWordBound_of_runBlockAverage` — **the crux from a single hypothesis**: the block average
  bound for those sets.

So of S7-PN's `PinnedData`, everything except `BlockAverageBound` is now discharged, and the sets
it refers to are not existentially quantified any more but given by a definition.  That is directive
fact (α) with nothing else attached to it.
-/
import NormalNumbers.VandeheyS7RunClock

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

/-- The pullback of the `j`-th output slot, for a `MapState`. -/
def mapBlockSet (s : MapState) (w : List ℕ) (j : ℕ) : Set ℝ :=
  s.mob ⁻¹' (gaussMap^[j] ⁻¹' cfCylinder w ∩ Set.Ioo (0:ℝ) 1) ∩ Set.Ioo (0:ℝ) 1

/-- **The clock ratio is automatic.** -/
theorem runClock_ratio_tendsto (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) :
    Tendsto (fun n => ((runClock Φ x (n + 1) : ℝ)) / (runClock Φ x n : ℝ)) atTop (nhds 1) := by
  have hub := runClock_tendsto Φ hx hy hyirr
  have hstep : ∀ n, runClock Φ x (n + 1) ≤ runClock Φ x n + 1 := by
    intro n
    rw [runClock_succ]
    have := runWord_length_le_one Φ x n
    omega
  have hmono : ∀ n, runClock Φ x n ≤ runClock Φ x (n + 1) := by
    intro n; rw [runClock_succ]; omega
  have hpos : ∀ᶠ n in atTop, 0 < (runClock Φ x n : ℝ) := by
    filter_upwards [hub.eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  have hlow : ∀ᶠ n in atTop, (1:ℝ) ≤ (runClock Φ x (n + 1) : ℝ) / (runClock Φ x n : ℝ) := by
    filter_upwards [hpos] with n hn
    rw [le_div_iff₀ hn]
    have : (runClock Φ x n : ℝ) ≤ (runClock Φ x (n + 1) : ℝ) := by exact_mod_cast hmono n
    linarith
  have hhigh : ∀ᶠ n in atTop,
      (runClock Φ x (n + 1) : ℝ) / (runClock Φ x n : ℝ) ≤ 1 + 1 / (runClock Φ x n : ℝ) := by
    filter_upwards [hpos] with n hn
    rw [div_le_iff₀ hn]
    have : (runClock Φ x (n + 1) : ℝ) ≤ (runClock Φ x n : ℝ) + 1 := by exact_mod_cast hstep n
    have hrw : (1 + 1 / (runClock Φ x n : ℝ)) * (runClock Φ x n : ℝ)
        = (runClock Φ x n : ℝ) + 1 := by field_simp
    linarith [hrw]
  have htop : Tendsto (fun n => 1 + 1 / (runClock Φ x n : ℝ)) atTop (nhds 1) := by
    have h0 : Tendsto (fun n => 1 / (runClock Φ x n : ℝ)) atTop (nhds 0) := by
      have hb : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      exact hb.comp hub
    simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop hlow hhigh

/-- **The coupling, for the constructed run.** -/
theorem runBlockCoupling (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) (w : List ℕ) :
    BlockCouplingM (cfCylinder w) x (Φ.mob x) (runClock Φ x)
      (fun n j => mapBlockSet (runState Φ x n) w j) where
  base := by simp
  mono := runClock_mono Φ x
  unbounded := runClock_tendsto Φ hx hy hyirr
  couple := by
    intro n j _
    obtain ⟨hmem, -, hclock⟩ := runValue_spec Φ hx hy hyirr n
    have hval : (runState Φ x n).mob (gaussMap^[n] x) = runValue Φ x n := rfl
    have hiter : gaussMap^[runClock Φ x n + j] (Φ.mob x)
        = gaussMap^[j] (runValue Φ x n) := by
      rw [Nat.add_comm, Function.iterate_add_apply, hclock]
    constructor
    · intro hin
      rw [hiter] at hin
      exact ⟨⟨by rw [Set.mem_preimage, hval]; exact hin, by rw [hval]; exact hmem⟩, hx n⟩
    · rintro ⟨⟨h1, -⟩, -⟩
      rw [Set.mem_preimage, hval] at h1
      rw [hiter]
      exact h1

/-- **S7-RP.**  The crux, from the block average bound alone. -/
theorem orbitWordBound_of_runBlockAverage {q r₀ C : ℝ} (hC : 0 ≤ C)
    (hirr : AffineImageIrrational q r₀)
    (hΦ : ∀ x : ℝ, IsCFNormal (Int.fract x) →
      ∃ Φ : MapState, Φ.mob (Int.fract x) = Int.fract (q * x + r₀))
    (hBA : ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
      ∀ Φ : MapState, Φ.mob (Int.fract x) = Int.fract (q * x + r₀) →
      BlockAverageBound (C * (gaussMeasure (cfCylinder w)).toReal) (Int.fract x)
        (runClock Φ (Int.fract x))
        (fun n j => mapBlockSet (runState Φ (Int.fract x) n) w j)) :
    OrbitWordBound q r₀ C := by
  intro x hx w hw ε hε
  obtain ⟨Φ, hΦeq⟩ := hΦ x hx
  have hx0 : Irrational x := Literature.irrational_of_isCFNormal_fract hx
  have hxirr : Irrational (Int.fract x) := (irrational_fract_mem hx0).1
  have hxmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hx0).2
  have hxo : ∀ k, gaussMap^[k] (Int.fract x) ∈ Set.Ioo (0:ℝ) 1 :=
    fun k => (irrational_orbit _ hxirr hxmem k).2
  have hyirr0 : Irrational (q * x + r₀) := hirr x hx
  have hymem : Int.fract (q * x + r₀) ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hyirr0).2
  have hyirr : Irrational (Int.fract (q * x + r₀)) := (irrational_fract_mem hyirr0).1
  have hy : Φ.mob (Int.fract x) ∈ Set.Ioo (0:ℝ) 1 := by rw [hΦeq]; exact hymem
  have hyi : Irrational (Φ.mob (Int.fract x)) := by rw [hΦeq]; exact hyirr
  have hB : 0 ≤ C * (gaussMeasure (cfCylinder w)).toReal :=
    mul_nonneg hC ENNReal.toReal_nonneg
  have hcoup := runBlockCoupling Φ hxo hy hyi w
  rw [hΦeq] at hcoup
  exact freq_le_of_blockAverage_mono hcoup (runClock_ratio_tendsto Φ hxo hy hyi) hB
    (hBA x hx w hw Φ hΦeq) ε hε

end MapState

section Audit

#print axioms MapState.runClock_ratio_tendsto
#print axioms MapState.runBlockCoupling
#print axioms MapState.orbitWordBound_of_runBlockAverage

end Audit

end NormalNumbers.VandeheyS7
