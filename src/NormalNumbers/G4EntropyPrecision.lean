/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyDiagonal

/-!
# The quantized sample never determines an orbit value

Two facts now stand side by side:

* `exists_orbitLocal_forces_normal` (lap 19) — the **unquantized** orbit value `{2^r x}` at a
  *single* time `r` carries a hypothesis that forces binary normality;
* `qForces_normal_iff_density_one` (lap 20) — a **quantized** sampler forces normality iff its
  windows have density one.

This module joins them: a quantized sampler whose windows have density `< 1` does not determine
`{2^r x}` for **any** `r` — there are two reals in `[0,1)` with literally the same sample values
and different orbit points at time `r` (`exists_qVal_eq_orbit_ne`).

So the gap between the arithmetic sample and normality is not that the sample is too coarse to
*imply* normality; it is that the sample never pins down the object — one orbit value — that
would imply it.  The witness is minimal: flip a single unread digit.  (The two reals produced
are close when the unread position is late, so this is a statement about exact determination,
not about approximation; approximating `{2^r x}` from the sample is exactly what a sampler with
growing windows *can* do, and lap 20 shows that is still not enough.)
-/

open Filter

namespace NormalNumbers.G4Entropy

open NormalNumbers

/-- The digit sequence with a single `1`, at position `j`. -/
def spikeDigits (j : ℕ) (k : ℕ) : ℕ := if k = j then 1 else 0

lemma spikeDigits_lt (j k : ℕ) : spikeDigits j k < 2 := by
  unfold spikeDigits; split <;> omega

lemma properDigits_spike (j : ℕ) : ProperDigits 2 (spikeDigits j) := by
  intro N
  refine ⟨max N (j + 1), le_max_left _ _, ?_⟩
  unfold spikeDigits
  rw [if_neg (by omega : ¬ max N (j + 1) = j)]
  omega

/-- The real with a single `1` digit, at position `j`. -/
noncomputable def spikeReal (j : ℕ) : ℝ := realOfDigits 2 (spikeDigits j)

lemma spikeReal_mem_Ico (j : ℕ) : spikeReal j ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico 2 (by norm_num) _ (spikeDigits_lt j) (properDigits_spike j)

lemma digitOf_spikeReal (j : ℕ) :
    digitOf 2 (Int.fract (spikeReal j)) = spikeDigits j := by
  have h := spikeReal_mem_Ico j
  rw [Set.mem_Ico] at h
  rw [Int.fract_eq_self.2 h]
  exact digitOf_realOfDigits 2 (by norm_num) _ (spikeDigits_lt j) (properDigits_spike j)

lemma digitOf_zero (k : ℕ) : digitOf 2 (Int.fract (0 : ℝ)) k = 0 := by
  have : Int.fract (0 : ℝ) = 0 := by simp
  rw [this]
  unfold digitOf
  norm_num

/-- **A quantized sampler of density `< 1` determines no orbit value.**  For every time `r`
there are two reals of `[0,1)` with identical quantized sample values and different orbit
points at time `r`. -/
theorem exists_qVal_eq_orbit_ne {ι : Type*} (W : ι → ℕ × ℕ) {c : ℝ} (hc : c < 1) {L₀ : ℕ}
    (hdens : ∀ L : ℕ, L₀ ≤ L → ((((Finset.range L).filter (qRead W)).card : ℝ)) ≤ c * L)
    (r : ℕ) :
    ∃ x y : ℝ, 0 ≤ x ∧ x < 1 ∧ 0 ≤ y ∧ y < 1 ∧ qVal W x = qVal W y ∧
      orbit 2 x r ≠ orbit 2 y r := by
  obtain ⟨j, hjr, hjn⟩ :=
    exists_not_mem_of_density_eventually (S := qRead W) hc hdens r
  refine ⟨0, spikeReal j, le_rfl, by norm_num, (spikeReal_mem_Ico j).1,
    (spikeReal_mem_Ico j).2, ?_, ?_⟩
  · refine qVal_congr fun k hk => ?_
    rw [digitOf_zero, digitOf_spikeReal]
    unfold spikeDigits
    rw [if_neg (by rintro rfl; exact hjn hk)]
  · intro hEq
    have hd : digitOf 2 (orbit 2 (0:ℝ) r) (j - r) = digitOf 2 (orbit 2 (spikeReal j) r) (j - r) :=
      congrArg (fun z => digitOf 2 z (j - r)) hEq
    rw [digitOf_orbit 2 (by norm_num) 0 le_rfl r (j - r),
      digitOf_orbit 2 (by norm_num) (spikeReal j) (spikeReal_mem_Ico j).1 r (j - r)] at hd
    have hrj : r + (j - r) = j := by omega
    rw [hrj] at hd
    have h0 : digitOf 2 (0 : ℝ) j = 0 := by
      have : Int.fract (0 : ℝ) = 0 := by simp
      rw [← this]
      exact digitOf_zero j
    have h1 : digitOf 2 (spikeReal j) j = 1 := by
      have hfr : Int.fract (spikeReal j) = spikeReal j :=
        Int.fract_eq_self.2 ⟨(spikeReal_mem_Ico j).1, (spikeReal_mem_Ico j).2⟩
      have := congrFun (digitOf_spikeReal j) j
      rw [hfr] at this
      rw [this]
      unfold spikeDigits
      rw [if_pos rfl]
    rw [h0, h1] at hd
    exact absurd hd (by omega)

end NormalNumbers.G4Entropy

/-! ## The implemented schedule determines no orbit value -/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy

lemma filter_qRead_schedW (L : ℕ) :
    (Finset.range L).filter (qRead schedW) = (Finset.range L).filter IsSampled := by
  apply Finset.filter_congr
  intro j _
  simpa using qRead_schedW_iff j

/-- **The expedition's sample never pins down an orbit point.**  At every time `r` two reals of
`[0,1)` have the same quantized sample at every scale and different `{2^r ·}`.  By lap 19 that
orbit value would have forced normality; the sample loses exactly it. -/
theorem exists_sample_eq_orbit_ne (r : ℕ) :
    ∃ x y : ℝ, 0 ≤ x ∧ x < 1 ∧ 0 ≤ y ∧ y < 1 ∧ qVal schedW x = qVal schedW y ∧
      orbit 2 x r ≠ orbit 2 y r := by
  refine exists_qVal_eq_orbit_ne schedW (c := 1 / 4) (by norm_num) (L₀ := 0) ?_ r
  intro L _
  rw [filter_qRead_schedW L]
  exact card_isSampled_le_real L

end NormalNumbers.G4.Sched
