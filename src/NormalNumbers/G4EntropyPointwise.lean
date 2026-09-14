/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyJointFree
import NormalNumbers.G4EntropyControl

/-!
# The averaging is necessary: no pointwise (`ℓ^∞`) `t`-wise bound

Every endpoint of the joint ladder —

* `tendsto_occursCountJoint_primeLambertFour` (one common aligned position),
* `tendsto_occursCountJointPos_primeLambertFour` (a fixed offset vector, aligned shifts),
* `tendsto_occursCountJointUniform_primeLambertFour` (all aligned vectors, averaged),
* `tendsto_occursCountJointFree_primeLambertFour` (all vectors, averaged)

— is an **`ℓ¹` statement**: it bounds an *average* of deviations over the sampled positions.
The natural strengthening is the `ℓ^∞` form: *for each fixed* position vector, the frequency
tends to `2^{−ℓt}`.  This module shows that strengthening is **false at the abstract layer**,
and therefore cannot be obtained from the capacity hypothesis by any sharpening of the
estimates.

The witness is the uniform law on the box `∏_α lowHalf m` — every window's leading bit forced
to `0`, everything else uniform.  Its entropy is exactly `|A|(m − 1)`, i.e. a deficit of
`Δ = |A|`: **one bit per window**, vastly less than the schedule's `Δ = 50√K·|Atom|`.  Yet at
the fixed position vector `pv ≡ 0` the all-ones pattern has probability `0` instead of
`2^{−t}` — the largest possible deviation — in *every* block simultaneously.

So the averaging in `abs_uniPosFreq_sub_le` is not an artefact of the proof: an `o(1)` bound at
a fixed position vector is inconsistent with the premise those theorems are proved from.  This
is the `t`-wise, joint-law form of `entropy_rate_not_control_bit` (`G4EntropyControl`), which
made the same point for a single window.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers Real

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The box of window vectors all of whose windows have leading bit `0`. -/
noncomputable def lowBox (A : Type*) [Fintype A] [DecidableEq A] (m : ℕ) :
    Finset (A → Fin (2 ^ m)) :=
  Fintype.piFinset (fun _ : A => lowHalf m)

lemma mem_lowBox {m : ℕ} (z : A → Fin (2 ^ m)) :
    z ∈ lowBox A m ↔ ∀ α, z α ∈ lowHalf m := by
  rw [lowBox, Fintype.mem_piFinset]

lemma card_lowBox {m : ℕ} (hm : 1 ≤ m) :
    (lowBox A m).card = (2 ^ (m - 1)) ^ (Fintype.card A) := by
  rw [lowBox, Fintype.card_piFinset]
  simp [card_lowHalf hm]

lemma lowBox_nonempty {m : ℕ} (hm : 1 ≤ m) : (lowBox A m).Nonempty := by
  rw [← Finset.card_pos, card_lowBox hm]
  positivity

/-- **The entropy of the box law is exactly `|A|(m − 1)`** — a deficit of one bit per window. -/
theorem H₂_uniformOn_lowBox {m : ℕ} (hm : 1 ≤ m) :
    (uniformOn (lowBox A m) (lowBox_nonempty hm)).H₂
      = (Fintype.card A : ℝ) * ((m : ℝ) - 1) := by
  rw [H₂_uniformOn, card_lowBox hm]
  rw [show (((2 ^ (m - 1)) ^ (Fintype.card A) : ℕ) : ℝ)
      = (2 : ℝ) ^ ((m - 1) * Fintype.card A) by push_cast; rw [← pow_mul]]
  rw [Real.logb_pow]
  have h2 : Real.logb 2 2 = 1 := by simp
  rw [h2, mul_one]
  push_cast [Nat.cast_sub hm]
  ring

/-- The leading bit of a low-half block is `0`. -/
lemma posAt_one_zero_of_mem_lowHalf {m : ℕ} (hm : 1 ≤ m) {z : Fin (2 ^ m)}
    (hz : z ∈ lowHalf m) : posAt m 1 0 z = (0 : Fin (2 ^ 1)) := by
  rw [lowHalf, Finset.mem_filter] at hz
  refine Fin.ext ?_
  rw [posAt_val]
  have h : (z : ℕ) / 2 ^ (m - 0 - 1) = 0 := Nat.div_eq_of_lt (by simpa using hz.2)
  simp only [Nat.sub_zero] at h
  simp [h]

/-- **The pointwise refutation.**  For every `m ≥ 1`, every `t ≥ 1` and every blocking, there is
a law on the window vectors whose entropy deficit is only `|A|` bits — one per window — at which
the all-ones `t`-wise pattern, read at the fixed position vector `pv ≡ 0`, has probability `0`
in **every** block, against its uniform value `2^{−t}`. -/
theorem exists_deficit_law_pointwise_zero {m t : ℕ} (hm : 1 ≤ m) (ht : 0 < t)
    (blk : B → Fin t → A) :
    ∃ L : FinLaw (A → Fin (2 ^ m)),
      (m : ℝ) * (Fintype.card A : ℝ) - (Fintype.card A : ℝ) ≤ L.H₂ ∧
      ∀ b : B, (L.map (pvPat m 1 t blk b (fun _ => 0))).prob
          {packFin t 1 (fun _ => (1 : Fin (2 ^ 1)))} = 0 := by
  classical
  refine ⟨uniformOn (lowBox A m) (lowBox_nonempty hm), ?_, ?_⟩
  · rw [H₂_uniformOn_lowBox hm]; ring_nf; exact le_rfl
  · intro b
    rw [FinLaw.prob_singleton_map]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [Finset.mem_filter] at hz
    rw [uniformOn_p, if_neg]
    intro hmem
    -- on the box, every leading bit is `0`, so the pattern is the all-zeros word
    have hzero : pvPat m 1 t blk b (fun _ => 0) z
        = packFin t 1 (fun _ => (0 : Fin (2 ^ 1))) := by
      rw [pvPat]
      exact congrArg (packFin t 1)
        (funext fun s => posAt_one_zero_of_mem_lowHalf hm ((mem_lowBox z).1 hmem _))
    have hne : packFin t 1 (fun _ => (0 : Fin (2 ^ 1)))
        ≠ packFin t 1 (fun _ => (1 : Fin (2 ^ 1))) := by
      intro h
      have := congrFun ((packFin t 1).injective h) ⟨0, ht⟩
      exact absurd this (by decide)
    exact hne (hzero ▸ hz.2)

/-- **No `ℓ^∞` bound follows from the deficit hypothesis.**  The deviation at a fixed position
vector can be the maximum possible, `2^{−t}`, under a deficit of one bit per window — so a
fortiori under the schedule's much larger deficit.  Every bound in the joint ladder must
therefore average over positions. -/
theorem no_pointwise_bound_from_deficit {m t : ℕ} (hm : 1 ≤ m) (ht : 0 < t)
    (blk : B → Fin t → A) {Δ : ℝ} (hΔ : (Fintype.card A : ℝ) ≤ Δ) :
    ∃ L : FinLaw (A → Fin (2 ^ m)),
      (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂ ∧
      ∀ b : B, |(L.map (pvPat m 1 t blk b (fun _ => 0))).prob
            {packFin t 1 (fun _ => (1 : Fin (2 ^ 1)))} - 1 / (2 : ℝ) ^ (1 * t)|
          = 1 / (2 : ℝ) ^ (1 * t) := by
  obtain ⟨L, hH, hz⟩ := exists_deficit_law_pointwise_zero (A := A) (B := B) hm ht blk
  refine ⟨L, le_trans (by linarith) hH, fun b => ?_⟩
  rw [hz b, zero_sub, abs_neg, abs_of_pos (by positivity)]

end NormalNumbers.G4Entropy
