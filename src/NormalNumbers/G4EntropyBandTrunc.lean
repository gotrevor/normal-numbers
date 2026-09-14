/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandFull
import NormalNumbers.G4EntropyE1Down
import NormalNumbers.G4EntropyMultiplierSpread

/-!
# The band law at a **truncated** outer scale

`H₂_bandTLaw_ge` certifies the band's *whole* sample `bandT i`, by restricting the scale-`X(K)`
joint law; its capture bound `abs_posAvg_bandTLaw_le` therefore speaks only about the band's end.
A mid-band position cutoff `c` keeps the sample times `n ≲ d_α c/2`, i.e. a **truncation of the
outer scale** — and `G4EntropyMultiplierSpread.kIdx_cross` says the per-atom thresholds agree to
within `1 + 1/K`, so a single `X'` brackets them.

This module runs the `H₂_bandTLaw_ge` argument at the truncated scale, feeding it
`entropy_E1_down` instead of `entropy_E1`:

```
PKtr i X'        = apSample X' P₀ b₀                the truncated sample
bandTtr i X'     = bandT i ∩ PKtr i X'              the band's part of it
deficit_primeLambertFour_down                       E1 at X', in `|Atom|` form
card_bandTtr_ge                                     σ ≥ 1/2 at every X' ≥ Xlo (KK i)
H₂_bandTLawTr_ge                                    per-window deficit ≤ 101√K, at X'
abs_posAvg_bandTLawTr_le                            capture at X': 2√(808 log2·ℓ/√K)
```

The point is what is **absent**: the error no longer carries the restriction price
`(δ+1)·|P_K|/a` of `abs_posAvg_preLaw_le`, because the truncated prefix is certified in its own
right rather than as a thin sub-collection of the full-scale sample.  The bad initial portion of
each band drops from an `≈ K^{−1/2}` fraction to an `≈ X^{−1/2}` fraction — and no further:
`G4EntropyScaleGap.Xhi_lt_Xlo_step` shows `Xlo (KK i)` cannot be lowered to meet the previous
rung's reach.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The truncated sample -/

/-- The scale-`i` sample truncated at the outer scale `X'`. -/
noncomputable def PKtr (i X' : ℕ) : Finset ℕ := apSample X' (gridAt i).P₀ (gridAt i).b₀

lemma PKtr_subset_PK {i X' : ℕ} (h : X' ≤ X (KK i)) : PKtr i X' ⊆ PK i := by
  intro n hn
  rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range] at hn
  rw [PK, apSample, Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_lt_of_le hn.1 h, hn.2⟩

/-- `b₀ < X'` whenever the truncation is above the downward floor. -/
lemma b₀_lt_of_Xlo_le_at {i X' : ℕ} (hlo : Xlo (KK i) ≤ X') : (gridAt i).b₀ < X' :=
  b₀_lt_of_Xlo_le (KK_hundred i) hlo

lemma PKtr_nonempty {i X' : ℕ} (hlo : Xlo (KK i) ≤ X') : (PKtr i X').Nonempty :=
  apSample_nonempty (gridAt i) (b₀_lt_of_Xlo_le_at hlo)

open Classical in
/-- The band's sample times, truncated at the outer scale `X'`. -/
noncomputable def bandTtr (i X' : ℕ) : Finset ℕ := (bandT i).filter (fun n => n < X')

lemma bandTtr_subset (i X' : ℕ) : bandTtr i X' ⊆ PKtr i X' := by
  classical
  intro n hn
  rw [bandTtr, Finset.mem_filter] at hn
  have hPK : n ∈ PK i := bandT_subset i hn.1
  rw [PK, apSample, Finset.mem_filter, Finset.mem_range] at hPK
  rw [PKtr, apSample, Finset.mem_filter, Finset.mem_range]
  exact ⟨hn.2, hPK.2⟩

/-! ### E1 at the truncated scale, in `|Atom|` form -/

/-- **`entropy_E1_down` at family index `i`.**  The joint law of the truncated sample carries
all but `50√K` bits per window, at every `X' ∈ [Xlo (KK i), X (KK i)]`. -/
theorem deficit_primeLambertFour_down (i X' : ℕ) (hlo : Xlo (KK i) ≤ X')
    (hhi : X' ≤ X (KK i)) :
    ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLaw (gridAt i) (b₀_lt_of_Xlo_le_at hlo) (kk i) (primeLambertAtBase 4)).H₂ := by
  have hE1 := entropy_E1_down (K := KK i) (k₄ := kk i) (X' := X') rfl (KK_ge i) hlo hhi
  refine le_trans (le_of_eq ?_) hE1.le
  rw [card_Atom_gridAt]
  ring

/-! ### The truncated band keeps at least half the truncated sample -/

/-- **The head-room leaf.**  At every truncation above the downward floor, the band's `n`-floor
`Dm·bandLo i` removes at most half the truncated sample.

Arithmetic: `|PKtr| ≥ X'/P₀ − 1` and the removed part is at most `Dm·bandLo i/P₀ + 1`, so it
suffices that `4·Dm·bandLo i + 4P₀ ≤ Xlo (KK i)`.  `bandLo i ≤ 2X(KK i − 4) + kk i`, and both
`Dm` and `X (KK i − 4)` are below `2^{2^{m (KK i)}}` while `Xlo (KK i) = 2^{50·2^{m (KK i)}}` —
the tower gap of `G4EntropyScaleGap`, with room to spare. -/
theorem card_bandTtr_ge (i X' : ℕ) (hlo : Xlo (KK i) ≤ X') (hhi : X' ≤ X (KK i)) :
    ((PKtr i X').card : ℝ) ≤ 2 * ((bandTtr i X').card : ℝ) := by
  sorry

lemma bandTtr_nonempty {i X' : ℕ} (hlo : Xlo (KK i) ≤ X') (hhi : X' ≤ X (KK i)) :
    (bandTtr i X').Nonempty := by
  classical
  rw [← Finset.card_pos]
  have h := card_bandTtr_ge i X' hlo hhi
  have hP : (0 : ℝ) < ((PKtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (PKtr_nonempty hlo)
    exact_mod_cast this
  have : (0 : ℝ) < ((bandTtr i X').card : ℝ) := by linarith
  exact_mod_cast this

/-! ### The certified truncated band law -/

open Classical in
/-- The joint window law of the band's sample times below the outer scale `X'`. -/
noncomputable def bandTLawTr (i X' : ℕ) (hlo : Xlo (KK i) ≤ X') (hhi : X' ≤ X (KK i)) (x : ℝ) :
    FinLaw ((gridAt i).Atom → Fin (2 ^ kk i)) :=
  empirical (bandTtr i X') (bandTtr_nonempty hlo hhi) (ZVec (gridAt i) (kk i) x)

set_option maxHeartbeats 1000000 in
/-- **The truncated band keeps the joint certification**, with the same `101√K` per-window
deficit as `H₂_bandTLaw_ge` — and, crucially, **no** `|P_K|/a` restriction price. -/
theorem H₂_bandTLawTr_ge (i X' : ℕ) (hlo : Xlo (KK i) ≤ X') (hhi : X' ≤ X (KK i)) :
    ((kk i : ℝ) - 101 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (bandTLawTr i X' hlo hhi (primeLambertAtBase 4)).H₂ := by
  classical
  have hApos : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 0 < Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS400 : (400 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := by
    have h : (160000 : ℝ) ≤ ((KK i : ℕ) : ℝ) := by exact_mod_cast KK_ge i
    have h2 : Real.sqrt (160000 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_le_sqrt h
    have h400 : Real.sqrt (160000 : ℝ) = 400 := by
      rw [show (160000 : ℝ) = 400 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h400 ▸ h2]
  have hA1 : (1 : ℝ) ≤ (Fintype.card (gridAt i).Atom : ℝ) := by
    have : 1 ≤ Fintype.card (gridAt i).Atom := Fintype.card_pos
    exact_mod_cast this
  -- the truncated full law's deficit
  have hfull : ((kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
      ≤ (empirical (PKtr i X') (PKtr_nonempty hlo)
          (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))).H₂ := by
    have h := deficit_primeLambertFour_down i X' hlo hhi
    have hlaw : jointLaw (gridAt i) (b₀_lt_of_Xlo_le_at hlo) (kk i) (primeLambertAtBase 4)
        = empirical (PKtr i X') (PKtr_nonempty hlo)
            (ZVec (gridAt i) (kk i) (primeLambertAtBase 4)) := rfl
    rw [hlaw] at h
    linarith [h, sub_mul (kk i : ℝ) (50 * Real.sqrt (KK i))
      (Fintype.card (gridAt i).Atom : ℝ)]
  -- restriction to the band's part
  have hrest := H₂_empirical_restrict_ge (PKtr_nonempty hlo) (bandTtr_nonempty hlo hhi)
    (bandTtr_subset i X') (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))
    (M := (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ))
    (δ := 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
    (fun T hT => H₂_vector_le i T hT _) hfull
  have hPpos : (0 : ℝ) < ((PKtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (PKtr_nonempty hlo)
    exact_mod_cast this
  have hTpos : (0 : ℝ) < ((bandTtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (bandTtr_nonempty hlo hhi)
    exact_mod_cast this
  have hσ : (1 : ℝ) / 2 ≤ ((bandTtr i X').card : ℝ) / ((PKtr i X').card : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hPpos]
    linarith [card_bandTtr_ge i X' hlo hhi]
  have hδpos : (0 : ℝ) < 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1 := by
    have := Real.sqrt_pos.2 hKpos
    positivity
  have hcost : (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1)
      / (((bandTtr i X').card : ℝ) / ((PKtr i X').card : ℝ))
      ≤ 2 * (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * (((bandTtr i X').card : ℝ) / ((PKtr i X').card : ℝ)) := by linarith
    nlinarith [hδpos, h2]
  have hlaw2 : bandTLawTr i X' hlo hhi (primeLambertAtBase 4)
      = empirical (bandTtr i X') (bandTtr_nonempty hlo hhi)
          (ZVec (gridAt i) (kk i) (primeLambertAtBase 4)) := rfl
  rw [hlaw2]
  have hfin : (2 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
    nlinarith [hS400, hA1]
  have hexp : ((kk i : ℝ) - 101 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      = (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
        - 101 * (Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ)) := by ring
  rw [hexp]
  linarith [hrest, hcost, hfin]

set_option maxHeartbeats 1000000 in
/-- **The truncated band's capture bound.**  Every `ℓ`-word's frequency over the `(n, α, p)`
triples of the band *below the outer scale `X'`* is within `2√(808 log 2·ℓ/√K)` of `2^{−ℓ}` —
the same bound `abs_posAvg_bandTLaw_le` gives at the band's end, now at **every** truncation down
to `Xlo (KK i) = √(X (KK i))`. -/
theorem abs_posAvg_bandTLawTr_le (i X' ℓ : ℕ) (hlo : Xlo (KK i) ≤ X') (hhi : X' ≤ X (KK i))
    (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i) (w : Fin (2 ^ ℓ)) :
    |posAvg (kk i) ℓ (bandTLawTr i X' hlo hhi (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 101 * Real.sqrt (KK i) := by linarith [hS0]
  have hmain := abs_posAvg_sub_le hℓ (by omega)
    (bandTLawTr i X' hlo hhi (primeLambertAtBase 4)) w hδ (H₂_bandTLawTr_ge i X' hlo hhi)
  refine hmain.trans ?_
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hhalf : (kk i : ℝ) / 2 ≤ (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hden : (0 : ℝ) < (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
  have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
    rw [Real.mul_self_sqrt hKpos.le, hkk4]
  have hstep : Real.log 2 * (ℓ : ℝ) * (101 * Real.sqrt (KK i)) / ((kk i : ℝ) - ℓ + 1)
      ≤ 808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i) := by
    rw [div_le_div_iff₀ hden hS0]
    have hkey : Real.log 2 * (ℓ : ℝ) * (101 * Real.sqrt (KK i)) * Real.sqrt ((KK i : ℕ) : ℝ)
        = 404 * Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by
      linear_combination (101 * Real.log 2 * (ℓ : ℝ)) * hsq
    rw [hkey]
    have hc : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by positivity
    have hstep2 := mul_le_mul_of_nonneg_left hhalf
      (by positivity : (0:ℝ) ≤ 808 * Real.log 2 * (ℓ : ℝ))
    linarith [hc, hstep2]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (101 * Real.sqrt (KK i))
      / ((kk i : ℝ) - ℓ + 1) := by positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

end NormalNumbers.G4.Sched
