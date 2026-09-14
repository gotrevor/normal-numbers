/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandFreq

/-!
# Entropy expedition — the whole sample in a band, and its certification

`G4EntropyBandFreq` certifies one *good atom*'s windows inside a band; the good atom depends on
`G₄`'s entropy data, so the resulting read is explicit but not schedule-only.  With
`windows_eq_or_disjoint` (`Q ∣ P₀`) the read can instead take the **whole** sample's windows in a
band — a schedule-only object.  This module certifies that collection:

* `bandTLaw i x` — the joint window law restricted to the band's sample times (`bandT`, an
  `n`-only condition, so the restriction is a pure sample-time restriction);
* `H₂_bandTLaw_ge` — the restriction costs a factor `2` plus one bit: per-window deficit
  `≤ 101√K`;
* `abs_posAvg_bandTLaw_le` — hence every `ℓ`-word's frequency over the band's `(n, α, p)` triples
  is within `2√(808 log 2·ℓ/√K)` of `2^{−ℓ}`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

open Classical in
/-- The joint window law of the band's sample times. -/
noncomputable def bandTLaw (i : ℕ) (x : ℝ) : FinLaw ((gridAt i).Atom → Fin (2 ^ kk i)) :=
  empirical (bandT i) (bandT_nonempty i) (ZVec (gridAt i) (kk i) x)

/-- The alphabet ceiling for a window *vector*: `m·|A|` bits. -/
lemma H₂_vector_le (i : ℕ) {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ((gridAt i).Atom → Fin (2 ^ kk i))) :
    (empirical S hS f).H₂ ≤ (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ) := by
  classical
  have hcard : Fintype.card ((gridAt i).Atom → Fin (2 ^ kk i))
      = (2 ^ kk i) ^ (Fintype.card (gridAt i).Atom) := by
    simp [Fintype.card_fun]
  have hpos : 0 < Fintype.card ((gridAt i).Atom → Fin (2 ^ kk i)) := by
    rw [hcard]
    exact Nat.pow_pos (Nat.two_pow_pos _)
  have h := (empirical S hS f).H₂_le_logb_card hpos
  rw [hcard] at h
  refine h.trans (le_of_eq ?_)
  have hrw : (((2 ^ kk i) ^ (Fintype.card (gridAt i).Atom) : ℕ) : ℝ)
      = (2 : ℝ) ^ (kk i * Fintype.card (gridAt i).Atom) := by
    rw [← pow_mul]
    push_cast
    ring
  rw [hrw, Real.logb, Real.log_pow]
  have hne : Real.log 2 ≠ 0 := by
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
    linarith
  field_simp
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **The band keeps the joint certification.**  `σ ≥ 1/2` costs a factor `2` and one bit, so the
per-window deficit rises from `entropy_E1`'s `50√K` to at most `101√K`. -/
theorem H₂_bandTLaw_ge (i : ℕ) :
    ((kk i : ℝ) - 101 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (bandTLaw i (primeLambertAtBase 4)).H₂ := by
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
  -- the full law's deficit
  have hfull : ((kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
      ≤ (empirical (PK i) (PK_nonempty i)
          (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))).H₂ := by
    have h := deficit_primeLambertFour i
    have hlaw : jointLawAt i (primeLambertAtBase 4)
        = empirical (PK i) (PK_nonempty i) (ZVec (gridAt i) (kk i) (primeLambertAtBase 4)) := rfl
    rw [hlaw] at h
    linarith [h, sub_mul (kk i : ℝ) (50 * Real.sqrt (KK i))
      (Fintype.card (gridAt i).Atom : ℝ)]
  -- restriction
  have hrest := H₂_empirical_restrict_ge (PK_nonempty i) (bandT_nonempty i) (bandT_subset i)
    (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))
    (M := (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ))
    (δ := 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
    (fun T hT => H₂_vector_le i T hT _) hfull
  -- `σ ≥ 1/2`
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hTpos : (0 : ℝ) < ((bandT i).card : ℝ) := by
    have := Finset.card_pos.2 (bandT_nonempty i)
    exact_mod_cast this
  have hσ : (1 : ℝ) / 2 ≤ ((bandT i).card : ℝ) / ((PK i).card : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hPpos]
    linarith [card_bandT_ge' i]
  have hδpos : (0 : ℝ) < 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1 := by
    have := Real.sqrt_pos.2 hKpos
    positivity
  have hcost : (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1)
      / (((bandT i).card : ℝ) / ((PK i).card : ℝ))
      ≤ 2 * (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * (((bandT i).card : ℝ) / ((PK i).card : ℝ)) := by linarith
    nlinarith [hδpos, h2]
  have hlaw2 : bandTLaw i (primeLambertAtBase 4)
      = empirical (bandT i) (bandT_nonempty i)
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
/-- **The band's capture bound for the whole sample.**  Every `ℓ`-word's frequency over the
band's `(n, α, p)` triples is within `2√(808 log 2·ℓ/√K)` of `2^{−ℓ}`. -/
theorem abs_posAvg_bandTLaw_le (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i)
    (w : Fin (2 ^ ℓ)) :
    |posAvg (kk i) ℓ (bandTLaw i (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 101 * Real.sqrt (KK i) := by linarith [hS0]
  have hmain := abs_posAvg_sub_le hℓ (by omega) (bandTLaw i (primeLambertAtBase 4)) w hδ
    (H₂_bandTLaw_ge i)
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
