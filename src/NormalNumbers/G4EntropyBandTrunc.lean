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

/-- `m (KK i) + 7 ≤ m (KK (i+1))`: a crude strengthening of `two_pow_m_step`, enough to put the
whole previous scale below `Xlo` rather than merely below `X`.  (The true gap is a tower;
`m₂ (K+4) - m₂ K = 64K + 128` alone suffices.) -/
lemma m_step_seven (i : ℕ) : m (KK i) + 7 ≤ m (KK (i + 1)) := by
  have hK : 160000 ≤ KK i := KK_ge i
  have hsucc : KK (i + 1) = KK i + 4 := KK_succ i
  have h1 : m₁ (KK i) ≤ m₁ (KK i + 4) := by
    show 1000 * 8 ^ KK i * KK i ^ (2 * KK i + 1)
      ≤ 1000 * 8 ^ (KK i + 4) * (KK i + 4) ^ (2 * (KK i + 4) + 1)
    have hA : (8 : ℕ) ^ KK i ≤ 8 ^ (KK i + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hB : KK i ^ (2 * KK i + 1) ≤ (KK i + 4) ^ (2 * (KK i + 4) + 1) :=
      le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl 1000) hA) hB
  have h2 : m₂ (KK i) + 7 ≤ m₂ (KK i + 4) := by
    show 8 * KK i ^ 2 + 7 ≤ 8 * (KK i + 4) ^ 2
    nlinarith
  rw [hsucc]
  show m₁ (KK i) + m₂ (KK i) + 7 ≤ m₁ (KK i + 4) + m₂ (KK i + 4)
  omega

/-- The exponent gap with `Xlo`'s exponent `50` in place of `X`'s `100`. -/
lemma exponent_gap_Xlo (i : ℕ) :
    4 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i) ≤ 49 * 2 ^ m (KK (i + 1)) := by
  have hK : 160000 ≤ KK i := KK_ge i
  have hsucc : KK (i + 1) = KK i + 4 := KK_succ i
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hbig : 21 * KK (i + 1) ^ 2 + 2 ≤ KK i ^ 3 := by
    rw [hsucc]
    nlinarith [hK]
  have hstep : (2 : ℕ) ^ 7 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by have := m_step_seven i; omega)
  have hmono : 2 ^ (21 * KK (i + 1) ^ 2 + 2) ≤ 2 ^ m (KK i) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (21 * KK (i + 1) ^ 2 + 2) = 4 * 2 ^ (21 * KK (i + 1) ^ 2) := by
    rw [pow_add]; ring
  have hone : 1 ≤ 2 ^ (21 * KK (i + 1) ^ 2) := Nat.one_le_two_pow
  have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
  omega

set_option maxHeartbeats 1000000 in
/-- **The band gap, against the downward floor.**  `12·Dm(K_{i+1})·X(K_i) + 4·P₀ ≤ Xlo(K_{i+1})`:
the previous scale's whole inflated position range sits below the *floor* of the next scale's
certified window, not merely below its top. -/
theorem band_gap_strong_Xlo (i : ℕ) :
    (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
        + 4 * ((gridAt (i + 1)).P₀ : ℝ)
      ≤ (Xlo (KK (i + 1)) : ℝ) := by
  have hK1 : 100 ≤ KK (i + 1) := by have := KK_ge (i + 1); omega
  have hgap := exponent_gap_Xlo i
  have hXv : ((X (KK i) : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by
    show ((2 ^ (100 * 2 ^ m (KK i)) : ℕ) : ℝ) = _
    push_cast; ring
  have hone : (1 : ℕ) ≤ 2 ^ m (KK (i + 1)) := Nat.one_le_two_pow
  have hA : (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
      ≤ (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1))) := by
    have hDm : (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ)
        ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) := by
      have h := gridDm_le_two_pow hK1
      have h' : ((gridDm (KK (i + 1)) (N (KK (i + 1))) : ℕ) : ℝ)
          ≤ ((2 ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    have h12 : (12 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
    calc (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
        ≤ (2 : ℝ) ^ 4 * (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2))
            * (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by
          rw [hXv]
          have hXpos : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by positivity
          have hDmpos : (0 : ℝ) ≤ (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) :=
            Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul h12 hDm hDmpos (by positivity)) hXpos
      _ = (2 : ℝ) ^ (4 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i)) := by
          rw [← pow_add, ← pow_add]
      _ ≤ (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1))) := pow_le_pow_right₀ (by norm_num) hgap
  have hB : 4 * ((gridAt (i + 1)).P₀ : ℝ) ≤ (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1))) := by
    have hP := P₀_le_two_pow_band i
    calc 4 * ((gridAt (i + 1)).P₀ : ℝ)
        ≤ (2 : ℝ) ^ 2 * (2 : ℝ) ^ (2 * 2 ^ m (KK (i + 1))) := by
          have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [this]
          exact mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (2 : ℝ) ^ (2 + 2 * 2 ^ m (KK (i + 1))) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1))) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum : (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1))) + (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1)))
      ≤ (Xlo (KK (i + 1)) : ℝ) := by
    rw [Xlo_cast]
    have he : (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1))) + (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1)))
        = (2 : ℝ) ^ (49 * 2 ^ m (KK (i + 1)) + 1) := by rw [pow_succ]; ring
    rw [he]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

open Classical in
/-- The truncated band is the truncated sample's part above the band floor. -/
lemma bandTtr_eq_filter (i X' : ℕ) (hhi : X' ≤ X (KK i)) :
    bandTtr i X' = (PKtr i X').filter (fun n => gridDm (KK i) (N (KK i)) * bandLo i ≤ n) := by
  classical
  ext n
  simp only [bandTtr, PKtr, PK, bandT, apSample, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨-, hmod⟩, hfl⟩, hlt⟩
    exact ⟨⟨hlt, hmod⟩, hfl⟩
  · rintro ⟨⟨hlt, hmod⟩, hfl⟩
    exact ⟨⟨⟨lt_of_lt_of_le hlt hhi, hmod⟩, hfl⟩, hlt⟩

set_option maxHeartbeats 1000000 in
/-- **The head-room leaf.**  At every truncation above the downward floor, the band's `n`-floor
`Dm·bandLo i` removes at most half the truncated sample.

The count is `card_bandT_ge`'s, at the outer scale `X'`: the dropped times are below
`M = 3·Dm·X(K_{i−1})`, an arithmetic progression of modulus `P₀` meets `[0, M)` at most
`M/P₀ + 1` times, and `|PKtr| ≥ X'/(2P₀)`; `band_gap_strong_Xlo` says `4M + 4P₀ ≤ Xlo (KK i) ≤ X'`,
which is exactly `2(M/P₀ + 1) ≤ X'/(2P₀)`. -/
theorem card_bandTtr_ge (i X' : ℕ) (hlo : Xlo (KK i) ≤ X') (hhi : X' ≤ X (KK i)) :
    ((PKtr i X').card : ℝ) ≤ 2 * ((bandTtr i X').card : ℝ) := by
  classical
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hP₀R : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  have h2P₀ : 2 * (gridAt i).P₀ ≤ X' :=
    le_trans (two_mul_P₀_le_Xlo (KK_hundred i)) hlo
  have heq := bandTtr_eq_filter i X' hhi
  rcases i with _ | j
  · -- scale `0`: the floor is `0`, nothing is dropped
    have hb : bandTtr 0 X' = PKtr 0 X' := by
      rw [heq]
      refine Finset.filter_true_of_mem fun n _ => ?_
      rw [show bandLo 0 = 0 from rfl, Nat.mul_zero]
      exact Nat.zero_le n
    rw [hb]
    have h0 : (0 : ℝ) ≤ ((PKtr 0 X').card : ℝ) := Nat.cast_nonneg _
    linarith
  · set Dm : ℕ := gridDm (KK (j + 1)) (N (KK (j + 1))) with hDm
    set M : ℕ := 3 * Dm * X (KK j) with hM
    have hdrop : (PKtr (j + 1) X').filter (fun n => ¬ Dm * bandLo (j + 1) ≤ n)
        ⊆ (PKtr (j + 1) X').filter (fun n => n < M) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      have hlt : n < Dm * bandLo (j + 1) := by have := hn.2; omega
      have hbl : bandLo (j + 1) = bandTop j := rfl
      have hbt : bandTop j = 2 * X (KK j) + kk j := rfl
      have hkk := kk_succ_le_X j
      have hmono : Dm * bandLo (j + 1) ≤ Dm * (3 * X (KK j)) := by
        refine Nat.mul_le_mul_left _ ?_
        rw [hbl, hbt]
        omega
      have hMeq : Dm * (3 * X (KK j)) = M := by rw [hM]; ring
      omega
    have hcount : (((PKtr (j + 1) X').filter (fun n => n < M)).card : ℝ)
        ≤ (M : ℝ) / ((gridAt (j + 1)).P₀ : ℝ) + 1 := by
      have h := card_filter_lt_apSample_le X' (gridAt (j + 1)).P₀ (gridAt (j + 1)).b₀ M hP₀pos
      have hR : ((((PKtr (j + 1) X').filter (fun n => n < M)).card : ℕ) : ℝ)
          ≤ ((M / (gridAt (j + 1)).P₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h
      refine hR.trans ?_
      push_cast
      have : ((M / (gridAt (j + 1)).P₀ : ℕ) : ℝ) ≤ (M : ℝ) / ((gridAt (j + 1)).P₀ : ℝ) := Nat.cast_div_le
      linarith
    have hbig : (X' : ℝ) / (2 * ((gridAt (j + 1)).P₀ : ℝ)) ≤ ((PKtr (j + 1) X').card : ℝ) :=
      card_apSample_ge_half X' (gridAt (j + 1)).P₀ (gridAt (j + 1)).b₀ hP₀pos (gridAt (j + 1)).b₀_lt_P₀ h2P₀
    have hgate : (12 : ℝ) * (Dm : ℝ) * (X (KK j) : ℝ) + 4 * ((gridAt (j + 1)).P₀ : ℝ)
        ≤ (X' : ℝ) := by
      refine le_trans (band_gap_strong_Xlo j) ?_
      exact Nat.cast_le.2 hlo
    have hMR : (M : ℝ) = 3 * (Dm : ℝ) * (X (KK j) : ℝ) := by rw [hM]; push_cast; ring
    have hhalf : 2 * ((M : ℝ) / ((gridAt (j + 1)).P₀ : ℝ) + 1) ≤ ((PKtr (j + 1) X').card : ℝ) := by
      refine le_trans ?_ hbig
      rw [le_div_iff₀ (show (0:ℝ) < 2 * ((gridAt (j + 1)).P₀ : ℝ) by linarith)]
      have hexp : 2 * ((M : ℝ) / ((gridAt (j + 1)).P₀ : ℝ) + 1) * (2 * ((gridAt (j + 1)).P₀ : ℝ))
          = 4 * (M : ℝ) + 4 * ((gridAt (j + 1)).P₀ : ℝ) := by
        field_simp
        ring
      rw [hexp, hMR]
      linarith [hgate]
    have hsplit : ((PKtr (j + 1) X').card : ℝ)
        = ((bandTtr (j + 1) X').card : ℝ)
          + (((PKtr (j + 1) X').filter (fun n => ¬ Dm * bandLo (j + 1) ≤ n)).card : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not
        (s := PKtr (j + 1) X') (p := fun n => Dm * bandLo (j + 1) ≤ n)
      rw [heq, ← h]
      push_cast
      ring
    have hdropR : ((((PKtr (j + 1) X').filter (fun n => ¬ Dm * bandLo (j + 1) ≤ n)).card : ℕ) : ℝ)
        ≤ (((PKtr (j + 1) X').filter (fun n => n < M)).card : ℝ) := by
      exact Nat.cast_le.2 (Finset.card_le_card hdrop)
    linarith

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
