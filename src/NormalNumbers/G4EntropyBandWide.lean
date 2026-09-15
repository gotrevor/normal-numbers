/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandHead
import NormalNumbers.G4EntropyMTowerAssembly

/-!
# The **wide** band: scale range `[Xlo (KK i), Xlo (KK (i+1))]`

`G4EntropyBandTrunc` certifies the band's truncations at every `X' ∈ [Xlo (KK i), X (KK i)]`,
and `G4EntropyBandHead` raises the band floor to `bandLoH i = 2·Xlo (KK i)` so that *every*
mid-band cutoff is above the certificate floor.  What that leaves is the **head ratio problem**:
at a cutoff `X'` just above the floor `wFloor i = gridDm·bandLoH i` the visited part of the
sample is a vanishing fraction of the certified truncation `PKtr i X'`, so the restriction price
is unpayable — and the head is *not* absorbable by the trivial bound, because band `i`'s floor
`≈ Xlo (KK i) = 2^{50·2^{m_i}}` already contains `2^{48·2^{m_i}}` sample times while the previous
band, topping out at `X (KK (i−1))`, contains only `2^{98·2^{m_{i−1}}}` — a tower fewer.

**The fix is to widen the previous band, not to lower the floor.**  `entropy_E1_tile` certifies
grid level `KK i` at *every* outer scale in `[Xlo (KK i), Xlo (KK (i+1))]`, so band `i` may run
all the way up to `Xlo (KK (i+1))` instead of stopping at `X (KK i) = Xlo (KK i)²`.  Then the
scale ranges of consecutive bands **tile**, and band `i+1`'s uncertifiable head, of scale
`≲ 8·gridDm_{i+1}·Xlo (KK (i+1))`, is compared against band `i`'s *full* length, of scale
`≈ Xlo (KK (i+1))`.  The ratio is

  `8·gridDm_{i+1}·(|Atom_{i+1}|·kk_{i+1}/P₀^{(i+1)}) / (|Atom_i|·kk_i/P₀^{(i)})
      ≈ 2^{2·2^{21·KK_{i+1}²}} · 2^{−2·2^{m_{i+1}}}`,

which is astronomically small because `m ≥ K³ ≫ 21K²`: the denser lower band drowns the sparser
upper band's head.  That is the content of `head_frac_tiny` downstream.

This module builds the wide band and its certified capture bound.  Nothing here changes
`bandT`, `bandTtr` or `fullReal`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### E1 at every scale of the tile -/

/-- **`entropy_E1_tile` at family index `i`.**  The joint law of the truncated sample carries all
but `50√K` bits per window, at every `X' ∈ [Xlo (KK i), Xlo (KK (i+1))]` — the *whole* tile, not
just up to `X (KK i)`. -/
theorem deficit_primeLambertFour_wide (i X' : ℕ) (hlo : Xlo (KK i) ≤ X')
    (hhi : X' ≤ Xlo (KK (i + 1))) :
    ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLaw (gridAt i) (b₀_lt_of_Xlo_le_at hlo) (kk i) (primeLambertAtBase 4)).H₂ := by
  have hhi' : X' ≤ Xlo (KK i + 4) := by rwa [← KK_succ i]
  have hE1 := entropy_E1_tile (K := KK i) (k₄ := kk i) (X' := X') rfl (KK_ge i) hlo hhi'
    (b₀_lt_of_Xlo_le_at hlo)
  refine le_trans (le_of_eq ?_) hE1.le
  rw [card_Atom_gridAt]
  ring

/-! ### The wide band and its truncations -/

/-- The wide band's **position** floor, `4·Xlo (KK i)`: four times the certificate floor, so that
it also clears the previous band's position ceiling `2·Xlo (KK i) + kk (i−1)`. -/
noncomputable def wLo (i : ℕ) : ℕ := 4 * Xlo (KK i)

/-- The wide band's `n`-floor: `gridDm · wLo i`.  Every sample time of the band is at least this,
which puts every atom's window start above `wLo i`. -/
noncomputable def wFloor (i : ℕ) : ℕ := gridDm (KK i) (N (KK i)) * wLo i

lemma Xlo_le_wFloor (i : ℕ) : Xlo (KK i) ≤ wFloor i := by
  show Xlo (KK i) ≤ gridDm (KK i) (N (KK i)) * wLo i
  have hDm : 1 ≤ gridDm (KK i) (N (KK i)) := gridDm_pos _ _
  have hb : wLo i = 4 * Xlo (KK i) := rfl
  have : wLo i ≤ gridDm (KK i) (N (KK i)) * wLo i := Nat.le_mul_of_pos_left _ hDm
  omega

attribute [local irreducible] Xlo wLo wFloor

open Classical in
/-- The wide band, truncated at the outer scale `X'`: the truncated sample above the raised
floor.  Unlike `bandTtr`, this is **not** tied to the scale `X (KK i)`; `X'` may run all the way
to `Xlo (KK (i+1))`. -/
noncomputable def bandWtr (i X' : ℕ) : Finset ℕ :=
  (PKtr i X').filter (fun n => wFloor i ≤ n)

lemma bandWtr_subset (i X' : ℕ) : bandWtr i X' ⊆ PKtr i X' := Finset.filter_subset _ _

/-! **The gate** is the hypothesis `4·wFloor i + 4·P₀ ≤ X'`, written out at each use (never as a
`def`: a `Prop`-valued abbreviation for it sits in the local context of every downstream proof and
sends `whnf` into the schedule's tower terms). -/

lemma Xlo_le_of_wgate {i X' : ℕ} (h : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    Xlo (KK i) ≤ X' := by
  have := Xlo_le_wFloor i
  omega

lemma two_P₀_le_of_wgate {i X' : ℕ} (h : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    2 * (gridAt i).P₀ ≤ X' := by omega

/-- **The wide band keeps at least half of the truncated sample**, at every cutoff above the
gate.  Same count as `card_bandTtr_ge`, with `M = wFloor i` in place of `3·Dm·X (KK (i−1))`. -/
theorem card_bandWtr_ge (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') :
    ((PKtr i X').card : ℝ) ≤ 2 * ((bandWtr i X').card : ℝ) := by
  classical
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hP₀R : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  set M : ℕ := wFloor i with hM
  have hdrop : (PKtr i X').filter (fun n => ¬ M ≤ n)
      ⊆ (PKtr i X').filter (fun n => n < M) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, by have := hn.2; omega⟩
  have hcount : (((PKtr i X').filter (fun n => n < M)).card : ℝ)
      ≤ (M : ℝ) / ((gridAt i).P₀ : ℝ) + 1 := by
    have h := card_filter_lt_apSample_le X' (gridAt i).P₀ (gridAt i).b₀ M hP₀pos
    have hR : ((((PKtr i X').filter (fun n => n < M)).card : ℕ) : ℝ)
        ≤ ((M / (gridAt i).P₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    refine hR.trans ?_
    push_cast
    have : ((M / (gridAt i).P₀ : ℕ) : ℝ) ≤ (M : ℝ) / ((gridAt i).P₀ : ℝ) := Nat.cast_div_le
    linarith
  have hbig : (X' : ℝ) / (2 * ((gridAt i).P₀ : ℝ)) ≤ ((PKtr i X').card : ℝ) :=
    card_apSample_ge_half X' (gridAt i).P₀ (gridAt i).b₀ hP₀pos (gridAt i).b₀_lt_P₀
      (two_P₀_le_of_wgate hg)
  have hgateR : (4 : ℝ) * (M : ℝ) + 4 * ((gridAt i).P₀ : ℝ) ≤ (X' : ℝ) := by
    have h' : ((4 * M + 4 * (gridAt i).P₀ : ℕ) : ℝ) ≤ (X' : ℝ) := Nat.cast_le.2 hg
    push_cast at h'
    linarith
  have hhalf : 2 * ((M : ℝ) / ((gridAt i).P₀ : ℝ) + 1) ≤ ((PKtr i X').card : ℝ) := by
    refine le_trans ?_ hbig
    rw [le_div_iff₀ (show (0:ℝ) < 2 * ((gridAt i).P₀ : ℝ) by linarith)]
    have hexp : 2 * ((M : ℝ) / ((gridAt i).P₀ : ℝ) + 1) * (2 * ((gridAt i).P₀ : ℝ))
        = 4 * (M : ℝ) + 4 * ((gridAt i).P₀ : ℝ) := by
      field_simp
      ring
    rw [hexp]
    linarith
  have hsplit : ((PKtr i X').card : ℝ)
      = ((bandWtr i X').card : ℝ)
        + (((PKtr i X').filter (fun n => ¬ M ≤ n)).card : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := PKtr i X') (p := fun n => M ≤ n)
    have hb : bandWtr i X' = (PKtr i X').filter (fun n => M ≤ n) := rfl
    rw [hb, ← h]
    push_cast
    ring
  have hdropR : ((((PKtr i X').filter (fun n => ¬ M ≤ n)).card : ℕ) : ℝ)
      ≤ (((PKtr i X').filter (fun n => n < M)).card : ℝ) :=
    Nat.cast_le.2 (Finset.card_le_card hdrop)
  linarith

lemma bandWtr_nonempty {i X' : ℕ} (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') : (bandWtr i X').Nonempty := by
  classical
  rw [← Finset.card_pos]
  have h := card_bandWtr_ge i X' hg
  have hP : (0 : ℝ) < ((PKtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (PKtr_nonempty (Xlo_le_of_wgate hg))
    exact_mod_cast this
  have : (0 : ℝ) < ((bandWtr i X').card : ℝ) := by linarith
  exact_mod_cast this

/-! ### The certified wide band law -/

open Classical in
/-- The joint window law of the wide band's sample times below the outer scale `X'`. -/
noncomputable def bandWLaw (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (x : ℝ) :
    FinLaw ((gridAt i).Atom → Fin (2 ^ kk i)) :=
  empirical (bandWtr i X') (bandWtr_nonempty hg) (ZVec (gridAt i) (kk i) x)

set_option maxHeartbeats 1000000 in
/-- **The wide band keeps the joint certification**, with the same `101√K` per-window deficit as
`H₂_bandTLawTr_ge`, now at every cutoff of the *whole tile*. -/
theorem H₂_bandWLaw_ge (i X' : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hhi : X' ≤ Xlo (KK (i + 1))) :
    ((kk i : ℝ) - 101 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (bandWLaw i X' hg (primeLambertAtBase 4)).H₂ := by
  classical
  have hlo : Xlo (KK i) ≤ X' := Xlo_le_of_wgate hg
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
  have hfull : ((kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
      ≤ (empirical (PKtr i X') (PKtr_nonempty hlo)
          (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))).H₂ := by
    have h := deficit_primeLambertFour_wide i X' hlo hhi
    have hlaw : jointLaw (gridAt i) (b₀_lt_of_Xlo_le_at hlo) (kk i) (primeLambertAtBase 4)
        = empirical (PKtr i X') (PKtr_nonempty hlo)
            (ZVec (gridAt i) (kk i) (primeLambertAtBase 4)) := rfl
    rw [hlaw] at h
    linarith [h, sub_mul (kk i : ℝ) (50 * Real.sqrt (KK i))
      (Fintype.card (gridAt i).Atom : ℝ)]
  have hrest := H₂_empirical_restrict_ge (PKtr_nonempty hlo) (bandWtr_nonempty hg)
    (bandWtr_subset i X') (ZVec (gridAt i) (kk i) (primeLambertAtBase 4))
    (M := (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ))
    (δ := 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ))
    (fun T hT => H₂_vector_le i T hT _) hfull
  have hPpos : (0 : ℝ) < ((PKtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (PKtr_nonempty hlo)
    exact_mod_cast this
  have hTpos : (0 : ℝ) < ((bandWtr i X').card : ℝ) := by
    have := Finset.card_pos.2 (bandWtr_nonempty hg)
    exact_mod_cast this
  have hσ : (1 : ℝ) / 2 ≤ ((bandWtr i X').card : ℝ) / ((PKtr i X').card : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hPpos]
    linarith [card_bandWtr_ge i X' hg]
  have hδpos : (0 : ℝ) < 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1 := by
    have := Real.sqrt_pos.2 hKpos
    positivity
  have hcost : (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1)
      / (((bandWtr i X').card : ℝ) / ((PKtr i X').card : ℝ))
      ≤ 2 * (50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ) + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * (((bandWtr i X').card : ℝ) / ((PKtr i X').card : ℝ)) := by linarith
    nlinarith [hδpos, h2]
  have hlaw2 : bandWLaw i X' hg (primeLambertAtBase 4)
      = empirical (bandWtr i X') (bandWtr_nonempty hg)
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
/-- **The wide band's capture bound.**  Every `ℓ`-word's frequency over the `(n, α, p)` triples
of the wide band below `X'` is within `2√(808 log 2·ℓ/√K)` of `2^{−ℓ}`, at **every** cutoff of
the tile `[Xlo (KK i), Xlo (KK (i+1))]` above the gate. -/
theorem abs_posAvg_bandWLaw_le (i X' ℓ : ℕ) (hg : 4 * wFloor i + 4 * (gridAt i).P₀ ≤ X') (hhi : X' ≤ Xlo (KK (i + 1)))
    (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i) (w : Fin (2 ^ ℓ)) :
    |posAvg (kk i) ℓ (bandWLaw i X' hg (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (808 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 101 * Real.sqrt (KK i) := by linarith [hS0]
  have hmain := abs_posAvg_sub_le hℓ (by omega)
    (bandWLaw i X' hg (primeLambertAtBase 4)) w hδ (H₂_bandWLaw_ge i X' hg hhi)
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
