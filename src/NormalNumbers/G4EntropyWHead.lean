/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWMid
import NormalNumbers.G4GridP0Lower

/-!
# The ungated head of a band

`abs_prefix_ratio_sub_le` controls the read at every position cutoff `c` **above the gate**
`8·wFloor i ≤ cutLo i c`.  Below the gate the two flanks are no longer comparable — the lower one
can be empty — so the certificate says nothing.  This module bounds what is left.

* `headW i` — the number of windows an ungated cutoff can consume: `cutLo i c < 8·wFloor i`
  forces `cutHi i c ≤ 16·wFloor i` (`cutHi_le_of_ungated`), so the consumed starts all lie in
  `bandWtr i (16·wFloor i) ×ˢ univ` (`aLe_le_headW`).  The head is thus a *bounded multiple of
  the floor*, in sample-time scale.
* `aLe_fnthW` — the read-index/cutoff bridge in the other direction: the cutoff `fnthW i (a−1)`
  consumes exactly the first `a` windows.  This is what lets step 4 quantify over read indices.
* `head_frac_tiny` — the one open leaf: the head's read length is at most a `1/K` fraction of
  everything read before band `i`.
-/

open Finset

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The read-index ↔ cutoff bridge, in the other direction -/

open Classical in
/-- **The cutoff at the `a`-th start consumes exactly `a` windows.** -/
theorem aLe_fnthW (i a : ℕ) (ha : 0 < a) (haN : a ≤ (winStartsW i).card) :
    aLe i (fnthW i (a - 1)) = a := by
  classical
  have ha1 : a - 1 < (winStartsW i).card := by omega
  have hidx : idxLe i (fnthW i (a - 1)) = Finset.range a := by
    ext b
    rw [idxLe, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    constructor
    · rintro ⟨hb, hle⟩
      have := (fnthW_le_iff hb ha1).1 hle
      omega
    · intro hb
      have hbN : b < (winStartsW i).card := by omega
      exact ⟨hbN, (fnthW_le_iff hbN ha1).2 (by omega)⟩
  have := card_idxLe i (fnthW i (a - 1))
  rw [hidx, Finset.card_range] at this
  omega

/-! ### The head is a bounded multiple of the floor -/

lemma one_le_wFloor (i : ℕ) : 1 ≤ wFloor i := by
  have h := Xlo_le_wFloor' i
  have := Xlo_pos (KK i)
  omega

/-- **An ungated cutoff cannot reach past `16·wFloor i`.**  `cutHi ≤ cutLo·(1+3/K) + 4·d_ref + 5`
and `K·d_ref ≤ wFloor`, so `cutLo < 8·wFloor` gives `cutHi ≤ 9·wFloor` with room to spare. -/
theorem cutHi_le_of_ungated (i c : ℕ) (h : cutLo i c < 8 * wFloor i) :
    cutHi i c ≤ 16 * wFloor i := by
  have hK : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by linarith
  have hgap := flank_gap i c
  have hlo : (cutLo i c : ℝ) ≤ 8 * (wFloor i : ℝ) := by
    have : (cutLo i c : ℝ) < 8 * (wFloor i : ℝ) := by exact_mod_cast h
    linarith
  have hdref : (KK i : ℝ) * (dRef i : ℝ) ≤ (wFloor i : ℝ) := by
    have := KK_mul_dRef_le_wFloor i
    exact_mod_cast this
  have hwf : (1 : ℝ) ≤ (wFloor i : ℝ) := by
    have := one_le_wFloor i; exact_mod_cast this
  -- `2K²·cutHi ≤ 16K²·wFloor + 48K·wFloor + 8K·wFloor + 10K² ≤ 32K²·wFloor`
  have hstep : 2 * (KK i : ℝ) ^ 2 * (cutHi i c : ℝ) ≤ 2 * (KK i : ℝ) ^ 2 * (16 * (wFloor i : ℝ)) := by
    have hwfnn : (0:ℝ) ≤ (wFloor i : ℝ) := by linarith
    have hKsq : (0:ℝ) ≤ 2 * (KK i : ℝ) ^ 2 := by positivity
    have p1 : 2 * (KK i : ℝ) ^ 2 * (cutLo i c : ℝ) ≤ 2 * (KK i : ℝ) ^ 2 * (8 * (wFloor i : ℝ)) :=
      mul_le_mul_of_nonneg_left hlo hKsq
    have p2 : 6 * (KK i : ℝ) * (cutLo i c : ℝ) ≤ 6 * (KK i : ℝ) * (8 * (wFloor i : ℝ)) :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    have hK48 : (48 : ℝ) * (KK i : ℝ) ≤ (KK i : ℝ) ^ 2 := by nlinarith
    have p3 : 48 * (KK i : ℝ) * (wFloor i : ℝ) ≤ (KK i : ℝ) ^ 2 * (wFloor i : ℝ) := by
      have := mul_le_mul_of_nonneg_right hK48 hwfnn
      linarith
    have p4 : 8 * (KK i : ℝ) * ((KK i : ℝ) * (dRef i : ℝ)) ≤ 8 * (KK i : ℝ) * (wFloor i : ℝ) :=
      mul_le_mul_of_nonneg_left hdref (by positivity)
    have hK8 : (8 : ℝ) * (KK i : ℝ) ≤ (KK i : ℝ) ^ 2 := by nlinarith
    have p5 : 8 * (KK i : ℝ) * (wFloor i : ℝ) ≤ (KK i : ℝ) ^ 2 * (wFloor i : ℝ) := by
      have := mul_le_mul_of_nonneg_right hK8 hwfnn
      linarith
    have p6 : 10 * (KK i : ℝ) ^ 2 ≤ 10 * ((KK i : ℝ) ^ 2 * (wFloor i : ℝ)) := by
      nlinarith [hwf, hKpos]
    have hd8 : 8 * (KK i : ℝ) ^ 2 * (dRef i : ℝ)
        = 8 * (KK i : ℝ) * ((KK i : ℝ) * (dRef i : ℝ)) := by ring
    linarith [hgap, p1, p2, p3, p4, p5, p6]
  have hfin : (cutHi i c : ℝ) ≤ 16 * (wFloor i : ℝ) := by
    have h2 : (0 : ℝ) < 2 * (KK i : ℝ) ^ 2 := by positivity
    exact le_of_mul_le_mul_left (by linarith) h2
  have : ((cutHi i c : ℕ) : ℝ) ≤ ((16 * wFloor i : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

open Classical in
/-- The number of windows an ungated cutoff can consume. -/
noncomputable def headW (i : ℕ) : ℕ :=
  (bandWtr i (16 * wFloor i)).card * Fintype.card (gridAt i).Atom

open Classical in
/-- **An ungated cutoff consumes at most `headW i` windows.** -/
theorem aLe_le_headW (i c : ℕ) (h : ¬ (8 * wFloor i ≤ cutLo i c)) : aLe i c ≤ headW i := by
  classical
  have hlt : cutLo i c < 8 * wFloor i := by omega
  have hcut := cutHi_le_of_ungated i c hlt
  have h1 : aLe i c ≤ (pairsLe i c).card := by
    rw [aLe_eq_card_startsOf]; exact card_startsOf_le i (pairsLe i c)
  have h2 := card_pairsLe_le i c
  have h3 : (bandWtr i (cutHi i c)).card ≤ (bandWtr i (16 * wFloor i)).card :=
    Finset.card_le_card (bandWtr_mono i hcut)
  have h4 : (bandWtr i (cutHi i c)).card * Fintype.card (gridAt i).Atom ≤ headW i :=
    Nat.mul_le_mul_right _ h3
  omega

/-! ### The ℕ-level ingredients of the head estimate -/

lemma gridOf_congr {K K' NN NN' : ℕ} (hK : 1 ≤ K) (hK' : 1 ≤ K') (h : K = K') (hN : NN = NN') :
    gridOf K NN hK = gridOf K' NN' hK' := by
  subst h; subst hN; rfl

lemma gridAt_succ_eq (i : ℕ) :
    gridAt (i + 1) = gridOf (KK i + 4) (N (KK i + 4)) (by have := KK_pos i; omega) := by
  show gridOf (KK (i + 1)) (N (KK (i + 1))) (KK_one_le (i + 1)) = _
  exact gridOf_congr _ _ (KK_succ i) (by rw [KK_succ i])

/-- **The growth of the modulus swallows the head's junk factor.**  This is `P₀_growth`
transported to the band indexing: `240·Dm'·|Atom'|·kk'·KK'·P₀ ≤ P₀'`. -/
theorem head_growth (i : ℕ) :
    240 * gridDm (KK (i + 1)) (N (KK (i + 1))) * Fintype.card (gridAt (i + 1)).Atom
        * kk (i + 1) * KK (i + 1) * (gridAt i).P₀
      ≤ (gridAt (i + 1)).P₀ := by
  have hK2 : 2 ≤ KK i := by have := KK_ge i; omega
  have hKs : KK (i + 1) = KK i + 4 := KK_succ i
  have hA : Fintype.card (gridAt (i + 1)).Atom = gridH (KK i + 4) := by
    rw [card_Atom_gridAt, hKs]; rfl
  have hkkKK : kk (i + 1) * KK (i + 1) ≤ (KK i + 4) ^ 2 := by
    have h1 : KK (i + 1) = 4 * kk (i + 1) := rfl
    have h2 : kk (i + 1) ≤ KK i + 4 := by
      have : KK i = 4 * kk i := rfl
      unfold kk at *
      omega
    nlinarith [h1, h2, Nat.zero_le (kk (i+1))]
  have hg := P₀_growth (K := KK i) hK2
  have hP : (gridAt i).P₀ = (gridOf (KK i) (N (KK i)) (by omega : 1 ≤ KK i)).P₀ := rfl
  have hP' : (gridAt (i + 1)).P₀
      = (gridOf (KK i + 4) (N (KK i + 4)) (by omega : 1 ≤ KK i + 4)).P₀ := by
    rw [gridAt_succ_eq i]
  rw [hP', hP]
  refine le_trans ?_ hg
  have hDm : gridDm (KK (i + 1)) (N (KK (i + 1))) = gridDm (KK i + 4) (N (KK i + 4)) := by
    rw [hKs]
  rw [hDm, hA]
  have hstep : 240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4)
      * (kk (i + 1) * KK (i + 1))
      ≤ 256 * (KK i + 4) ^ 2 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) := by
    have h1 : 240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4)
        * (kk (i + 1) * KK (i + 1))
        ≤ 240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) * (KK i + 4) ^ 2 :=
      Nat.mul_le_mul_left _ hkkKK
    calc 240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) * (kk (i + 1) * KK (i + 1))
        ≤ 240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) * (KK i + 4) ^ 2 := h1
      _ ≤ 256 * (KK i + 4) ^ 2 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) := by
          nlinarith [Nat.zero_le (gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4)
            * (KK i + 4) ^ 2)]
  calc 240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) * kk (i + 1) * KK (i + 1)
        * (gridOf (KK i) (N (KK i)) (by omega : 1 ≤ KK i)).P₀
      = (240 * gridDm (KK i + 4) (N (KK i + 4)) * gridH (KK i + 4) * (kk (i + 1) * KK (i + 1)))
          * (gridOf (KK i) (N (KK i)) (by omega : 1 ≤ KK i)).P₀ := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hstep

/-- `n² + 1 ≤ 2^{2n}`. -/
lemma sq_succ_le_two_pow (n : ℕ) : n ^ 2 + 1 ≤ 2 ^ (2 * n) := by
  have h : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : n ^ 2 < (2 ^ n) ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  have : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul]; ring_nf
  omega

/-- **The head's junk factor is dwarfed by the previous certificate floor.** -/
lemma head_junk_le_Xlo (i : ℕ) :
    Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i ≤ Xlo (KK i) := by
  set K := KK i with hK
  have hKge : 160000 ≤ K := KK_ge i
  have hKs : KK (i + 1) = K + 4 := KK_succ i
  have hA : Fintype.card (gridAt (i + 1)).Atom = ((K + 4) ^ 2 + 1) ^ (K + 4) := by
    rw [card_Atom_gridAt, hKs]
  have hA2 : Fintype.card (gridAt (i + 1)).Atom ≤ 2 ^ (2 * (K + 4) ^ 2) := by
    rw [hA]
    calc ((K + 4) ^ 2 + 1) ^ (K + 4) ≤ (2 ^ (2 * (K + 4))) ^ (K + 4) :=
          Nat.pow_le_pow_left (sq_succ_le_two_pow (K + 4)) _
      _ = 2 ^ (2 * (K + 4) ^ 2) := by rw [← pow_mul]; ring_nf
  have hkkKK : kk (i + 1) * KK (i + 1) ≤ 2 ^ (2 * (K + 4)) := by
    have h2 : kk (i + 1) ≤ K + 4 := by
      have : K = 4 * kk i := rfl
      unfold kk at *
      omega
    have h3 : KK (i + 1) = 4 * kk (i + 1) := rfl
    have h4 : kk (i + 1) * KK (i + 1) ≤ (K + 4) ^ 2 := by nlinarith [h2, h3, Nat.zero_le (kk (i+1))]
    have := sq_succ_le_two_pow (K + 4)
    omega
  have hkki : kk i ≤ 2 ^ (2 * (K + 4)) := by
    have : K = 4 * kk i := rfl
    have h := Nat.lt_two_pow_self (n := 2 * (K + 4))
    omega
  have hprod : Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i
      ≤ 2 ^ (2 * (K + 4) ^ 2 + 2 * (K + 4) + 1) := by
    have hm : Fintype.card (gridAt (i + 1)).Atom * (kk (i + 1) * KK (i + 1))
        ≤ 2 ^ (2 * (K + 4) ^ 2) * 2 ^ (2 * (K + 4)) := Nat.mul_le_mul hA2 hkkKK
    have hpow : (2 : ℕ) ^ (2 * (K + 4) ^ 2) * 2 ^ (2 * (K + 4))
        = 2 ^ (2 * (K + 4) ^ 2 + 2 * (K + 4)) := by rw [← pow_add]
    have hlast : (2 : ℕ) ^ (2 * (K + 4)) ≤ 2 ^ (2 * (K + 4) ^ 2 + 2 * (K + 4)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdouble : (2 : ℕ) ^ (2 * (K + 4) ^ 2 + 2 * (K + 4) + 1)
        = 2 ^ (2 * (K + 4) ^ 2 + 2 * (K + 4)) + 2 ^ (2 * (K + 4) ^ 2 + 2 * (K + 4)) := by
      rw [pow_succ]; ring
    have hassoc : Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1)
        = Fintype.card (gridAt (i + 1)).Atom * (kk (i + 1) * KK (i + 1)) := by ring
    omega
  have hexp : 2 * (K + 4) ^ 2 + 2 * (K + 4) + 1 ≤ 50 * 2 ^ m K := by
    have hcube : K ^ 3 ≤ m K := by
      have h1 := m₁_ge_cube (show 1 ≤ K by omega)
      unfold m
      omega
    have h2 : m K < 2 ^ m K := Nat.lt_two_pow_self
    nlinarith [hcube, h2, hKge]
  have hXlo : Xlo K = 2 ^ (50 * 2 ^ m K) := by
    show (2 ^ (2 ^ m K)) ^ 50 = _
    rw [← pow_mul]; ring_nf
  calc Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i
      ≤ 2 ^ (2 * (K + 4) ^ 2 + 2 * (K + 4) + 1) := hprod
    _ ≤ 2 ^ (50 * 2 ^ m K) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = Xlo K := hXlo.symm

/-- **The additive slack.**  `8·P₀·(junk) ≤ wTop i`. -/
theorem head_slack (i : ℕ) :
    8 * (gridAt i).P₀ * (Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i)
      ≤ wTop i := by
  have hjunk := head_junk_le_Xlo i
  have hP : (gridAt i).P₀ ≤ Xlo (KK i) := by
    have h := KK_mul_P₀_le_Xlo i
    have hK := KK_pos i
    have : (gridAt i).P₀ ≤ KK i * (gridAt i).P₀ := Nat.le_mul_of_pos_left _ hK
    omega
  have hstep : 8 * (gridAt i).P₀
      * (Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i)
      ≤ 8 * (Xlo (KK i) * Xlo (KK i)) := by
    have := Nat.mul_le_mul hP hjunk
    calc 8 * (gridAt i).P₀
        * (Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i)
        = 8 * ((gridAt i).P₀
            * (Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i)) := by ring
      _ ≤ 8 * (Xlo (KK i) * Xlo (KK i)) := Nat.mul_le_mul_left _ this
  have hsq : Xlo (KK i) * Xlo (KK i) = X (KK i) := Xlo_sq (KK i)
  have h18 := eighteen_X_le_wTop i
  omega

/-! ### The ratio arithmetic, schedule-free -/

/-- **The head estimate in closed form.**  `X0` is the head's per-window junk factor
`|Atom'|·kk'·KK'`, `Dm` the next level's multiplier bound, `W` the previous band's scale top,
`F` its floor, `P`/`P'` the two moduli and `k` the previous band's window length.  The two
inputs are the modulus growth and the additive slack. -/
theorem head_core {Dm W X0 P P' F k : ℝ}
    (hP : 0 < P) (hP' : 0 < P') (hX0 : 1 ≤ X0) (hk : 1 ≤ k) (hF : 0 ≤ F) (hDm : 0 ≤ Dm)
    (hgrow : 240 * Dm * X0 * P ≤ P')
    (hslack : 8 * P * (X0 + k) ≤ W)
    (hfloor : 4 * F ≤ W) :
    P * (15 * (4 * Dm * W) + 2 * P') * X0 ≤ P' * (W - F - 2 * P) * k := by
  have h4 : 16 * P ≤ W := by nlinarith
  have hW : (0 : ℝ) < W := by linarith
  have h1 : 60 * Dm * W * P * X0 ≤ P' * W / 4 := by nlinarith [hgrow, hW]
  have h2 : 2 * P * X0 ≤ W / 4 - 2 * P * k := by linarith
  have h3 : 2 * P * P' * X0 ≤ P' * (W / 4 - 2 * P * k) := by nlinarith [h2, hP']
  have h5 : 5 * W / 8 ≤ W - F - 2 * P := by linarith
  have h6 : (W - F - 2 * P) * 1 ≤ (W - F - 2 * P) * k :=
    mul_le_mul_of_nonneg_left hk (by linarith)
  have h7 : P' * (5 * W / 8) ≤ P' * ((W - F - 2 * P) * k) := by nlinarith [h5, h6, hP']
  have hexp : P * (15 * (4 * Dm * W) + 2 * P') * X0
      = 60 * Dm * W * P * X0 + 2 * P * P' * X0 := by ring
  have hR : P' * (W - F - 2 * P) * k = P' * ((W - F - 2 * P) * k) := by ring
  have hPk : 0 ≤ P' * (2 * P * k) := by positivity
  rw [hexp, hR]
  nlinarith [h1, h3, h7, hPk, hP', hW]

/-! ### The open leaf -/

/-- **The ungated head is a vanishing fraction of the history.**

The head consumes at most `headW i ≈ 16·wFloor_i·|Atom_i|/P₀_i` windows, each `kk i` long, while
everything read before band `i` is at least `fLW (i−1) ≥ |bandW (i−1)|·kk (i−1)`.  Since
`wFloor (i+1) = 4·gridDm_{i+1}·wTop i`, the scale `wTop i` cancels and what is left is a pure
size hierarchy for the progression modulus between consecutive levels,
`P₀ (K+4) ≥ 256·(K+4)²·Dm(K+4)·H(K+4)·P₀ K` — that is `G4GridP0Lower.P₀_growth`, transported here
as `head_growth`.  The additive slack (`head_slack`) is the statement that the junk factor is
below the previous certificate floor, which `Xlo` settles with room to spare.

Stated for `i+1` because band `0` has no history (`fTW 0 = 0`); the finitely many read indices in
band `0` do not affect the limit. -/
theorem head_frac_tiny (i : ℕ) :
    (headW (i + 1) : ℝ) * (kk (i + 1) : ℝ) * (KK (i + 1) : ℝ) ≤ (fTW (i + 1) : ℝ) := by
  classical
  set K := KK i with hKdef
  set P : ℝ := ((gridAt i).P₀ : ℝ) with hPdef
  set P' : ℝ := ((gridAt (i + 1)).P₀ : ℝ) with hP'def
  set W : ℝ := (wTop i : ℝ) with hWdef
  set F : ℝ := (wFloor i : ℝ) with hFdef
  set Dm : ℝ := (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) with hDmdef
  set A' : ℝ := (Fintype.card (gridAt (i + 1)).Atom : ℝ) with hAdef
  set X0 : ℝ := A' * (kk (i + 1) : ℝ) * (KK (i + 1) : ℝ) with hX0def
  have hPpos : (0 : ℝ) < P := by
    have := (gridAt i).P₀_pos; rw [hPdef]; exact_mod_cast this
  have hP'pos : (0 : ℝ) < P' := by
    have := (gridAt (i + 1)).P₀_pos; rw [hP'def]; exact_mod_cast this
  have hkk : (1 : ℝ) ≤ (kk i : ℝ) := by
    have : 1 ≤ kk i := by unfold kk; omega
    exact_mod_cast this
  have hX0one : (1 : ℝ) ≤ X0 := by
    have h1 : 1 ≤ Fintype.card (gridAt (i + 1)).Atom := Fintype.card_pos
    have h2 : 1 ≤ kk (i + 1) := by unfold kk; omega
    have h3 : 1 ≤ KK (i + 1) := KK_pos (i + 1)
    have : (1 : ℕ) ≤ Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) := by
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [hX0def, hAdef]
    exact_mod_cast this
  -- the floor of the next band, in closed form
  have hF' : (wFloor (i + 1) : ℝ) = 4 * Dm * W := by
    have h := wFloor_eq' (i + 1)
    have hw : wTop i = Xlo (KK (i + 1)) := wTop_eq i
    rw [hDmdef, hWdef, hw]
    rw [h]
    push_cast
    ring
  -- the two certified counts
  set B' : ℝ := ((bandWtr (i + 1) (16 * wFloor (i + 1))).card : ℝ) with hB'def
  set B : ℝ := ((bandW i).card : ℝ) with hBdef
  have hB'le : B' * P' ≤ 15 * (4 * Dm * W) + 2 * P' := by
    have hle : wFloor (i + 1) ≤ 16 * wFloor (i + 1) := by
      have := one_le_wFloor (i + 1); omega
    have h := card_bandWtr_le_real (i + 1) (16 * wFloor (i + 1)) hle
    have hcast : ((16 * wFloor (i + 1) : ℕ) : ℝ) = 16 * (wFloor (i + 1) : ℝ) := by push_cast; ring
    rw [hcast, ← hP'def, ← hB'def] at h
    have hdiv : (16 * (wFloor (i + 1) : ℝ) - (wFloor (i + 1) : ℝ)) / P' * P'
        = 15 * (wFloor (i + 1) : ℝ) := by field_simp; ring
    have := mul_le_mul_of_nonneg_right h (le_of_lt hP'pos)
    rw [add_mul, hdiv] at this
    rw [hF'] at this
    linarith
  have hBge : W - F - 2 * P ≤ B * P := by
    have hle : wFloor i ≤ wTop i := by
      have := wgate_wTop i; omega
    have h := card_bandWtr_ge_real i (wTop i) hle
    rw [← hWdef, ← hFdef, ← hPdef] at h
    have hbw : ((bandWtr i (wTop i)).card : ℝ) = B := rfl
    rw [hbw] at h
    have hm := mul_le_mul_of_nonneg_right h (le_of_lt hPpos)
    have hdiv : (W - F) / P * P = W - F := by field_simp
    rw [sub_mul, hdiv] at hm
    linarith
  -- the two schedule inputs
  have hgrow : 240 * Dm * X0 * P ≤ P' := by
    have h := head_growth i
    have hR : (240 * gridDm (KK (i + 1)) (N (KK (i + 1)))
        * Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1)
        * (gridAt i).P₀ : ℝ) ≤ ((gridAt (i + 1)).P₀ : ℝ) := by exact_mod_cast h
    rw [hX0def, hAdef, hDmdef, hPdef, hP'def]
    push_cast at hR ⊢
    linarith [hR]
  have hslack : 8 * P * (X0 + (kk i : ℝ)) ≤ W := by
    have h := head_slack i
    have hR : ((8 * (gridAt i).P₀
        * (Fintype.card (gridAt (i + 1)).Atom * kk (i + 1) * KK (i + 1) + kk i) : ℕ) : ℝ)
        ≤ ((wTop i : ℕ) : ℝ) := by exact_mod_cast h
    rw [hX0def, hAdef, hPdef, hWdef]
    push_cast at hR ⊢
    linarith [hR]
  have hfloor : 4 * F ≤ W := by
    have := wgate_wTop i
    have hR : ((4 * wFloor i + 4 * (gridAt i).P₀ : ℕ) : ℝ) ≤ ((wTop i : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hFdef, hWdef]
    push_cast at hR ⊢
    linarith [hR, hPpos]
  have hFnn : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hDmnn : (0 : ℝ) ≤ Dm := Nat.cast_nonneg _
  have hcore := head_core hPpos hP'pos hX0one hkk hFnn hDmnn hgrow hslack hfloor
  -- from the two counts to the read lengths
  have hkey : B' * X0 ≤ B * (kk i : ℝ) := by
    have hmul : (0 : ℝ) < P * P' := mul_pos hPpos hP'pos
    refine le_of_mul_le_mul_right ?_ hmul
    have hXP : (0 : ℝ) ≤ X0 * P := by
      have : (0:ℝ) ≤ X0 := by linarith
      exact mul_nonneg this (le_of_lt hPpos)
    have hstep1 : B' * X0 * (P * P') = (B' * P') * (X0 * P) := by ring
    have hstep2 : (B' * P') * (X0 * P) ≤ (15 * (4 * Dm * W) + 2 * P') * (X0 * P) :=
      mul_le_mul_of_nonneg_right hB'le hXP
    have hstep3 : (15 * (4 * Dm * W) + 2 * P') * (X0 * P) = P * (15 * (4 * Dm * W) + 2 * P') * X0 := by
      ring
    have hkpos : (0 : ℝ) ≤ (kk i : ℝ) := Nat.cast_nonneg _
    have hstep4 : P' * (W - F - 2 * P) * (kk i : ℝ) ≤ P' * (B * P) * (kk i : ℝ) := by
      have : P' * (W - F - 2 * P) ≤ P' * (B * P) :=
        mul_le_mul_of_nonneg_left hBge (le_of_lt hP'pos)
      exact mul_le_mul_of_nonneg_right this hkpos
    have hstep5 : P' * (B * P) * (kk i : ℝ) = B * (kk i : ℝ) * (P * P') := by ring
    linarith [hstep2, hcore, hstep4]
  -- the head, and the history
  have hhead : (headW (i + 1) : ℝ) * (kk (i + 1) : ℝ) * (KK (i + 1) : ℝ) = B' * X0 := by
    have : headW (i + 1)
        = (bandWtr (i + 1) (16 * wFloor (i + 1))).card * Fintype.card (gridAt (i + 1)).Atom := rfl
    rw [this, hX0def, hB'def, hAdef]
    push_cast
    ring
  have hhist : B * (kk i : ℝ) ≤ (fTW (i + 1) : ℝ) := by
    have h1 : (bandW i).card ≤ (winStartsW i).card := card_bandW_le_winStartsW i
    have h2 : (bandW i).card * kk i ≤ fLW i := by
      show _ ≤ (winStartsW i).card * kk i
      exact Nat.mul_le_mul_right _ h1
    have h3 : fLW i ≤ fTW (i + 1) := by
      show fLW i ≤ fTW i + fLW i
      omega
    have : (bandW i).card * kk i ≤ fTW (i + 1) := le_trans h2 h3
    have hR : (((bandW i).card * kk i : ℕ) : ℝ) ≤ ((fTW (i + 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [hBdef]
    push_cast at hR ⊢
    linarith [hR]
  rw [hhead]
  linarith [hkey, hhist]


end NormalNumbers.G4.Sched
