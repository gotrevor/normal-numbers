/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWMid

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

/-! ### The open leaf -/

/-- **The ungated head is a vanishing fraction of the history.**

The head consumes at most `headW i ≈ 16·wFloor_i·|Atom_i|/P₀_i` windows, each `kk i` long, while
everything read before band `i` is at least `fLW (i−1) ≥ |bandW (i−1)|·kk (i−1)
≥ Xlo (KK i)·kk_{i−1}/(4·P₀_{i−1})`.  Since `wFloor i = 4·gridDm_i·Xlo (KK i)`, the `Xlo (KK i)`
cancels and what is left is

> `256·gridDm_i·|Atom_i|·kk_i·P₀_{i−1} / (P₀_i·kk_{i−1})`.

**Why it is still open.**  Closing it needs a *lower* bound on `P₀_i = Mprod_i·freezeQ_i`
relative to `gridDm_i·P₀_{i−1}`, and the repo currently carries only *upper* bounds on `P₀`
(`P₀_le`, `P₀_le_two_pow`, `logP₀Nat_le_two_pow`) — every estimate in the E0 cone wants `P₀`
small.  The true statement is not in doubt (`freezeQ ≥ ∏_{p ≤ 2|Idx|} p` with
`|Idx| = (K²+1)^K·N(K)`, against `P₀_{i−1} ≤ gridP₀Bound (K−4)`), but it is a genuine
size-hierarchy fact about the schedule, not a formality: it needs a Chebyshev-type lower bound on
the primorial, or a lower bound on `Mprod = ∏_α d_α²`.

Stated for `i+1` because band `0` has no history (`fTW 0 = 0`); the finitely many read indices in
band `0` do not affect the limit. -/
theorem head_frac_tiny (i : ℕ) :
    (headW (i + 1) : ℝ) * (kk (i + 1) : ℝ) * (KK (i + 1) : ℝ) ≤ (fTW (i + 1) : ℝ) := by
  sorry

end NormalNumbers.G4.Sched
