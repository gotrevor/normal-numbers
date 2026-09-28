/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyLRTransducer

/-!
# The run dictionary: the `L/R` expansion's runs ARE the CF digits

The transducer of `VandeheyLRTransducer` emits `L/R` letters, and its output is the `L/R`
expansion of the image (`lrWord_eq_lrExpandWord`).  The assembly, however, wants the image's
CF digits.  This file is the dictionary between them.

## The mechanism

`lrTail z = z/(1-z)` below `1` and `z - 1` above, so:

* above `1` the step SUBTRACTS ONE: `lrTail z = z - 1`;
* below `1` the step subtracts one in the RECIPROCAL coordinate: `(lrTail z)⁻¹ = z⁻¹ - 1`.

So the `L/R` expansion is the slow (Stern–Brocot) continued fraction, and a maximal run is a
whole integer part being stripped at once.  Writing `T` for the Gauss map, for `w ∈ (0,1)`
irrational the runs of the expansion of `w` have lengths `cfDigit w 0, cfDigit w 1, …`
alternating `L, R, L, R, …`, and after `n` runs the point is

  `Tⁿw`  (`n` even)   or   `(Tⁿw)⁻¹`  (`n` odd).

`lrTail_lrPos` is that statement, and `lrExpand_eq_of_lt_lrPos_succ` reads off the letters.  The
CF digits of the image are therefore the run lengths of the emitted word — the fact that makes a
letter-emitting transducer (which CAN be finite-state) as good as a digit-emitting one (which
cannot).
-/

namespace NormalNumbers.VandeheyLR

open Mat2

/-! ## The two run steps -/

/-- Above `1`, `lrTail` subtracts one; so an `R`-run strips the integer part in one go. -/
lemma lrTail_iter_R : ∀ (k : ℕ) {z : ℝ}, (k : ℝ) ≤ z → lrTail^[k] z = z - k := by
  intro k
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have hk : ((k : ℝ) + 1) ≤ z := by push_cast at hz; linarith
    have hnlt : ¬ (z < 1) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have : (1 : ℝ) ≤ z := by linarith
      linarith
    rw [Function.iterate_succ_apply, lrTail, if_neg hnlt, ih (by linarith)]
    push_cast
    ring

/-- The letters of an `R`-run. -/
lemma lrExpand_R_run {k : ℕ} {z : ℝ} (hz : (k : ℝ) ≤ z) {i : ℕ} (hi : i < k) :
    lrExpand z i = false := by
  have hik : (i : ℝ) + 1 ≤ (k : ℝ) := by
    have : (i : ℕ) + 1 ≤ k := hi
    exact_mod_cast this
  rw [lrExpand, lrTail_iter_R i (by linarith), lrLetter, decide_eq_false]
  linarith

/-- Below `1`, `lrTail` subtracts one in the reciprocal coordinate; so an `L`-run strips the
integer part of `z⁻¹` in one go. -/
lemma lrTail_iter_L : ∀ (k : ℕ) {z : ℝ}, 0 < z → (k : ℝ) < z⁻¹ →
    lrTail^[k] z = (z⁻¹ - k)⁻¹ := by
  intro k
  induction k with
  | zero => intro z hz _; simp [inv_inv]
  | succ k ih =>
    intro z hz hk
    have hk' : ((k : ℝ) + 1) < z⁻¹ := by push_cast at hk; linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hone : (1 : ℝ) < z⁻¹ := by linarith
    have hzlt : z < 1 := by
      have h := mul_lt_mul_of_pos_right hone hz
      rw [one_mul, inv_mul_cancel₀ (ne_of_gt hz)] at h
      linarith
    have hzne : z ≠ 0 := ne_of_gt hz
    have hsub : (1 - z) ≠ 0 := by intro h; rw [show z = 1 from by linarith] at hzlt; linarith
    have hz' : 0 < z / (1 - z) := div_pos hz (by linarith)
    have hinv : (z / (1 - z))⁻¹ = z⁻¹ - 1 := by
      rw [inv_div]
      field_simp
    rw [Function.iterate_succ_apply, lrTail, if_pos hzlt, ih hz' (by rw [hinv]; linarith), hinv]
    push_cast
    ring_nf

/-- The letters of an `L`-run. -/
lemma lrExpand_L_run {k : ℕ} {z : ℝ} (hz : 0 < z) (hk : (k : ℝ) < z⁻¹) {i : ℕ} (hi : i < k) :
    lrExpand z i = true := by
  have hik : (i : ℝ) + 1 ≤ (k : ℝ) := by
    have : (i : ℕ) + 1 ≤ k := hi
    exact_mod_cast this
  have hiz : (i : ℝ) < z⁻¹ := by linarith
  have hpos : 0 < z⁻¹ - (i : ℝ) := by linarith
  have h1 : (1 : ℝ) < z⁻¹ - (i : ℝ) := by linarith
  rw [lrExpand, lrTail_iter_L i hz hiz, lrLetter, decide_eq_true (inv_lt_one_of_one_lt₀ h1)]

/-! ## The dictionary -/

/-- The `L/R` position at which the `n`-th run begins: the sum of the first `n` CF digits. -/
noncomputable def lrPos (w : ℝ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, cfDigit w i

@[simp] lemma lrPos_zero (w : ℝ) : lrPos w 0 = 0 := by simp [lrPos]

lemma lrPos_succ (w : ℝ) (n : ℕ) : lrPos w (n + 1) = lrPos w n + cfDigit w n := by
  simp [lrPos, Finset.sum_range_succ]

/-- `gaussMap` in reciprocal form. -/
lemma gaussMap_eq_sub (y : ℝ) (hy : y ≠ 0) (hy0 : 0 ≤ y⁻¹) :
    gaussMap y = y⁻¹ - (⌊y⁻¹⌋₊ : ℝ) := by
  rw [gaussMap, if_neg hy, Int.fract, natCast_floor_eq_intCast_floor hy0]

/-- **The run dictionary.**  After the first `n` runs of the `L/R` expansion of an irrational
`w ∈ (0,1)` — that is, after `cfDigit w 0 + ⋯ + cfDigit w (n-1)` letters — the remaining point is
`Tⁿw` for `n` even and `(Tⁿw)⁻¹` for `n` odd.  So the `n`-th run has length exactly
`cfDigit w n`: **the runs of the `L/R` expansion ARE the CF digits.** -/
theorem lrTail_lrPos (w : ℝ) (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ n : ℕ, lrTail^[lrPos w n] w
      = if n % 2 = 0 then gaussMap^[n] w else (gaussMap^[n] w)⁻¹ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hirrn, hn0, hn1⟩ := irrational_orbit w hirr hw n
    set p : ℝ := gaussMap^[n] w with hp
    have hpne : p ≠ 0 := ne_of_gt hn0
    have hpinv : 0 < p⁻¹ := inv_pos.mpr hn0
    have hd : cfDigit w n = ⌊p⁻¹⌋₊ := by rw [cfDigit]
    have hnext : gaussMap^[n + 1] w = gaussMap p := by
      rw [Function.iterate_succ_apply', hp]
    have hfract : gaussMap p = p⁻¹ - (cfDigit w n : ℝ) := by
      rw [gaussMap_eq_sub p hpne hpinv.le, hd]
    rw [lrPos_succ, show lrPos w n + cfDigit w n = cfDigit w n + lrPos w n from by omega,
      Function.iterate_add_apply, ih]
    rcases Nat.even_or_odd n with he | ho
    · -- `n` even: the point is `Tⁿw ∈ (0,1)`, and an `L`-run of length `cfDigit w n` follows
      have hmod : n % 2 = 0 := Nat.even_iff.mp he
      have hmod' : (n + 1) % 2 ≠ 0 := by omega
      rw [if_pos hmod, if_neg hmod']
      have hlt : ((cfDigit w n : ℕ) : ℝ) < p⁻¹ := by
        rw [hd]
        refine lt_of_le_of_ne (Nat.floor_le hpinv.le) fun hcon => ?_
        exact hirrn.inv.ne_nat _ hcon.symm
      rw [lrTail_iter_L (cfDigit w n) hn0 hlt, hnext, hfract]
    · -- `n` odd: the point is `(Tⁿw)⁻¹ > 1`, and an `R`-run of length `cfDigit w n` follows
      have hmod : n % 2 ≠ 0 := Nat.odd_iff.mp ho ▸ one_ne_zero
      have hmod' : (n + 1) % 2 = 0 := by omega
      rw [if_neg hmod, if_pos hmod']
      have hle : ((cfDigit w n : ℕ) : ℝ) ≤ p⁻¹ := by
        rw [hd]; exact Nat.floor_le hpinv.le
      rw [lrTail_iter_R (cfDigit w n) hle, hnext, hfract]

/-- **The letters of the `n`-th run.**  Every letter strictly inside the `n`-th run is `L` for
`n` even and `R` for `n` odd. -/
theorem lrExpand_run (w : ℝ) (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1) (n i : ℕ)
    (hi : i < cfDigit w n) :
    lrExpand w (lrPos w n + i) = decide (n % 2 = 0) := by
  obtain ⟨hirrn, hn0, hn1⟩ := irrational_orbit w hirr hw n
  set p : ℝ := gaussMap^[n] w with hp
  have hpinv : 0 < p⁻¹ := inv_pos.mpr hn0
  have hd : cfDigit w n = ⌊p⁻¹⌋₊ := by rw [cfDigit]
  have hbase := lrTail_lrPos w hirr hw n
  have hshift : lrExpand w (lrPos w n + i) = lrExpand (lrTail^[lrPos w n] w) i := by
    rw [lrExpand, lrExpand, ← Function.iterate_add_apply, Nat.add_comm i (lrPos w n)]
  rw [hshift, hbase]
  rcases Nat.even_or_odd n with he | ho
  · have hmod : n % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos hmod, decide_eq_true hmod]
    have hlt : ((cfDigit w n : ℕ) : ℝ) < p⁻¹ := by
      rw [hd]
      refine lt_of_le_of_ne (Nat.floor_le hpinv.le) fun hcon => ?_
      exact hirrn.inv.ne_nat _ hcon.symm
    exact lrExpand_L_run hn0 hlt hi
  · have hmod : n % 2 ≠ 0 := Nat.odd_iff.mp ho ▸ one_ne_zero
    rw [if_neg hmod, decide_eq_false hmod]
    have hle : ((cfDigit w n : ℕ) : ℝ) ≤ p⁻¹ := by
      rw [hd]; exact Nat.floor_le hpinv.le
    exact lrExpand_R_run hle hi

/-! ## The run index

Every position of the `L/R` stream lies in exactly one run, because `lrPos` is strictly
monotone (every CF digit of an irrational is `≥ 1`).  `runIdx` names that run, and then the
whole stream is described by ONE identity: the letter at `P` is the parity of `runIdx P`.
Alternations sit exactly at run ends, which is the fact the occurrence translation needs. -/

section RunIdx

variable {w : ℝ} (hirr : Irrational w) (hw : w ∈ Set.Ioo (0 : ℝ) 1)

include hirr hw

lemma lrPos_lt_succ (n : ℕ) : lrPos w n < lrPos w (n + 1) := by
  have h := one_le_cfDigit w hirr hw n
  rw [lrPos_succ]
  omega

lemma lrPos_strictMono : StrictMono (lrPos w) :=
  strictMono_nat_of_lt_succ (lrPos_lt_succ hirr hw)

lemma le_lrPos (n : ℕ) : n ≤ lrPos w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := lrPos_lt_succ hirr hw n
    omega

/-- The index of the run containing the position `P`. -/
noncomputable def runIdx (w : ℝ) (P : ℕ) : ℕ := Nat.findGreatest (fun n => lrPos w n ≤ P) P

omit hirr hw in
lemma runIdx_le (P : ℕ) : lrPos w (runIdx w P) ≤ P :=
  Nat.findGreatest_spec (P := fun n => lrPos w n ≤ P) (Nat.zero_le P) (by simp)

lemma lt_runIdx_succ (P : ℕ) : P < lrPos w (runIdx w P + 1) := by
  by_contra hcon
  have hle : lrPos w (runIdx w P + 1) ≤ P := by omega
  have hbound : runIdx w P + 1 ≤ P := le_trans (le_lrPos hirr hw _) hle
  refine Nat.findGreatest_is_greatest (P := fun n => lrPos w n ≤ P) ?_ hbound hle
  show Nat.findGreatest (fun n => lrPos w n ≤ P) P < runIdx w P + 1
  rw [← runIdx]
  omega

/-- The run index is pinned by the bracketing. -/
lemma runIdx_eq (m P : ℕ) (h1 : lrPos w m ≤ P) (h2 : P < lrPos w (m + 1)) :
    runIdx w P = m := by
  have hmono := lrPos_strictMono hirr hw
  have k1 := runIdx_le (w := w) P
  have k2 := lt_runIdx_succ hirr hw P
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono.monotone (show runIdx w P + 1 ≤ m from by omega)
    omega
  · have := hmono.monotone (show m + 1 ≤ runIdx w P from by omega)
    omega

/-- **The stream, in one identity.**  The letter at position `P` is the parity of the run `P`
lies in. -/
theorem lrExpand_eq_runIdx_parity (P : ℕ) :
    lrExpand w P = decide (runIdx w P % 2 = 0) := by
  have h1 := runIdx_le (w := w) P
  have h2 := lt_runIdx_succ hirr hw P
  rw [lrPos_succ] at h2
  have hP : P - lrPos w (runIdx w P) < cfDigit w (runIdx w P) := by omega
  have key := lrExpand_run w hirr hw (runIdx w P) (P - lrPos w (runIdx w P)) hP
  rw [show lrPos w (runIdx w P) + (P - lrPos w (runIdx w P)) = P from by omega] at key
  exact key

/-- The run index steps by at most one, and steps exactly when a run ends. -/
lemma runIdx_succ_eq (P : ℕ) :
    runIdx w (P + 1) = if P + 1 = lrPos w (runIdx w P + 1) then runIdx w P + 1
      else runIdx w P := by
  have h1 := runIdx_le (w := w) P
  have h2 := lt_runIdx_succ hirr hw P
  have hmono := lrPos_strictMono hirr hw
  have hrP : runIdx w P ≤ P := le_trans (le_lrPos hirr hw _) h1
  split_ifs with h
  · -- the next position starts the next run
    refine le_antisymm ?_ ?_
    · by_contra hcon
      have hlt : runIdx w P + 1 < runIdx w (P + 1) := by omega
      have := hmono hlt
      have h3 := runIdx_le (w := w) (P + 1)
      omega
    · exact Nat.le_findGreatest (by omega) (by omega)
  · refine le_antisymm ?_ ?_
    · by_contra hcon
      have hlt : runIdx w P < runIdx w (P + 1) := by omega
      have hge : runIdx w P + 1 ≤ runIdx w (P + 1) := by omega
      have := hmono.monotone hge
      have h3 := runIdx_le (w := w) (P + 1)
      omega
    · exact Nat.le_findGreatest (le_trans (le_lrPos hirr hw _) (by omega)) (by omega)

/-- **Alternations sit exactly at run ends.**  This is what turns an occurrence of a CF word in
the image's expansion into an occurrence of a single `L/R` pattern with forced boundary letters:
the letter change pins the run boundary. -/
theorem lrExpand_ne_succ_iff (P : ℕ) :
    lrExpand w P ≠ lrExpand w (P + 1) ↔ P + 1 = lrPos w (runIdx w P + 1) := by
  rw [lrExpand_eq_runIdx_parity hirr hw P, lrExpand_eq_runIdx_parity hirr hw (P + 1),
    runIdx_succ_eq hirr hw P]
  split_ifs with h
  · simp only [h, ne_eq, decide_eq_decide, iff_true]
    omega
  · simpa using h

end RunIdx

end NormalNumbers.VandeheyLR

section
open NormalNumbers.VandeheyLR
#print axioms lrTail_iter_R
#print axioms lrExpand_R_run
#print axioms lrTail_iter_L
#print axioms lrExpand_L_run
#print axioms lrTail_lrPos
#print axioms lrExpand_run
#print axioms runIdx_eq
#print axioms lrExpand_eq_runIdx_parity
#print axioms runIdx_succ_eq
#print axioms lrExpand_ne_succ_iff
end
