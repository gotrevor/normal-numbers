/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOffset

/-!
# The offset classes, separately — and the average over any sub-family of them

`abs_posAvg_sub_le` averages a word's block probability over **all** `m − ℓ + 1` window
positions.  Its proof, however, is not monolithic: it decomposes the positions into the `ℓ`
**offset classes** `p ≡ r (mod ℓ)` (the map is `posEquiv : (r, j) ↦ r + jℓ`), certifies each
class *separately* through `abs_avg_block_prob_offset_le`, and only then sums.

This module makes that per-class claim a first-class theorem (`abs_offset_class_le`) and draws
the consequence that the averaging may be restricted to **any** sub-family `R` of the classes at
**the same constant** (`abs_posAvgR_sub_le`).

Why this matters: a base-`2^k` digit of a number in `[0,1)` is a `k`-block of its binary digits
at a position `≡ 0 (mod k)`.  So base-`2^k` normality needs word frequencies restricted to a
**residue class of positions mod `k`** — and for a word of length `ℓ` with `k ∣ ℓ`, a residue
class of positions mod `k` is exactly a union of offset classes mod `ℓ`.  The restriction
therefore costs nothing at all: not a factor `√k`, not even a constant.
-/

open Finset

namespace NormalNumbers.G4Entropy

/-- The block-probability sum of the offset class `r`: over all coordinates `α : A` and all
whole `ℓ`-blocks of the window starting at a position `≡ r (mod ℓ)`. -/
noncomputable def classSum {A : Type*} [Fintype A] [DecidableEq A] (m ℓ : ℕ)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) (r : Fin ℓ) : ℝ :=
  ∑ c : A × Fin ((m - (r : ℕ)) / ℓ),
    ((L.map (lowTuple m (r : ℕ))).map (fullCoord (m - (r : ℕ)) ℓ c)).prob {w}

/-- The number of `(coordinate, block)` pairs in the offset class `r`. -/
noncomputable def classCard (A : Type*) [Fintype A] (m ℓ : ℕ) (r : Fin ℓ) : ℝ :=
  (Fintype.card A : ℝ) * (((m - (r : ℕ)) / ℓ : ℕ) : ℝ)

lemma classCard_nonneg (A : Type*) [Fintype A] (m ℓ : ℕ) (r : Fin ℓ) :
    0 ≤ classCard A m ℓ r := by
  rw [classCard]; positivity

/-- **Each offset class, on its own.**  The class `r` carries the *same* capacity bound that the
full average does — the constant is `2√(log2·ℓδ/(m − ℓ + 1))` for every class. -/
theorem abs_offset_class_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ) (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂) (r : Fin ℓ) :
    |classSum m ℓ L w r - (1 / (2 : ℝ) ^ ℓ) * classCard A m ℓ r|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) * classCard A m ℓ r := by
  classical
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hmℓ : (1 : ℝ) ≤ (m : ℝ) - ℓ + 1 := by
    have : (ℓ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hℓm
    linarith
  have hCA : (0 : ℝ) < (Fintype.card A : ℝ) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  set cc : ℝ := 1 / (2 : ℝ) ^ ℓ with hcc
  set B : ℝ := 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) with hB
  have hcardprod : (Fintype.card (A × Fin ((m - (r : ℕ)) / ℓ)) : ℝ) = classCard A m ℓ r := by
    rw [classCard]
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  rcases le_or_gt ((r : ℕ) + ℓ) m with hcase | hcase
  · -- a full block exists at this offset
    have hone : 1 ≤ (m - (r : ℕ)) / ℓ := (Nat.one_le_div_iff hℓ).2 (by omega)
    have hNpos : 0 < classCard A m ℓ r := by
      rw [classCard]
      have h1 : (1 : ℝ) ≤ (((m - (r : ℕ)) / ℓ : ℕ) : ℝ) := by exact_mod_cast hone
      nlinarith
    have hoff := abs_avg_block_prob_offset_le (A := A) (m := m) (ℓ := ℓ) (r := (r : ℕ))
      hℓ (by omega) L w hδ hdef
    rw [hcardprod] at hoff
    have hBr : 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - (r : ℕ))) ≤ B := by
      rw [hB]
      have hrle : ((r : ℕ) : ℝ) ≤ (ℓ : ℝ) - 1 := by
        have h2 : ((r : ℕ) + 1 : ℕ) ≤ ℓ := r.isLt
        have h3 : (((r : ℕ) + 1 : ℕ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h2
        push_cast at h3
        linarith
      have hden : (m : ℝ) - ℓ + 1 ≤ (m : ℝ) - (r : ℕ) := by linarith
      have hd0 : (0 : ℝ) < (m : ℝ) - ℓ + 1 := by linarith
      have hmono : Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - (r : ℕ))
          ≤ Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1) :=
        div_le_div_of_nonneg_left (by positivity) hd0 hden
      have := Real.sqrt_le_sqrt hmono
      linarith
    have hSN : |classSum m ℓ L w r / classCard A m ℓ r - cc| ≤ B := le_trans hoff hBr
    have h1 : classSum m ℓ L w r - cc * classCard A m ℓ r
        = classCard A m ℓ r * (classSum m ℓ L w r / classCard A m ℓ r - cc) := by
      field_simp
    have hkey : |classSum m ℓ L w r - cc * classCard A m ℓ r|
        = classCard A m ℓ r * |classSum m ℓ L w r / classCard A m ℓ r - cc| := by
      rw [h1, abs_mul, abs_of_nonneg hNpos.le]
    rw [hkey]
    calc classCard A m ℓ r * |classSum m ℓ L w r / classCard A m ℓ r - cc|
        ≤ classCard A m ℓ r * B := mul_le_mul_of_nonneg_left hSN hNpos.le
      _ = B * classCard A m ℓ r := by ring
  · -- no full block at this offset: both sides vanish
    have hzero : (m - (r : ℕ)) / ℓ = 0 := Nat.div_eq_of_lt (by omega)
    have hN0 : classCard A m ℓ r = 0 := by
      rw [classCard, hzero]; norm_num
    have hS0 : classSum m ℓ L w r = 0 := by
      rw [classSum]
      refine Finset.sum_eq_zero fun c _ => ?_
      have hemp : IsEmpty (Fin ((m - (r : ℕ)) / ℓ)) := by rw [hzero]; infer_instance
      exact hemp.elim c.2
    rw [hS0, hN0]
    norm_num

/-- The average of a word's block probability over the positions whose offset class lies in `R`. -/
noncomputable def posAvgR {A : Type*} [Fintype A] [DecidableEq A] (m ℓ : ℕ)
    (R : Finset (Fin ℓ)) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) : ℝ :=
  (∑ r ∈ R, classSum m ℓ L w r) / (∑ r ∈ R, classCard A m ℓ r)

/-- 🎯 **The capacity bound survives restriction to ANY sub-family of offset classes**, at the
*same* constant.  This is what base-`2^k` normality needs: the positions of a fixed residue mod
`k` are a union of offset classes whenever `k ∣ ℓ`. -/
theorem abs_posAvgR_sub_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ) (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂)
    (R : Finset (Fin ℓ)) (hR : 0 < ∑ r ∈ R, classCard A m ℓ r) :
    |posAvgR m ℓ R L w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) := by
  classical
  set cc : ℝ := 1 / (2 : ℝ) ^ ℓ with hcc
  set B : ℝ := 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * δ / ((m : ℝ) - ℓ + 1)) with hB
  set D : ℝ := ∑ r ∈ R, classCard A m ℓ r with hD
  have hsum : |(∑ r ∈ R, classSum m ℓ L w r) - cc * D| ≤ B * D := by
    have h1 : |(∑ r ∈ R, classSum m ℓ L w r) - cc * D|
        ≤ ∑ r ∈ R, |classSum m ℓ L w r - cc * classCard A m ℓ r| := by
      rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ r ∈ R, |classSum m ℓ L w r - cc * classCard A m ℓ r|
        ≤ ∑ r ∈ R, B * classCard A m ℓ r :=
      Finset.sum_le_sum fun r _ => abs_offset_class_le hℓ hℓm L w hδ hdef r
    rw [← Finset.mul_sum, ← hD] at h2
    linarith
  rw [posAvgR, ← hD]
  have hdiv : (∑ r ∈ R, classSum m ℓ L w r) / D - cc
      = ((∑ r ∈ R, classSum m ℓ L w r) - cc * D) / D := by
    field_simp
  rw [hdiv, abs_div, abs_of_pos hR, div_le_iff₀ hR]
  exact hsum

end NormalNumbers.G4Entropy
