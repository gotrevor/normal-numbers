/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyPositions
import NormalNumbers.G4EntropyRate
import NormalNumbers.Bridge
import NormalNumbers.Counting

/-!
# Entropy expedition §6: the transfer targets, and the refutation of `T_E`

The brief freezes three transfer statements over the *same* sampling family.  Here the family
is indexed by `i : ℕ` through `k₄ = 40000 + i`, `K = 4k₄` (so `K ≥ 160000`, the range where
`entropy_E1` holds), and the statements are

* `E0 x` — `H₂(Z^x_K)/(m_K H_K) → 1`;
* `T_E`  — `∀ x ∈ [0,1), E0 x → IsNormal 2 x`   (the brief's **primary** target).

`E0_primeLambertFour` upgrades `entropy_E1` to the genuine limit statement for `x = G₄`.

`T_E` is then **false**.  The witness is `G₄` masked to the sampled positions: `maskedReal`
keeps the digits of `G₄` at every position some scale actually samples and sets every other
digit to `0`.  By `G4EntropyLocality` the masked number has literally the same joint law at
every scale, so it satisfies `E0`; by `G4EntropyPositions` the sampled positions have density
`≤ 1/4`, so fewer than a quarter of its digits are `1` and it is not normal.

This is the outcome the brief calls for: *a precise counterexample satisfying the exact
premise*.  It says that no statement about this arithmetic sample alone — however strong —
can imply ordinary normality: the sample simply does not look at enough digits.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The frozen sampling family -/

/-- The block length `m_K = k₄` at family index `i`. -/
def kk (i : ℕ) : ℕ := 40000 + i

/-- The scale `K = 4k₄` at family index `i`. -/
def KK (i : ℕ) : ℕ := 4 * kk i

lemma KK_ge (i : ℕ) : 160000 ≤ KK i := by unfold KK kk; omega

lemma KK_one_le (i : ℕ) : 1 ≤ KK i := by have := KK_ge i; omega

lemma KK_hundred (i : ℕ) : 100 ≤ KK i := by have := KK_ge i; omega

/-- The grid at family index `i`. -/
noncomputable def gridAt (i : ℕ) : GridParams := gridOf (KK i) (N (KK i)) (KK_one_le i)

lemma b₀_lt_X_at (i : ℕ) : (gridAt i).b₀ < X (KK i) := b₀_lt_X (KK_hundred i)

/-- The digit positions the scale-`i` sample reads. -/
noncomputable def sampledPosAt (i : ℕ) : Finset ℕ :=
  sampledPos (gridAt i) (X (KK i)) (kk i)

/-- A digit position read by *some* admissible scale. -/
def IsSampled (j : ℕ) : Prop := ∃ i, j ∈ sampledPosAt i

/-- The joint quantized sample law at family index `i`. -/
noncomputable def jointLawAt (i : ℕ) (x : ℝ) :
    FinLaw ((gridAt i).Atom → Fin (2 ^ kk i)) :=
  jointLaw (gridAt i) (b₀_lt_X_at i) (kk i) x

/-- The maximal entropy `m_K · H_K` at family index `i`. -/
noncomputable def maxH (i : ℕ) : ℝ := (kk i : ℝ) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ)

/-! ### The transfer targets (brief §6) -/

/-- **E0**: the sample entropy is asymptotically maximal. -/
def E0 (x : ℝ) : Prop :=
  Tendsto (fun i => (jointLawAt i x).H₂ / maxH i) atTop (nhds 1)

/-- **`T_E`** (brief §6, the primary transfer target): `E0` implies ordinary binary
normality, for every `x ∈ [0,1)`. -/
def T_E : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → E0 x → IsNormal 2 x

/-! ### `E0` holds for `G₄` -/

lemma card_Atom_gridAt (i : ℕ) :
    Fintype.card (gridAt i).Atom = (KK i ^ 2 + 1) ^ KK i := by
  show Fintype.card (Fin (KK i) → Fin (KK i ^ 2 + 1)) = (KK i ^ 2 + 1) ^ KK i
  simp

lemma maxH_pos (i : ℕ) : 0 < maxH i := by
  unfold maxH
  have h1 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have h2 : (0 : ℝ) < (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    have : 0 < (KK i ^ 2 + 1) ^ KK i := pow_pos (by omega) _
    exact_mod_cast this
  positivity

set_option maxHeartbeats 1000000 in
/-- The ratio is at most `1` (the alphabet bound). -/
theorem ratio_le_one (i : ℕ) (x : ℝ) : (jointLawAt i x).H₂ / maxH i ≤ 1 := by
  have h := H₂_jointLaw_le_mul (gridAt i) (b₀_lt_X_at i) (kk i) x
  rw [card_Atom_gridAt i] at h
  rw [div_le_one (maxH_pos i)]
  exact h.trans_eq (by unfold maxH; push_cast; ring)

set_option maxHeartbeats 1000000 in
/-- The ratio is at least `1 − 200/√K` (from `entropy_E1`). -/
theorem one_sub_le_ratio (i : ℕ) :
    1 - 200 / Real.sqrt (KK i) ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ / maxH i := by
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have := KK_ge i
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : (0 : ℝ) < Real.sqrt (KK i) := Real.sqrt_pos.2 hKpos
  have hSsq : Real.sqrt (KK i) * Real.sqrt (KK i) = (KK i : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by
    unfold KK; push_cast; ring
  rw [le_div_iff₀ (maxH_pos i)]
  refine le_trans ?_ hE1.le
  -- `(1 − 200/√K)·(k₄ H) ≤ k₄ H − 50 √K H` because `200 k₄ = 50 K = 50 √K·√K`
  have hH : (0 : ℝ) ≤ (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by positivity
  have hkey : (200 / Real.sqrt (KK i)) * (kk i : ℝ) = 50 * Real.sqrt (KK i) := by
    field_simp
    nlinarith [hSsq, hk4]
  unfold maxH
  have : (1 - 200 / Real.sqrt (KK i)) * ((kk i : ℝ) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ))
      = (kk i : ℝ) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ)
        - ((200 / Real.sqrt (KK i)) * (kk i : ℝ)) * (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    ring
  rw [this, hkey]

lemma tendsto_KK_atTop : Tendsto (fun i => (KK i : ℝ)) atTop atTop := by
  have : ∀ i : ℕ, (i : ℝ) ≤ (KK i : ℝ) := by
    intro i
    have : i ≤ KK i := by unfold KK kk; omega
    exact_mod_cast this
  exact tendsto_atTop_mono this tendsto_natCast_atTop_atTop

lemma tendsto_deficit : Tendsto (fun i => 200 / Real.sqrt (KK i)) atTop (nhds 0) := by
  have h : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
  have h2 : Tendsto (fun i => (Real.sqrt (KK i))⁻¹) atTop (nhds 0) := by
    exact h.inv_tendsto_atTop
  have h3 := h2.const_mul (200 : ℝ)
  simpa [div_eq_mul_inv] using h3

/-- **`E0` holds for `G₄`** — the brief's qualitative target, as a genuine limit. -/
theorem E0_primeLambertFour : E0 (primeLambertAtBase 4) := by
  have hlo : Tendsto (fun i => 1 - 200 / Real.sqrt (KK i)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub tendsto_deficit
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun i => one_sub_le_ratio i) (fun i => ratio_le_one i _)

end NormalNumbers.G4.Sched
