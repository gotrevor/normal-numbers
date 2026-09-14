/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyOffset

/-!
# Entropy expedition — restricting the sample to a subset of coordinates (route E-T8)

The normal real of `G4EntropyBlockWord` reuses each sampled position `rep m` times, so its
position map is **not** injective.  Trigger `E-T8` asks for a strictly increasing `samplePos`,
i.e. a genuine subsequence of `G₄`'s digits.  The only known route is to split one scale's
window collection into many *disjoint* good sub-collections, so that repetition is replaced by
fresh windows.  This module proves the affirmative half of that route: **what a sub-collection
of coordinates costs**.

* `restrictCoords`/`padG` — restriction of a window family to a subset `G` of coordinates.
* `H₂_restrictCoords_ge` — dropping `|A| − |G|` coordinates costs at most `(|A| − |G|)·m` bits,
  so a *total* deficit of `δ·|A|` survives restriction unchanged: the restricted law has
  per-coordinate deficit `δ·|A|/|G|`, i.e. `δ/ρ` at relative size `ρ`.
* `abs_posAvg_restrict_sub_le` — hence the sub-collection's word frequency obeys the same
  capacity bound with `δ` replaced by `δ/ρ`: the cost of restriction is `√(1/ρ)`, not `1/ρ`.

The consequence for `E-T8` is quantitative and is recorded in `PENDING_WORK.md`: a
sub-collection is usable only while `δ/ρ = o(m)`, i.e. `ρ ≫ 200·ℓ/√K`, so a scale admits at most
`O(√K)` disjoint good chunks — while replacing repetition needs `L_{i+1}/L_i ≈ K²` of them.

Nothing here mentions `G₄`.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy
namespace FinLaw

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The window family restricted to the coordinates in `G`. -/
def restrictCoords (G : Finset A) (m : ℕ) (z : A → Fin (2 ^ m)) : (↥G) → Fin (2 ^ m) :=
  fun α => z (α : A)

/-- Padding a restricted family back out by zero. -/
def padG (G : Finset A) (m : ℕ) (v : (↥G) → Fin (2 ^ m)) : A → Fin (2 ^ m) :=
  fun α => if h : α ∈ G then v ⟨α, h⟩ else ⟨0, Nat.two_pow_pos m⟩

lemma padG_injective (G : Finset A) (m : ℕ) : Function.Injective (padG G m) := by
  intro v v' h
  funext α
  have := congrFun h (α : A)
  rw [padG, padG, dif_pos α.2, dif_pos α.2] at this
  exact this

/-- The coordinate split used for subadditivity: the restricted family (padded out) together
with the individual dropped coordinates. -/
def splitG (G : Finset A) (m : ℕ) :
    Option (↥(Gᶜ)) → (A → Fin (2 ^ m)) → (A → Fin (2 ^ m))
  | none => fun z => padG G m (restrictCoords G m z)
  | some β => fun z => fun _ => z (β : A)

/-- **Restricting the coordinates costs at most `m` bits per dropped coordinate.**  Hence a
law with total deficit `δ·|A|` restricts to a law on `|G|` coordinates with the *same* total
deficit — per coordinate, `δ·|A|/|G|`. -/
theorem H₂_restrictCoords_ge (G : Finset A) (m : ℕ) (L : FinLaw (A → Fin (2 ^ m))) :
    L.H₂ - ((Fintype.card A : ℝ) - (G.card : ℝ)) * m
      ≤ (L.map (restrictCoords G m)).H₂ := by
  classical
  have hinj : Function.Injective
      (fun z : A → Fin (2 ^ m) => fun i => splitG G m i z) := by
    intro z z' h
    funext α
    by_cases hα : α ∈ G
    · have hnone := congrFun (congrFun h none) α
      simp only [splitG, padG, restrictCoords, dif_pos hα] at hnone
      exact hnone
    · have hβ : α ∈ Gᶜ := Finset.mem_compl.2 hα
      have hsome := congrFun (congrFun h (some ⟨α, hβ⟩)) α
      simpa [splitG] using hsome
  have hsub := L.H₂_le_sum_H₂_map (fun i => splitG G m i) hinj
  rw [Fintype.sum_option] at hsub
  -- the restricted family keeps its entropy
  have hrestH : (L.map (splitG G m none)).H₂ = (L.map (restrictCoords G m)).H₂ :=
    L.H₂_map_congr_comp (restrictCoords G m) (padG_injective G m) (splitG G m none)
      (fun z => rfl)
  -- each dropped coordinate carries at most `m` bits
  have hdrop : ∀ β : ↥(Gᶜ), (L.map (splitG G m (some β))).H₂ ≤ (m : ℝ) := by
    intro β
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    set T : Finset (A → Fin (2 ^ m)) :=
      Finset.image (fun u : Fin (2 ^ m) => (fun _ : A => u)) Finset.univ with hT
    have hsupp : ∀ v : A → Fin (2 ^ m), (L.map (splitG G m (some β))).p v ≠ 0 → v ∈ T := by
      intro v hv
      rw [FinLaw.map_p] at hv
      have hne : (Finset.univ.filter
          (fun z : A → Fin (2 ^ m) => splitG G m (some β) z = v)).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        rw [hcon] at hv
        simp at hv
      obtain ⟨z, hz⟩ := hne
      rw [Finset.mem_filter] at hz
      refine Finset.mem_image.mpr ⟨z (β : A), Finset.mem_univ _, ?_⟩
      funext γ
      have := congrFun hz.2 γ
      simpa [splitG] using this
    have hcard : T.card ≤ 2 ^ m := by
      calc T.card ≤ (Finset.univ : Finset (Fin (2 ^ m))).card := Finset.card_image_le
        _ = 2 ^ m := by simp
    have h := (L.map (splitG G m (some β))).H₂_le_logb hpos T hsupp hcard
    have hlg : Real.logb 2 ((2 ^ m : ℕ) : ℝ) = (m : ℝ) := by
      rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m by push_cast; ring, Real.logb, Real.log_pow]
      have hne : Real.log 2 ≠ 0 := by
        have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
        linarith
      field_simp
    rwa [hlg] at h
  have hsum : ∑ β : ↥(Gᶜ), (L.map (splitG G m (some β))).H₂
      ≤ ((Fintype.card A : ℝ) - (G.card : ℝ)) * m := by
    have hcount : (Fintype.card (↥(Gᶜ)) : ℝ)
        = (Fintype.card A : ℝ) - (G.card : ℝ) := by
      rw [Fintype.card_coe, Finset.card_compl]
      have : G.card ≤ Fintype.card A := Finset.card_le_univ G
      push_cast [Nat.cast_sub this]
      ring
    calc ∑ β : ↥(Gᶜ), (L.map (splitG G m (some β))).H₂
        ≤ ∑ _β : ↥(Gᶜ), (m : ℝ) := Finset.sum_le_sum fun β _ => hdrop β
      _ = ((Fintype.card A : ℝ) - (G.card : ℝ)) * m := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcount]
  rw [hrestH] at hsub
  linarith

end FinLaw

/-- **The sub-collection capacity bound.**  A window collection with per-coordinate deficit `δ`
restricts to any nonempty sub-collection `G` of relative size `ρ = |G|/|A|` with per-coordinate
deficit `δ/ρ`; hence every `ℓ`-block word's frequency over the sub-collection's windows obeys

    `|posAvg (L.map (restrictCoords G m)) w − 2^{−ℓ}| ≤ 2√(log 2 · ℓ · (δ|A|/|G|) / (m−ℓ+1))`.

The restriction cost is `√(1/ρ)`, not `1/ρ`. -/
theorem abs_posAvg_restrict_sub_le {A : Type*} [Fintype A] [DecidableEq A] {m ℓ : ℕ}
    (hℓ : 0 < ℓ) (hℓm : ℓ ≤ m) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ))
    {δ : ℝ} (hδ : 0 < δ) (hdef : ((m : ℝ) - δ) * (Fintype.card A : ℝ) ≤ L.H₂)
    (G : Finset A) (hG : G.Nonempty) :
    |posAvg m ℓ (L.map (FinLaw.restrictCoords G m)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ)
          * (δ * (Fintype.card A : ℝ) / (G.card : ℝ)) / ((m : ℝ) - ℓ + 1)) := by
  classical
  have : Nonempty (↥G) := ⟨⟨hG.choose, hG.choose_spec⟩⟩
  have hGcard : (0 : ℝ) < (G.card : ℝ) := by
    have := Finset.card_pos.2 hG
    exact_mod_cast this
  have hcoe : (Fintype.card (↥G) : ℝ) = (G.card : ℝ) := by
    rw [Fintype.card_coe]
  have hrest := FinLaw.H₂_restrictCoords_ge G m L
  have hδ' : 0 < δ * (Fintype.card A : ℝ) / (G.card : ℝ) := by
    have hA : (0 : ℝ) < (Fintype.card A : ℝ) := by
      have : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨hG.choose⟩
      exact_mod_cast this
    positivity
  have hdef' : ((m : ℝ) - δ * (Fintype.card A : ℝ) / (G.card : ℝ))
      * (Fintype.card (↥G) : ℝ) ≤ (L.map (FinLaw.restrictCoords G m)).H₂ := by
    rw [hcoe]
    have hexp : ((m : ℝ) - δ * (Fintype.card A : ℝ) / (G.card : ℝ)) * (G.card : ℝ)
        = (m : ℝ) * (G.card : ℝ) - δ * (Fintype.card A : ℝ) := by
      field_simp
    rw [hexp]
    have hd : (m : ℝ) * (Fintype.card A : ℝ) - δ * (Fintype.card A : ℝ) ≤ L.H₂ := by
      nlinarith [hdef]
    linarith
  exact abs_posAvg_sub_le hℓ hℓm _ w hδ' hdef'

end NormalNumbers.G4Entropy
