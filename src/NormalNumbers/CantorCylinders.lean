/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorSelfSimilar

/-!
# Depth-`m` cylinder decomposition of `pushFourier`

Iterating `pushFourier_self_similar`:
`pushFourier F ξ = 2^{-m} Σ_{|w| = m} pushFourier (F ∘ φ_w) ξ`, with `φ_w t = offs w + t / 4^m`
(`pushFourier_cylinders`).  Step 2 of the Phase 3 plan for `ExplicitOmegaK.polyDecay_Gk`.
-/

open MeasureTheory

namespace NormalNumbers.CantorCylinders

open ExplicitSquare CantorSelfSimilar

/-- All coin words of length `m`. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (words m).map (true :: ·) ++ (words m).map (false :: ·)

theorem length_words (m : ℕ) : (words m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [words, ih, pow_succ]; ring

theorem length_of_mem_words {m : ℕ} {w : List Bool} (hw : w ∈ words m) : w.length = m := by
  induction m generalizing w with
  | zero => simp [words] at hw; simp [hw]
  | succ m ih =>
    simp only [words, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

/-- Offset of the affine map `φ_w`. -/
noncomputable def offs : List Bool → ℝ
  | [] => 0
  | c :: w => 3 / 8 + (if c then 1 / 8 else 0) + offs w / 4

/-- The cylinder map `φ_w t = offs w + t / 4^{|w|}`. -/
noncomputable def phi (w : List Bool) (t : ℝ) : ℝ := offs w + t / 4 ^ w.length

theorem psi_comp_phi (c : Bool) (w : List Bool) : psi c ∘ phi w = phi (c :: w) := by
  funext t
  simp only [Function.comp, psi, phi, offs, List.length_cons, pow_succ]
  field_simp
  ring

theorem continuous_psi (c : Bool) : Continuous (psi c) := by
  unfold psi; fun_prop

/-- **Depth-`m` self-similarity of `pushFourier`.** -/
theorem pushFourier_cylinders (m : ℕ) (F : ℝ → ℝ) (hF : Measurable F) (ξ : ℝ) :
    pushFourier F ξ = ((2 : ℂ) ^ m)⁻¹ * ((words m).map fun w => pushFourier (F ∘ phi w) ξ).sum := by
  induction m generalizing F with
  | zero =>
    simp [words]
    congr 1; funext t; simp [phi, offs]
  | succ m ih =>
    rw [pushFourier_self_similar F hF ξ, ih _ (hF.comp (continuous_psi true).measurable),
      ih _ (hF.comp (continuous_psi false).measurable)]
    simp only [words, List.map_append, List.map_map, List.sum_append, Function.comp_assoc,
      psi_comp_phi]
    simp only [Function.comp_def]
    ring

/-- Cylinder maps send the window `[1/2, 1]` into itself. -/
theorem phi_mem_window (w : List Bool) {t : ℝ} (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    phi w t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  induction w generalizing t with
  | nil => simpa [phi, offs] using ht
  | cons c w ih =>
    rw [← psi_comp_phi]
    have := ih ht
    simp only [Function.comp, psi]
    constructor <;> split_ifs <;> linarith [this.1, this.2]

theorem nodup_words (m : ℕ) : (words m).Nodup := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    simp only [words]
    refine List.Nodup.append (ih.map fun _ _ h => List.cons_injective h)
      (ih.map fun _ _ h => List.cons_injective h) ?_
    simp [List.disjoint_left]

/-- Range of the offsets: `offs w ∈ [1/2 − 4^{-|w|}/2, 1 − 4^{-|w|}]`. -/
theorem offs_mem (w : List Bool) :
    1 / 2 - 1 / 4 ^ w.length / 2 ≤ offs w ∧ offs w ≤ 1 - 1 / 4 ^ w.length := by
  have h1 := phi_mem_window w (t := 1 / 2) ⟨le_rfl, by norm_num⟩
  have h2 := phi_mem_window w (t := 1) ⟨by norm_num, le_rfl⟩
  simp only [phi, Set.mem_Icc] at h1 h2
  have : (1 / 2 : ℝ) / 4 ^ w.length = 1 / 4 ^ w.length / 2 := by ring
  constructor <;> [linarith [h1.1]; linarith [h2.2]]

/-- **Separation of the offsets**: distinct words of equal length `m` have offsets at least
`4^{-m}/2` apart (the cylinder intervals have disjoint interiors). -/
theorem offs_sep : ∀ (w w' : List Bool), w.length = w'.length → w ≠ w' →
    1 / 4 ^ w.length / 2 ≤ |offs w - offs w'|
  | [], [], _, h => absurd rfl h
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: v, c' :: v', hl, hne => by
    simp only [List.length_cons, add_left_inj] at hl
    simp only [offs, List.length_cons, pow_succ]
    have hL : (0 : ℝ) < 4 ^ v.length := by positivity
    by_cases hc : c = c'
    · subst hc
      have hv : v ≠ v' := fun h => hne (by rw [h])
      have := offs_sep v v' hl hv
      rw [show 3 / 8 + (if c then (1 : ℝ) / 8 else 0) + offs v / 4 -
          (3 / 8 + (if c then 1 / 8 else 0) + offs v' / 4) = (offs v - offs v') / 4 by ring,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc 1 / (4 ^ v.length * 4) / 2 = 1 / 4 ^ v.length / 2 / 4 := by ring
        _ ≤ |offs v - offs v'| / 4 := by gcongr
    · have a := offs_mem v
      have b := offs_mem v'
      rw [← hl] at b
      have e1 : (4 : ℝ)⁻¹ * (4 ^ v.length)⁻¹ / 2 = 1 / 4 ^ v.length / 8 := by ring
      rcases Bool.eq_false_or_eq_true c with rfl | rfl <;>
      rcases Bool.eq_false_or_eq_true c' with rfl | rfl <;> simp at hc ⊢
      · rw [le_abs]; left; linarith
      · rw [le_abs]; right; linarith

/-- **Few cylinders near a point**: at most `4 R 4^m + 2` words of length `m` have offset within
`R` of `z`. -/
theorem card_near_le (m : ℕ) (z R : ℝ) (hR : 0 ≤ R) :
    (((words m).toFinset.filter fun w => |offs w - z| ≤ R).card : ℝ) ≤ 4 * R * 4 ^ m + 2 := by
  classical
  set δ : ℝ := 1 / 4 ^ m / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set S := (words m).toFinset.filter fun w => |offs w - z| ≤ R
  let f : List Bool → ℤ := fun w => ⌊offs w / δ⌋
  have hinj : Set.InjOn f S := by
    intro w hw w' hw' hf
    by_contra hne
    simp only [S, Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hw hw'
    have hl : w.length = w'.length := by
      rw [length_of_mem_words hw.1, length_of_mem_words hw'.1]
    have hs := offs_sep w w' hl hne
    rw [length_of_mem_words hw.1] at hs
    have h1 := Int.floor_le (offs w / δ)
    have h2 := Int.lt_floor_add_one (offs w / δ)
    have h3 := Int.floor_le (offs w' / δ)
    have h4 := Int.lt_floor_add_one (offs w' / δ)
    simp only [f] at hf
    rw [hf] at h1 h2
    have : |offs w / δ - offs w' / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ0, div_lt_one hδ0] at this
    linarith
  have hmaps : Set.MapsTo f S (Finset.Icc ⌊(z - R) / δ⌋ ⌊(z + R) / δ⌋) := by
    intro w hw
    simp only [S, Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq, abs_le] at hw
    simp only [Finset.coe_Icc, Set.mem_Icc, f]
    constructor <;> apply Int.floor_mono <;> gcongr <;> linarith [hw.2.1, hw.2.2]
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Int.card_Icc] at hcard
  have hc : (S.card : ℝ) ≤ ((⌊(z + R) / δ⌋ + 1 - ⌊(z - R) / δ⌋).toNat : ℝ) := by exact_mod_cast hcard
  refine hc.trans ?_
  have hnn : 0 ≤ ⌊(z + R) / δ⌋ + 1 - ⌊(z - R) / δ⌋ := by
    have : ⌊(z - R) / δ⌋ ≤ ⌊(z + R) / δ⌋ := Int.floor_mono (by gcongr; linarith)
    omega
  have : ((⌊(z + R) / δ⌋ + 1 - ⌊(z - R) / δ⌋).toNat : ℝ) =
      ((⌊(z + R) / δ⌋ + 1 - ⌊(z - R) / δ⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [this]
  push_cast
  have a1 := Int.floor_le ((z + R) / δ)
  have a2 := Int.lt_floor_add_one ((z - R) / δ)
  have : (z + R) / δ - (z - R) / δ = 4 * R * 4 ^ m := by
    rw [hδ]; field_simp; ring
  linarith

end NormalNumbers.CantorCylinders
