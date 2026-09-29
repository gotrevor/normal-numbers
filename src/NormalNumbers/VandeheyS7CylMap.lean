/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CM: the input word contracts — geometrically, with no continuants

`clockUnbounded` (S7-PN) reduces by S7-EE2 to "the state's width tends to `0` along the input
orbit", and by `width_comp_le` to the decay of `width (cylMap w)` as the input word `w` grows.

The usual route is continuants (`width = 1/(K_w (K_w + K_{w-1}))`, `K_w ≥ fib`).  This module takes
a shorter one: **two consecutive reads contract by `1/4`, unconditionally**.  The matrix of
`readMap a ∘ readMap b` is `[[1, b], [a, ab+1]]`, with determinant `1` and smallest denominator
`ab + 1 ≥ 2`, so its Lipschitz constant on `[0,1]` is `1/(ab+1)² ≤ 1/4` — no arithmetic of
continuants, no `fib`, and the bound is uniform in the digits.  Hence

    width (cylMap w) ≤ (1/4) ^ (|w| / 2)      (`width_cylMap_le`)

and `cylMap` is `readMap`-composition, so this is the contraction the transducer runs on.  The one
digit of slack (`|w|/2`, integer division) is the price of pairing and is irrelevant.
-/
import NormalNumbers.VandeheyS7EmitEv

namespace NormalNumbers.VandeheyS7

open Set

namespace MapState

/-- The identity state. -/
noncomputable def idMap : MapState where
  a := 1
  b := 0
  c := 0
  d := 1
  hd := one_pos
  hcd := by norm_num
  hb0 := le_refl 0
  hbd := zero_le_one
  hab0 := by norm_num
  habcd := by norm_num
  hdet := by norm_num

@[simp] lemma idMap_mob (z : ℝ) : idMap.mob z = z := by
  show ((1:ℝ) * z + 0) / (0 * z + 1) = z
  ring_nf

/-- Composition is associative — it is the matrix product. -/
theorem comp_assoc (s t u : MapState) : (s.comp t).comp u = s.comp (t.comp u) := by
  refine ext_entries ?_ ?_ ?_ ?_ <;> simp only [comp_a, comp_b, comp_c, comp_d] <;> ring

/-- The Lipschitz constant of a state on `[0,1]`. -/
noncomputable def lipConst (s : MapState) : ℝ := |s.a * s.d - s.b * s.c| / s.minDen ^ 2

theorem width_comp_le' (s t : MapState) : (s.comp t).width ≤ s.lipConst * t.width :=
  s.width_comp_le t

/-- The image lies in `[0,1]`, so the width never exceeds `1`. -/
theorem width_le_one (s : MapState) : s.width ≤ 1 := by
  have h0 := s.mapsTo ⟨le_refl (0:ℝ), zero_le_one⟩
  have h1 := s.mapsTo ⟨zero_le_one, le_refl (1:ℝ)⟩
  rw [width, abs_le]
  constructor <;> [linarith [h0.1, h0.2, h1.1, h1.2]; linarith [h0.1, h0.2, h1.1, h1.2]]

/-- **Two reads contract by `1/4`.**  `readMap a ∘ readMap b = [[1, b], [a, ab+1]]`, determinant
`1`, smallest denominator `ab + 1 ≥ 2`. -/
theorem lipConst_readMap_comp {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((readMap a ha).comp (readMap b hb)).lipConst ≤ 1 / 4 := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  set s := (readMap a ha).comp (readMap b hb) with hs
  have hsa : s.a = 1 := by simp [hs, comp_a, readMap]
  have hsb : s.b = b := by simp [hs, comp_b, readMap]
  have hsc : s.c = a := by simp [hs, comp_c, readMap]
  have hsd : s.d = a * b + 1 := by
    show (1:ℝ) * 1 + a * b = a * b + 1
    ring
  have hdet : |s.a * s.d - s.b * s.c| = 1 := by
    rw [hsa, hsb, hsc, hsd]
    have : (1:ℝ) * (a * b + 1) - b * a = 1 := by ring
    rw [this, abs_one]
  have hmin : s.minDen = a * b + 1 := by
    rw [minDen, hsc, hsd]
    exact min_eq_left (by nlinarith)
  have hge : (2:ℝ) ≤ a * b + 1 := by nlinarith
  rw [lipConst, hdet, hmin]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-! ## The cylinder map of an input word -/

/-- `cylMap w : z ↦ [0; w₁, …, w_k + z]`, as a `MapState`. -/
noncomputable def cylMap : List ℕ → MapState
  | [] => idMap
  | a :: w =>
      if ha : 1 ≤ a then (readMap (a : ℝ) (by exact_mod_cast ha)).comp (cylMap w)
      else idMap

@[simp] lemma cylMap_nil : cylMap [] = idMap := rfl

lemma cylMap_cons {a : ℕ} (ha : 1 ≤ a) (w : List ℕ) :
    cylMap (a :: w) = (readMap (a : ℝ) (by exact_mod_cast ha)).comp (cylMap w) := by
  rw [cylMap]; exact dif_pos ha

/-- **S7-CM.**  The input word contracts geometrically, uniformly in the digits. -/
theorem width_cylMap_le : ∀ w : List ℕ, (∀ e ∈ w, 1 ≤ e) →
    (cylMap w).width ≤ (1 / 4 : ℝ) ^ (w.length / 2)
  | [], _ => by simpa using (cylMap []).width_le_one
  | [a], _ => by simpa using (cylMap [a]).width_le_one
  | a :: b :: w, hpos => by
      have ha : 1 ≤ a := hpos a (by simp)
      have hb : 1 ≤ b := hpos b (by simp)
      have ha1 : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hb1 : (1:ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hw : ∀ e ∈ w, 1 ≤ e := fun e he => hpos e (by simp [he])
      have hstruct : cylMap (a :: b :: w)
          = ((readMap (a : ℝ) ha1).comp (readMap (b : ℝ) hb1)).comp (cylMap w) := by
        rw [cylMap_cons ha, cylMap_cons hb, comp_assoc]
      have hIH := width_cylMap_le w hw
      have hlen : (a :: b :: w).length / 2 = w.length / 2 + 1 := by
        simp [List.length_cons]; omega
      rw [hstruct, hlen, pow_succ]
      calc (((readMap (a : ℝ) ha1).comp (readMap (b : ℝ) hb1)).comp (cylMap w)).width
          ≤ ((readMap (a : ℝ) ha1).comp (readMap (b : ℝ) hb1)).lipConst * (cylMap w).width :=
            width_comp_le' _ _
        _ ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ (w.length / 2) := by
            refine mul_le_mul (lipConst_readMap_comp ha1 hb1) hIH (cylMap w).width_nonneg
              (by norm_num)
        _ = (1 / 4 : ℝ) ^ (w.length / 2) * (1 / 4 : ℝ) := by ring

/-- The contraction, in the limit form `clockUnbounded` needs. -/
theorem tendsto_width_cylMap {v : ℕ → List ℕ} (hpos : ∀ n, ∀ e ∈ v n, 1 ≤ e)
    (hlen : Filter.Tendsto (fun n => (v n).length) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (cylMap (v n)).width) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun n => (cylMap (v n)).width_nonneg)
    (fun n => width_cylMap_le (v n) (hpos n)) ?_
  have hq : Filter.Tendsto (fun m : ℕ => (1 / 4 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine hq.comp ?_
  refine Filter.tendsto_atTop_atTop.2 fun k => ?_
  obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.1 hlen (2 * k)
  exact ⟨M, fun n hn => by have := hM n hn; omega⟩

end MapState

section Audit

#print axioms MapState.lipConst_readMap_comp
#print axioms MapState.width_cylMap_le
#print axioms MapState.tendsto_width_cylMap

end Audit

end NormalNumbers.VandeheyS7
