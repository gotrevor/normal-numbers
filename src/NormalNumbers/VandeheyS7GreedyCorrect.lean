/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-GC: transducer correctness — the greedy output IS the image's continued fraction

The one link the §7 chain has never claimed (lap 89's handoff: "the last step, from digit
frequencies to `blockAvg`, is transducer-correctness … and is not claimed").  With the greedy run
of S7-GR it is a short induction.

* `cylMap_mob_mem_cfCylinder` — for `z ∈ (0,1)` the point `(cylMap u).mob z` lies in the cylinder
  `I_u`: reading a word and then evaluating produces exactly that word's digits.
* `factor_gOut` — the run identity, accumulated:
  `cylMap (gOut Φ x n) ∘ grunState Φ x n = Φ ∘ cylMap (digitWord x n)`.
* `mob_eq_cylMap_gOut` — hence `Φ.mob x = (cylMap (gOut Φ x n)).mob ((grunState Φ x n).mob (Gⁿx))`.
* `cfDigit_image_eq_gOut` — therefore the first `|gOut Φ x n|` continued-fraction digits of the
  IMAGE `Φ.mob x` are exactly the greedy output word, for every `n`:

      j < |gOut Φ x n|  →  cfDigit (Φ.mob x) j = (gOut Φ x n).getD j 0 .

This is the exact statement the lap-91 probe verified numerically to 120 digits (`z ↦ z/φ`); it is
now a theorem, for every map and every input with a genuine orbit whose image point is interior.

## Guard rule

**Content locator.**  `cylMap_mob_mem_cfCylinder` is the content; everything after it is the
`cylMap_append`/`comp_assoc` bookkeeping of S7-GR's step identity.

**Degenerate cases.**  `n = 0` gives the initial flush's word, which may be empty; the statement is
then vacuous.  The hypothesis `(grunState Φ x n).mob (Gⁿx) ∈ (0,1)` is what excludes the image
landing on a cylinder endpoint, and it is implied by irrationality of the image point.
-/
import NormalNumbers.VandeheyS7Greedy
import NormalNumbers.VandeheyS7CFRun

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-! ## Reading a word produces that word's digits -/

/-- **The cylinder identity.**  Evaluating `cylMap u` at an interior point lands in `I_u`. -/
theorem cylMap_mob_mem_cfCylinder : ∀ (u : List ℕ), (∀ e ∈ u, 1 ≤ e) → ∀ {z : ℝ},
    z ∈ Set.Ioo (0:ℝ) 1 → (cylMap u).mob z ∈ cfCylinder u
  | [], _, z, hz => by
      refine ⟨by simpa [cylMap_nil] using hz, ?_⟩
      intro i hi
      simp at hi
  | a :: u, hpos, z, hz => by
      have ha : 1 ≤ a := hpos a (by simp)
      have hu : ∀ e ∈ u, 1 ≤ e := fun e he => hpos e (by simp [he])
      have hinner : (cylMap u).mob z ∈ Set.Ioo (0:ℝ) 1 := cylMap_mapsTo_Ioo u hu hz
      have hih := cylMap_mob_mem_cfCylinder u hu hz
      have haR : (1:ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast ha
      have hval : (cylMap (a :: u)).mob z
          = (readMap ((a : ℕ) : ℝ) haR).mob ((cylMap u).mob z) := by
        rw [cylMap_cons ha, mob_comp _ _ ⟨hz.1.le, hz.2.le⟩]
      have hmem : (cylMap (a :: u)).mob z ∈ Set.Ioo (0:ℝ) 1 :=
        cylMap_mapsTo_Ioo (a :: u) hpos hz
      refine ⟨hmem, ?_⟩
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · -- the first digit is `a`
        have hgauss : gaussMap ((cylMap (a :: u)).mob z) = (cylMap u).mob z := by
          rw [hval]
          exact gaussMap_readMap_mob ha hinner
        have hfl : cfDigit ((cylMap (a :: u)).mob z) 0 = a := by
          have hexp : (cylMap (a :: u)).mob z = ((cylMap u).mob z + ((a : ℕ) : ℝ))⁻¹ := by
            rw [hval, readMap_mob, one_div]
          have h1 : (0:ℝ) < (cylMap u).mob z + ((a : ℕ) : ℝ) := by
            have := hinner.1; linarith
          rw [cfDigit, Function.iterate_zero_apply, hexp, inv_inv]
          have hlo : ((a : ℕ) : ℝ) ≤ (cylMap u).mob z + ((a : ℕ) : ℝ) := by
            have := hinner.1; linarith
          have hhi : (cylMap u).mob z + ((a : ℕ) : ℝ) < ((a : ℕ) : ℝ) + 1 := by
            have := hinner.2; linarith
          rw [Nat.floor_eq_iff (by positivity)]
          exact ⟨hlo, by push_cast; linarith⟩
        simpa using hfl
      · -- later digits come from `u`
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        have hju : j < u.length := by
          simp only [List.length_cons] at hi
          omega
        have hgauss : gaussMap ((cylMap (a :: u)).mob z) = (cylMap u).mob z := by
          rw [hval]
          exact gaussMap_readMap_mob ha hinner
        have hshift : cfDigit ((cylMap (a :: u)).mob z) (j + 1)
            = cfDigit ((cylMap u).mob z) j := by
          rw [cfDigit, cfDigit, Function.iterate_succ_apply, hgauss]
        rw [hshift, hih.2 j hju]
        simp

/-! ## The accumulated output of the greedy run -/

/-- The greedy run's output word after `n` reads. -/
noncomputable def gOut (Φ : MapState) (x : ℝ) : ℕ → List ℕ
  | 0 => flushWord Φ
  | n + 1 => gOut Φ x n ++ grunWord Φ x n

lemma gOut_pos (Φ : MapState) (x : ℝ) (n : ℕ) : ∀ a ∈ gOut Φ x n, 1 ≤ a := by
  induction n with
  | zero => exact flushWord_pos Φ
  | succ k ih =>
      intro a ha
      rw [gOut, List.mem_append] at ha
      rcases ha with ha | ha
      · exact ih a ha
      · exact grunWord_pos Φ x k a ha

lemma gOut_prefix (Φ : MapState) (x : ℝ) (n : ℕ) : gOut Φ x n <+: gOut Φ x (n + 1) :=
  ⟨grunWord Φ x n, rfl⟩

/-- The input word actually read by the run (the clamped digits). -/
noncomputable def inWord (x : ℝ) (n : ℕ) : List ℕ := (List.range n).map (inDigit x)

lemma inWord_pos (x : ℝ) (n : ℕ) : ∀ a ∈ inWord x n, 1 ≤ a := by
  intro a ha
  simp only [inWord, List.mem_map, List.mem_range] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact one_le_inDigit x i

lemma inWord_succ (x : ℝ) (n : ℕ) : inWord x (n + 1) = inWord x n ++ [inDigit x n] := by
  simp [inWord, List.range_succ]

lemma cylMap_singleton_inDigit (x : ℝ) (n : ℕ) : cylMap [inDigit x n] = readAt x n := by
  rw [cylMap_singleton (one_le_inDigit x n), readAt]

/-- **The run identity, accumulated.** -/
theorem factor_gOut (Φ : MapState) (x : ℝ) (n : ℕ) :
    (cylMap (gOut Φ x n)).comp (grunState Φ x n) = Φ.comp (cylMap (inWord x n)) := by
  induction n with
  | zero =>
      rw [gOut, inWord]
      simp only [List.range_zero, List.map_nil, cylMap_nil, comp_idMap]
      exact grunState_zero Φ x
  | succ k ih =>
      rw [gOut, cylMap_append _ _ (gOut_pos Φ x k), comp_assoc, grunState_succ Φ x k,
        ← comp_assoc, ih, comp_assoc, inWord_succ,
        cylMap_append _ _ (inWord_pos x k), cylMap_singleton_inDigit]

/-- **Correctness, as an evaluation.** -/
theorem mob_eq_cylMap_gOut (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    Φ.mob x = (cylMap (gOut Φ x n)).mob ((grunState Φ x n).mob (gaussMap^[n] x)) := by
  have hxn : gaussMap^[n] x ∈ Set.Ioo (0:ℝ) 1 := hx n
  have hin : inWord x n = digitWord x n := by
    simp only [inWord, digitWord]
    exact List.map_congr_left fun i _ => inDigit_eq_cfDigit hx i
  have hfac := factor_gOut Φ x n
  have hval : (Φ.comp (cylMap (inWord x n))).mob (gaussMap^[n] x) = Φ.mob x := by
    rw [mob_comp _ _ ⟨hxn.1.le, hxn.2.le⟩, hin, cylMap_digitWord_mob hx n]
  rw [← hval, ← hfac, mob_comp _ _ ⟨hxn.1.le, hxn.2.le⟩]

/-- **S7-GC: transducer correctness.**  The greedy output word is a prefix of the continued
fraction of the image. -/
theorem cfDigit_image_eq_gOut (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ)
    (hinner : (grunState Φ x n).mob (gaussMap^[n] x) ∈ Set.Ioo (0:ℝ) 1) :
    ∀ j < (gOut Φ x n).length, cfDigit (Φ.mob x) j = (gOut Φ x n).getD j 0 := by
  intro j hj
  have hmem := cylMap_mob_mem_cfCylinder (gOut Φ x n) (gOut_pos Φ x n) hinner
  rw [mob_eq_cylMap_gOut Φ hx n]
  exact hmem.2 j hj

/-- The image lies in the cylinder of the output word. -/
theorem image_mem_cfCylinder_gOut (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ)
    (hinner : (grunState Φ x n).mob (gaussMap^[n] x) ∈ Set.Ioo (0:ℝ) 1) :
    Φ.mob x ∈ cfCylinder (gOut Φ x n) := by
  rw [mob_eq_cylMap_gOut Φ hx n]
  exact cylMap_mob_mem_cfCylinder (gOut Φ x n) (gOut_pos Φ x n) hinner

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.cylMap_mob_mem_cfCylinder
#print axioms NormalNumbers.VandeheyS7.MapState.factor_gOut
#print axioms NormalNumbers.VandeheyS7.MapState.mob_eq_cylMap_gOut
#print axioms NormalNumbers.VandeheyS7.MapState.cfDigit_image_eq_gOut

end Audit
