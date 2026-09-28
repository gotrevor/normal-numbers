/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheySerret

/-!
# The leaf reduction, per matrix

`LiteratureVandehey.vandehey_matrix_action_of_uniformFreq` runs the either-or endgame for ALL
nonsingular integer matrices at once, because that is the shape of the crux `VandeheyUniformFreq`.
The leaf route of `VandeheySmith` needs it **one matrix at a time**: the only open leaf is
`MobiusCFNScale`, i.e. `x ↦ p·x` for prime `p`, and what the §5–§6 output-frequency engine
(`VandeheyOutputFreq`) delivers is an `x`-independent *limit* for a single map, not a value.

So this file isolates the per-matrix either-or:

* `MobiusUniformFreq a b c d` — for every genuine word, the window frequency in the image's CF
  expansion converges to a limit that does not depend on which CF-normal `x` is fed in.
* `mobiusCFN_of_uniformFreq` — for a nonsingular matrix that implies `MobiusCFN`.  The limit is
  pinned by the pigeonhole witness of `exists_cfNormal_with_cfNormal_image`: one CF-normal `x₀`
  whose image is also CF-normal forces `L = γ(I_v)`.
* `ScaleUniformFreq` / `mobiusCFNScale_of_scaleUniformFreq` /
  `vandeheyUniformFreq_of_scaleUniformFreq` — the chain down to the headline.  After this the
  whole of Vandehey 2017 Theorem 1.1 rests on ONE statement about the single map `x ↦ p·x`:
  that its output window frequencies have an `x`-independent limit.  No frequency value is ever
  asserted, exactly as in the paper.
-/

namespace NormalNumbers.Literature

open Filter

/-- **The per-matrix uniform-frequency statement.**  For every genuine CF word `v`, the window
frequency of `v` in the CF expansion of `Mx` converges to a limit `L` that does **not** depend on
which CF-normal `x` is fed in.  No value of `L` is asserted.  This is `VandeheyUniformFreq` at a
single matrix. -/
def MobiusUniformFreq (a b c d : ℤ) : Prop :=
  ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) →
    ∃ L : ℝ, ∀ x : ℝ, (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
      Tendsto
        (fun p => (countOccurrences v ((List.range p).map
            (cfDigit (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))))) : ℝ) / p)
        atTop (nhds L)

/-- **The either-or endgame, one matrix at a time.**  An `x`-independent limit plus the
pigeonhole witness gives `MobiusCFN`: the witness' image is CF-normal, so its frequency limit is
`γ(I_v)`, and uniqueness of limits transports that value to every CF-normal input. -/
theorem mobiusCFN_of_uniformFreq (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (h : MobiusUniformFreq a b c d) : MobiusCFN a b c d := by
  intro x hden hx v hne hpos
  obtain ⟨L, hL⟩ := h v hne hpos
  obtain ⟨x₀, _, hx₀den, hx₀n, hx₀img⟩ :=
    exists_cfNormal_with_cfNormal_image a b c d hdet
  have hLγ : L = (gaussMeasure (cfCylinder v)).toReal :=
    tendsto_nhds_unique (hL x₀ hx₀den hx₀n) (hx₀img v hne hpos)
  exact hLγ ▸ hL x hden hx

/-- **Content locator** (guard rule): the identity matrix satisfies `MobiusUniformFreq`, with the
limit read off the input's own normality.  This is where the content is *not*. -/
theorem mobiusUniformFreq_one : MobiusUniformFreq 1 0 0 1 := by
  intro v hne hpos
  refine ⟨(gaussMeasure (cfCylinder v)).toReal, fun x _ hx => ?_⟩
  have h1 : ((1 : ℤ) : ℝ) * x + ((0 : ℤ) : ℝ) = x := by push_cast; ring
  have h2 : ((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ) = 1 := by push_cast; ring
  simpa [h1, h2] using hx v hne hpos

/-- `gaussMap` fixes `0`, so the junk expansion of `0` is all zeros. -/
lemma cfDigit_zero_eq_zero (n : ℕ) : cfDigit 0 n = 0 := by
  have h : gaussMap^[n] (0 : ℝ) = 0 := Function.iterate_fixed (by simp [gaussMap]) n
  simp [cfDigit, h]

/-- A genuine word never occurs in an all-zeros list: a prefix of a tail is a subset of the
list, so one of its `≥ 1` entries would have to be `0`. -/
lemma countOccurrences_eq_zero_of_forall_eq_zero {v l : List ℕ} (hne : v ≠ [])
    (hpos : ∀ e ∈ v, 1 ≤ e) (hl : ∀ b ∈ l, b = 0) : countOccurrences v l = 0 := by
  rw [countOccurrences, List.countP_eq_zero]
  intro t ht hpref
  have hvt : v <+: t := List.isPrefixOf_iff_prefix.mp (by simpa using hpref)
  have htl : t <:+ l := (List.mem_tails _ _).mp ht
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil v hne
  have hel : e ∈ l := htl.subset (hvt.subset he)
  have := hpos e he
  rw [hl e hel] at this
  omega

/-- **Degenerate-case verdict** (guard rule): the constant map `x ↦ 1/1` — the singular
`a = c = 0` configuration — satisfies `MobiusUniformFreq` (its image is `0`, whose junk expansion
is all zeros, so every genuine frequency is `0`), while `MobiusCFN 0 1 0 1` is FALSE
(`not_mobiusCFN_const`).  So the *nonsingularity* hypothesis of `mobiusCFN_of_uniformFreq` is
load-bearing and cannot be dropped. -/
theorem mobiusUniformFreq_const : MobiusUniformFreq 0 1 0 1 := by
  intro v hne hpos
  refine ⟨0, fun x _ _ => ?_⟩
  have h1 : (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) / (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) = 1 := by
    push_cast; norm_num
  rw [h1, Int.fract_one]
  have hzero : ∀ n : ℕ,
      (countOccurrences v ((List.range n).map (cfDigit 0)) : ℝ) / n = 0 := by
    intro n
    have : countOccurrences v ((List.range n).map (cfDigit 0)) = 0 := by
      refine countOccurrences_eq_zero_of_forall_eq_zero hne hpos ?_
      intro b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact cfDigit_zero_eq_zero i
    simp [this]
  simp [hzero]

/-- **The single open leaf, in uniform-frequency form**: the scaling maps `x ↦ p·x` for prime
`p`.  Everything else in Vandehey 2017 Theorem 1.1 is discharged (`VandeheySerret` for the
`GL₂(ℤ)` factors, `VandeheySmith` for the Smith descent). -/
def ScaleUniformFreq : Prop :=
  ∀ p : ℕ, p.Prime → MobiusUniformFreq (p : ℤ) 0 0 1

theorem mobiusCFNScale_of_scaleUniformFreq (h : ScaleUniformFreq) : MobiusCFNScale := by
  intro p hp
  refine mobiusCFN_of_uniformFreq (p : ℤ) 0 0 1 ?_ (h p hp)
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  simpa using hp0

/-- **Vandehey 2017 Theorem 1.1 rests on one statement about one map.**  `ScaleUniformFreq` —
`x ↦ p·x` has `x`-independent output window frequencies for prime `p` — gives the crux. -/
theorem vandeheyUniformFreq_of_scaleUniformFreq (h : ScaleUniformFreq) : VandeheyUniformFreq :=
  vandeheyUniformFreq_of_scale (mobiusCFNScale_of_scaleUniformFreq h)

end NormalNumbers.Literature

section
open NormalNumbers.Literature
#print axioms mobiusCFN_of_uniformFreq
#print axioms mobiusUniformFreq_one
#print axioms mobiusUniformFreq_const
#print axioms mobiusCFNScale_of_scaleUniformFreq
#print axioms vandeheyUniformFreq_of_scaleUniformFreq
end
