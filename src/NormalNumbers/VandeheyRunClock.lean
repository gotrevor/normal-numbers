/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyAssembly

/-!
# The capstone on the RUN clock

`VandeheyAssembly.mobiusUniformFreq_of_transducer` reads the image's CF digits off the
transducer's output *stream* (`hout`) and rescales by the transducer's output *length*
(`hlen`).  For the concrete Raney machine that shape is unavailable, for a structural reason
recorded at lap 6 (`VandeheyRunBirkhoff`): the machine emits `L/R` **letters**, the image's CF
digits are the **runs** of the letter stream, and the letter count per input digit has infinite
mean (the Gauss digit mean diverges), so no `hlen` exists for the letter clock.  A run's *value*
is not a function of a finite state, so a digit-emitting finite-state transducer does not exist
either (`VandeheyLRTransducer`, module docstring).

This file is the restatement that dissolves the mismatch.  The observation is that the assembly
never needs the output stream to be *produced* by the automaton: the statement
`MobiusUniformFreq` speaks about `cfDigit` of the image directly.  What it needs is only

* a **clock** `ℓ x n` — the number of image CF digits accounted for by the first `n` input
  digits — which is monotone and grows linearly at an `x`-independent rate `r > 0`, and
* an `x`-independent Cesàro limit for the occurrence count *sampled along that clock*.

Both are then supplied by the concrete machine: `ℓ` is the run count
(`VandeheyTransportB.tendsto_numAlt_lrWord_div` gives the rate, `VandeheyFirstLetter`'s
`zero_lt_runRate` its positivity), and the sampled count comes from the letter-level trigger
engine through the run dictionary (`VandeheyLRPattern.card_cf_eq_card_patWord`).

So `hcof` and `hout` — two of the six named hypotheses of the old capstone, and the two that are
*false* for the letter machine (the letter stream is not the image's CF digit stream) — do not
appear here at all.  The content is `Rescale.tendsto_div_of_tendsto_comp_of_monotone` and
nothing else.
-/

namespace NormalNumbers.VandeheyOut

open Filter Literature

/-- The number of occurrences of `v` among the first `p` CF digits of `z`, as a real. -/
noncomputable def cfCount (v : List ℕ) (z : ℝ) (p : ℕ) : ℝ :=
  (countOccurrences v ((List.range p).map (cfDigit z)) : ℝ)

lemma cfCount_mono (v : List ℕ) (z : ℝ) : Monotone (cfCount v z) := by
  intro p p' h
  have : countOccurrences v ((List.range p).map (cfDigit z))
      ≤ countOccurrences v ((List.range p').map (cfDigit z)) :=
    countOccurrences_le_of_prefix ((range_prefix h).map _)
  simpa only [cfCount] using (Nat.cast_le.mpr this : ((_ : ℕ) : ℝ) ≤ _)

/-- **The capstone, on the run clock.**  A monotone `x`-indexed clock growing at a common rate
`r > 0`, together with an `x`-independent Cesàro limit for the image's occurrence count sampled
along that clock, gives the per-matrix uniform-frequency statement.  No transducer, no output
stream, and no value of the limit. -/
theorem mobiusUniformFreq_of_runClock {a b c d : ℤ} {r : ℝ} (hr : 0 < r)
    (ℓ : ℝ → ℕ → ℕ) (hmono : ∀ x : ℝ, Monotone (ℓ x))
    (hrate : ∀ x : ℝ, (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
      Tendsto (fun n => (ℓ x n : ℝ) / n) atTop (nhds r))
    (hcount : ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) → ∃ L : ℝ, ∀ x : ℝ,
      (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
      Tendsto (fun n =>
          cfCount v (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))) (ℓ x n) / n)
        atTop (nhds L)) :
    MobiusUniformFreq a b c d := by
  intro v hne hpos
  obtain ⟨L, hL⟩ := hcount v hne hpos
  refine ⟨L / r, fun x hden hx => ?_⟩
  exact Rescale.tendsto_div_of_tendsto_comp_of_monotone
    (cfCount_mono v (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))))
    (hmono x) hr (hrate x hden hx) (hL x hden hx)

/-- **Content locator** (guard rule) for the run-clock hypothesis bundle: the identity clock
`ℓ x n = n` with rate `1` reduces the bundle to the plain CF-normality of the image, so the
bundle is consistent and all of its content is in the clock's rate. -/
theorem mobiusUniformFreq_of_runClock_locator {a b c d : ℤ}
    (himg : ∀ x : ℝ, (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
      IsCFNormal (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d)))) :
    MobiusUniformFreq a b c d := by
  refine mobiusUniformFreq_of_runClock (r := 1) one_pos (fun _ n => n)
    (fun _ => monotone_id) (fun x _ _ => ?_) (fun v hne hpos => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  · exact ⟨(gaussMeasure (cfCylinder v)).toReal, fun x hden hx =>
      himg x hden hx v hne hpos⟩

end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms cfCount_mono
#print axioms mobiusUniformFreq_of_runClock
#print axioms mobiusUniformFreq_of_runClock_locator
end
