/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Wall
import NormalNumbers.VandeheyRunClock

/-!
# Factoring the Theorem 1.1 pipeline for `ℤ[φ]` (DIRECTION items 3–4)

`VandeheyS7.affineCFN_of_uniformFreq` reduced §7 Problem 1 to `AffineUniformFreq q r₀`:
frequency existence, no value.  `VandeheyS7Wall` showed the Theorem 1.1 machinery cannot supply
that over `ℤ[φ]`, because its finite state set is a certificate about **ℤ** and the certificate
has no analogue.  This file does the *reuse-before-rebuild* step: it isolates the part of the
proved pipeline that never used finiteness, and names, as hypotheses, exactly the two things
finiteness was used to produce.

## What survives the move off ℤ

`VandeheyOut.mobiusUniformFreq_of_runClock` is the restatement that made Theorem 1.1 assemble.
Its proof is **one rescaling** (`Rescale.tendsto_div_of_tendsto_comp_of_monotone`) and nothing
else — no transducer, no output stream, no determinant, no state set.  So it ports verbatim to a
real affine map.  That is `affineUniformFreq_of_runClock` below, and with
`affineCFN_of_uniformFreq` it gives the **whole reduction** of §7 Problem 1:

    0 < q → RunClock ℓ rate → SampledUniformCount q r₀ ℓ → AffineCFN q r₀ .

## The two named hypotheses

* `RunClock ℓ rate` — a monotone clock `ℓ x n` (how many image CF digits the first `n`
  input digits account for) growing at a **common, positive, `x`-independent** rate.  In the
  integer proof this came from the run-count Birkhoff average of the Raney machine, whose
  positivity used the finite state set.  Over `ℤ[φ]` it is Route A's Lemma 6.1 analogue: the
  attack map's 2026-08-24 measurement found `l(n) = c₁ n (1+o(1))` **survives** the loss of
  Lemma 2.2, because `∫ log(1+a) dγ < ∞` (the finiteness behind Khinchin's constant) even though
  the burst bound `burst ≤ C + log(1+a)/Lévy` is unbounded.  Measured `c₁ ∈ [0.965, 0.989]`.
* `SampledUniformCount q r₀ ℓ` — the occurrence count of each word in the image, **sampled along
  that clock**, has an `x`-independent Cesàro limit.  This is where all the remaining content
  is: it is what the trigger-window / distributional-merging nodes of Route A must deliver, and
  it is the only place the lost finiteness has to be replaced.

Splitting them matters because they fail differently: the clock is believed fine (measured, and
with a known finite-mean reason), while the count is the genuine crux.

## Guard rule

Content locator: `affineUniformFreq_of_runClock_locator` — the identity clock at rate `1` reduces
the bundle to plain CF-normality of the image, so the bundle is consistent and all the content is
in the clock rate and the sampled count.  Degenerate case: `not_affineCFN_zero` (previous module)
already shows the conclusion is false for `q = 0`, so no hypothesis bundle here can be vacuous.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers NormalNumbers.VandeheyOut

/-- **Named hypothesis 1: the clock.**  `ℓ x n` is monotone in `n` and grows at the positive,
`x`-independent rate `rate` along every CF-normal input.  The map `q·x + r₀` it is a clock FOR
enters only through `SampledUniformCount`; formally the clock hypothesis is map-free, which is
itself worth knowing — it is the half of the bundle that is not about the image at all. -/
def RunClock (ℓ : ℝ → ℕ → ℕ) (rate : ℝ) : Prop :=
  (∀ x : ℝ, Monotone (ℓ x)) ∧ 0 < rate ∧
    ∀ x : ℝ, IsCFNormal (Int.fract x) →
      Tendsto (fun n => (ℓ x n : ℝ) / n) atTop (nhds rate)

/-- **Named hypothesis 2: the sampled count.**  Every genuine word's occurrence count in the
image, sampled along the clock, has an `x`-independent Cesàro limit.  No value is asserted.
This is the crux; `q` appears only through the image. -/
def SampledUniformCount (q r₀ : ℝ) (ℓ : ℝ → ℕ → ℕ) : Prop :=
  ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) → ∃ L : ℝ, ∀ x : ℝ,
    IsCFNormal (Int.fract x) →
      Tendsto (fun n => cfCount v (Int.fract (q * x + r₀)) (ℓ x n) / n) atTop (nhds L)

/-- **The run-clock capstone, off ℤ.**  Verbatim `VandeheyOut.mobiusUniformFreq_of_runClock`
with a real affine map in place of the integer Möbius map: the proof is a single rescaling and
never touched the arithmetic. -/
theorem affineUniformFreq_of_runClock {q r₀ rate : ℝ} {ℓ : ℝ → ℕ → ℕ}
    (hclock : RunClock ℓ rate) (hcount : SampledUniformCount q r₀ ℓ) :
    AffineUniformFreq q r₀ := by
  obtain ⟨hmono, hrate0, hrate⟩ := hclock
  intro v hne hpos
  obtain ⟨L, hL⟩ := hcount v hne hpos
  refine ⟨L / rate, fun x hx => ?_⟩
  exact Rescale.tendsto_div_of_tendsto_comp_of_monotone
    (cfCount_mono v (Int.fract (q * x + r₀))) (hmono x) hrate0 (hrate x hx) (hL x hx)

/-- **The full reduction of Vandehey §7 Problem 1 to two analytic obligations.**  For any real
`q > 0` and any real `r₀`: a positive-rate clock plus an `x`-independent sampled count gives the
frozen target.  Nothing integral, nothing quadratic, no limit value. -/
theorem affineCFN_of_runClock {q r₀ rate : ℝ} {ℓ : ℝ → ℕ → ℕ} (hq : 0 < q)
    (hclock : RunClock ℓ rate) (hcount : SampledUniformCount q r₀ ℓ) :
    AffineCFN q r₀ :=
  affineCFN_of_uniformFreq hq r₀ (affineUniformFreq_of_runClock hclock hcount)

/-- `x ↦ φ·x`: the open problem, reduced to a clock and a sampled count. -/
theorem vandeheyS7_mul_phi_of_runClock {rate : ℝ} {ℓ : ℝ → ℕ → ℕ}
    (hclock : RunClock ℓ rate)
    (hcount : SampledUniformCount Real.goldenRatio 0 ℓ) : vandeheyS7_mul_phi :=
  affineCFN_of_runClock (lt_trans one_pos Real.one_lt_goldenRatio) hclock hcount

/-- `x ↦ x + φ`: likewise. -/
theorem vandeheyS7_add_phi_of_runClock {rate : ℝ} {ℓ : ℝ → ℕ → ℕ}
    (hclock : RunClock ℓ rate)
    (hcount : SampledUniformCount 1 Real.goldenRatio ℓ) : vandeheyS7_add_phi :=
  affineCFN_of_runClock one_pos hclock hcount

/-! ## Content locator (guard rule) -/

/-- The identity clock `ℓ x n = n` at rate `1` reduces the bundle to plain CF-normality of the
image.  So the hypothesis bundle is consistent, and all of its content sits in the clock's rate
and in the sampled count. -/
theorem affineUniformFreq_of_runClock_locator {q r₀ : ℝ}
    (himg : ∀ x : ℝ, IsCFNormal (Int.fract x) → IsCFNormal (Int.fract (q * x + r₀))) :
    AffineUniformFreq q r₀ := by
  refine affineUniformFreq_of_runClock (rate := 1) (ℓ := fun _ n => n)
    ⟨fun _ => monotone_id, one_pos, fun x _ => ?_⟩ (fun v hne hpos => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  · exact ⟨(gaussMeasure (cfCylinder v)).toReal, fun x hx => himg x hx v hne hpos⟩

section Audit

#print axioms affineUniformFreq_of_runClock
#print axioms affineCFN_of_runClock
#print axioms vandeheyS7_mul_phi_of_runClock
#print axioms affineUniformFreq_of_runClock_locator

end Audit

end NormalNumbers.VandeheyS7
