/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.Pillai
import NormalNumbers.Headline

/-!
# Uniform high-base equidistribution

A **single-limit** sufficient criterion for absolute normality, as an
alternative interface to `pillai`.

`pillai` asks for simple normality at *every* power `b ^ r`: a family of
limits indexed by `r`, each taken as the depth `N → ∞`.  This file asks
instead for one uniform statement as the *base* runs to infinity, measured
in total variation.

## Why total variation

The naive reading "each digit value has frequency `1 / b`" degenerates as
`b → ∞`, because the target `1 / b` vanishes: a sup-norm bound
`max_c |freq c - 1/b| → 0` says only that no digit value takes a positive
share of the window, which plenty of non-normal reals satisfy.  Summing the
deviations over all `b` cells cancels the vanishing target, so `digitTV` is
the notion with content here.  See `digitTV_diag_eq` for the sharp form of
the degeneracy at the diagonal depth `N = b`.

## Route

The engine is `Pillai.lean`, reused rather than rebuilt.  A base-`b ^ r`
digit is an aligned length-`r` block of base-`b` digits
(`digitOf_pow_eq_blockNatVal`), block occurrences at a fixed phase are
counted by `card_matchingValues`, and boundary-straddling occurrences are
already bounded by `card_straddling_phases`.  The only new ingredient is
`abs_expectation_sub_le_two_mul_digitTV`: total variation controls the
expectation of any `[0,1]`-valued statistic of a digit, which converts a
histogram bound into a block-frequency bound in one step, with no induction
on `r`.

Contrast with `phaseWindowFreq_tendsto`, which obtains the same conclusion
from a limit at fixed `r`.  Here `r` is large and the bound is uniform in
it, and that is the whole trade.

## Guardrails

Two statements in this file are refutations rather than tools, recorded so
that a proof search does not spend laps on them:

* `digitTV_diag_eq` shows the depth-`N = b` reading is a rigidity (the digit
  multiset must be a near-permutation), not a weakened randomness.  A random
  real fails it.
* `exists_schedule_digitTV_tendsto_not_isNormal` shows that asking for *some*
  depth schedule, rather than every one, is dodgeable: one depth per base is
  exactly what an oscillating real can satisfy.
-/

namespace NormalNumbers

open Filter

/-- Occurrences of the digit value `c` among the first `N` base-`b` digits
of `x`. -/
noncomputable def digitOccCount (b : ℕ) (x : ℝ) (N c : ℕ) : ℕ :=
  ((Finset.range N).filter fun i => digitOf b x i = c).card

/-- Total-variation distance from the base-`b` digit histogram of the first
`N` digits of `x` to the uniform distribution on `{0, …, b - 1}`. -/
noncomputable def digitTV (b : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  (∑ c ∈ Finset.range b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|) / 2

/-- **Guardrail.**  At the diagonal depth `N = b` the criterion is a
rigidity, not a randomness: `digitTV b x b` is small exactly when the first
`b` base-`b` digits are a permutation of `{0, …, b - 1}` up to `o b`
defects.  A uniformly random real has about `b / e` unused values at this
depth, pinning `digitTV b x b ≥ 1 / (2 * e)`, so this is *stronger* than
normality and orthogonal to it. -/
theorem digitTV_diag_eq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    digitTV b x b
      = (∑ c ∈ Finset.range b, |(digitOccCount b x b c : ℝ) - 1|) / (2 * b) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := lt_of_lt_of_le (by norm_num) hb
    exact_mod_cast this
  have hterm : ∀ c : ℕ, |(digitOccCount b x b c : ℝ) / b - (b : ℝ)⁻¹|
      = |(digitOccCount b x b c : ℝ) - 1| / b := by
    intro c
    rw [inv_eq_one_div, div_sub_div_same, abs_div, abs_of_pos hb0]
  simp only [digitTV, hterm, ← Finset.sum_div]
  ring

/-- Total variation controls every `[0,1]`-valued statistic of a digit.
This is the one genuinely new lemma; everything else is `Pillai.lean`. -/
theorem abs_expectation_sub_le_two_mul_digitTV (b : ℕ) (x : ℝ) (N : ℕ)
    (f : ℕ → ℝ) (hf0 : ∀ c, 0 ≤ f c) (hf1 : ∀ c, f c ≤ 1) :
    |(∑ c ∈ Finset.range b, (digitOccCount b x N c : ℝ) / N * f c)
        - ∑ c ∈ Finset.range b, (b : ℝ)⁻¹ * f c|
      ≤ 2 * digitTV b x N := by
  have h2 : 2 * digitTV b x N
      = ∑ c ∈ Finset.range b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹| := by
    unfold digitTV; ring
  rw [h2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro c _
  have hrw : (digitOccCount b x N c : ℝ) / N * f c - (b : ℝ)⁻¹ * f c
      = ((digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹) * f c := by ring
  rw [hrw, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (abs_le.mpr ⟨by linarith [hf0 c], hf1 c⟩)

/-- The bridge home: at a fixed base, the total-variation form and the
digit-frequency form of simple normality agree.  Stated so that a search
landing on either shape can reach the other. -/
theorem simplyNormal_iff_digitTV_tendsto (b : ℕ) (x : ℝ) :
    (∀ c < b, Tendsto (fun N => (digitOccCount b x N c : ℝ) / N) atTop (nhds (b : ℝ)⁻¹))
      ↔ Tendsto (digitTV b x) atTop (nhds 0) := by
  constructor
  · intro h
    have hsum : Tendsto (fun N => ∑ c ∈ Finset.range b,
        |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|) atTop (nhds 0) := by
      have hz : (0 : ℝ) = ∑ _c ∈ Finset.range b, (0 : ℝ) := by simp
      rw [hz]
      refine tendsto_finset_sum _ (fun c hc => ?_)
      have h0 : Tendsto (fun N => (digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹)
          atTop (nhds 0) := by
        simpa using (h c (Finset.mem_range.mp hc)).sub_const ((b : ℝ)⁻¹)
      simpa using h0.abs
    unfold digitTV
    simpa using hsum.div_const 2
  · intro h c hc
    have hterm : ∀ N : ℕ, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|
        ≤ 2 * digitTV b x N := by
      intro N
      have h2 : 2 * digitTV b x N
          = ∑ c' ∈ Finset.range b, |(digitOccCount b x N c' : ℝ) / N - (b : ℝ)⁻¹| := by
        unfold digitTV; ring
      rw [h2]
      exact Finset.single_le_sum
        (f := fun c' => |(digitOccCount b x N c' : ℝ) / N - (b : ℝ)⁻¹|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hc)
    have hsq : Tendsto (fun N => |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|)
        atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hterm (by simpa using h.const_mul 2)
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hsq

/-- **Uniform high-base equidistribution.**  For every `ε` there is a
sampling ratio `L` and a base threshold `B` such that every base `b ≥ B`,
read to any depth `N ≥ L * b`, has its digit histogram within `ε` of
uniform.

The `L * b` floor is forced: at `N` samples in `b` cells the typical
total variation is of order `√(b / N)`, so depth must outgrow the base for
the condition to be satisfiable at all. -/
def UniformDigitTV (x : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ L B : ℕ, ∀ b ≥ B, ∀ N ≥ L * b, digitTV b x N < ε

/-- The engine.  Only the powers of `b` are consumed, so the hypothesis may
be weakened to that subfamily. -/
theorem isNormal_of_uniform_digitTV_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (h : ∀ ε > (0 : ℝ), ∃ L K : ℕ, ∀ r ≥ K, ∀ N ≥ L * b ^ r, digitTV (b ^ r) x N < ε) :
    IsNormal b x := by
  sorry

/-- **Headline.**  Uniform high-base equidistribution implies absolute
normality.  Strictly stronger than the conclusion: a normal real may have
arbitrarily bad rates as the base grows, so this is a sufficient criterion,
not a characterisation. -/
theorem isAbsolutelyNormal_of_uniformDigitTV (x : ℝ) (h : UniformDigitTV x) :
    IsAbsolutelyNormal x := by
  sorry

/-- **Guardrail.**  Asking only for *some* depth schedule is dodgeable.
Witness: binary digits independent and fair, forced to `0` on
`[P j, 2 * P j)` for a rapidly growing `P`.  Such a real fails simple
normality in base `2` at depth `2 * P j`, while the schedule can be routed
through the clean stretches `(2 * P (j-1), P j)`, which are multiplicatively
wide enough to host it. -/
theorem exists_schedule_digitTV_tendsto_not_isNormal :
    ∃ x : ℝ, ∃ N : ℕ → ℕ,
      Tendsto (fun b => (N b : ℝ) / b) atTop atTop ∧
      Tendsto (fun b => digitTV b x (N b)) atTop (nhds 0) ∧
      ¬ IsNormal 2 x := by
  sorry

end NormalNumbers
