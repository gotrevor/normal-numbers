/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Bad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# S7-BS: how big the bad set really is — the exponent is `1/2`, not `1`

`conjHeight_ge_of_bad` (lap 60) prices one bad coincidence.  The counting problem it opens asks how
often the state's image endpoint lands in the **bad set**

    B(δ) = { x ∈ (0,1) : |x − 1/k| < δ for some k ≥ 1 },

the `δ`-neighbourhood of the Gauss cylinder endpoints, which is exactly the set of positions where
directive fact 2's distortion failure occurs.

The natural guess is `|B(δ)| ≍ δ`.  That guess is **wrong**, and the error is not a constant: the
endpoints `1/k` accumulate at `0`, so `B(δ)` contains a whole interval of length `≈ √δ` near the
origin and the disjoint part contributes `≈ 2δ·δ^{−1/2}` as well.  The truth is `|B(δ)| ≍ √δ`.

* `volume_badSet_le` — `|B(δ)| ≤ 6√δ` for `0 < δ ≤ 1`, with the split at `K = ⌈δ^{−1/2}⌉`:
  the `k > K` tail is swallowed by `(0, 1/K + δ)`, and the `K` remaining intervals contribute
  `2δK`.

## Why this matters to the route

Any bad-state budget must be stated in `√δ`, not `δ`.  That is still enough for the crux — the
ε-scheme only needs the bad frequency to tend to `0` with the scale — but a lap that writes `C·δ`
will be off by an unbounded factor and will look, spuriously, like a contradiction.  Recording the
correct exponent here is what stops lap 61's counting attack from being mis-calibrated from the
first line.

## Guard rule

Content locator: the `1/K` term is the accumulation of `1/k` at the origin and is what forces the
`√`; drop it and the bound would be `2δK`, minimised at `K = 1` — i.e. the estimate genuinely
trades the two terms off.  Degenerate case: `δ = 1` gives `|B| ≤ 6`, free, as it must be.
-/

namespace NormalNumbers.VandeheyS7

open MeasureTheory

/-- The bad set: the `δ`-neighbourhood, inside `(0,1)`, of the Gauss cylinder endpoints `1/k`. -/
def badSet (δ : ℝ) : Set ℝ :=
  {x | x ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ k : ℕ, 1 ≤ k ∧ |x - 1 / (k : ℝ)| < δ}

/-- **The bad set has measure `≍ √δ`, not `δ`.** -/
theorem volume_badSet_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    volume (badSet δ) ≤ ENNReal.ofReal (6 * Real.sqrt δ) := by
  classical
  set s := Real.sqrt δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ
  have hss : s * s = δ := Real.mul_self_sqrt hδ.le
  have hs1 : s ≤ 1 := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hδ1
  have hδs : δ ≤ s := by nlinarith
  set K : ℕ := ⌈1 / s⌉₊ with hKdef
  have hKpos : 0 < K := by
    rw [hKdef, Nat.ceil_pos]
    positivity
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hKlow : 1 / s ≤ (K : ℝ) := Nat.le_ceil _
  have hKhigh : (K : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one (by positivity)
  -- the covering
  have hsub : badSet δ ⊆ Set.Ioo (0 : ℝ) (1 / (K : ℝ) + δ) ∪
      ⋃ k ∈ Finset.Icc 1 K, Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ) := by
    rintro x ⟨⟨hx0, -⟩, k, hk1, habs⟩
    rcases le_or_gt k K with hk | hk
    · right
      simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop]
      exact ⟨k, ⟨hk1, hk⟩, by
        have := abs_lt.1 habs
        exact ⟨by linarith [this.1], by linarith [this.2]⟩⟩
    · left
      refine ⟨hx0, ?_⟩
      have hkR : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.le
      have hk0 : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := lt_of_lt_of_le hKpos hk.le
        exact_mod_cast this
      have h1 : 1 / (k : ℝ) ≤ 1 / (K : ℝ) := by
        exact one_div_le_one_div_of_le hKR hkR
      have := (abs_lt.1 habs).2
      linarith
  -- measure of the cover
  have hcov := measure_mono (μ := (volume : Measure ℝ)) hsub
  have hunion : volume (Set.Ioo (0 : ℝ) (1 / (K : ℝ) + δ) ∪
      ⋃ k ∈ Finset.Icc 1 K, Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ))
      ≤ volume (Set.Ioo (0 : ℝ) (1 / (K : ℝ) + δ))
        + ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ)) := by
    refine le_trans (measure_union_le _ _) (by
      gcongr
      exact measure_biUnion_finset_le _ _)
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      volume (Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ)) ≤ ENNReal.ofReal (2 * δ) := by
    intro k _
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hsum : ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ))
      ≤ ENNReal.ofReal (2 * δ * (K : ℝ)) := by
    calc ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ))
        ≤ ∑ _k ∈ Finset.Icc 1 K, ENNReal.ofReal (2 * δ) := Finset.sum_le_sum hterm
      _ = (K : ENNReal) * ENNReal.ofReal (2 * δ) := by
          rw [Finset.sum_const, Nat.card_Icc]
          simp [nsmul_eq_mul]
      _ = ENNReal.ofReal ((K : ℝ) * (2 * δ)) := by
          conv_rhs => rw [ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (2 * δ * (K : ℝ)) := by rw [mul_comm]
  have hfirst : volume (Set.Ioo (0 : ℝ) (1 / (K : ℝ) + δ))
      = ENNReal.ofReal (1 / (K : ℝ) + δ) := by
    rw [Real.volume_Ioo]; ring_nf
  -- the real inequality
  have hreal : 1 / (K : ℝ) + δ + 2 * δ * (K : ℝ) ≤ 6 * s := by
    have h1 : 1 / (K : ℝ) ≤ s := by
      rw [div_le_iff₀ hKR]
      have : 1 / s ≤ (K : ℝ) := hKlow
      rw [div_le_iff₀ hs0] at this
      linarith
    have h2 : 2 * δ * (K : ℝ) ≤ 2 * s + 2 * δ := by
      have hKb : (K : ℝ) ≤ 1 / s + 1 := hKhigh.le
      have : 2 * δ * (K : ℝ) ≤ 2 * δ * (1 / s + 1) := by nlinarith
      have hds : δ * (1 / s) = s := by
        field_simp
        nlinarith
      nlinarith [this, hds]
    linarith
  calc volume (badSet δ) ≤ _ := hcov
    _ ≤ volume (Set.Ioo (0 : ℝ) (1 / (K : ℝ) + δ))
        + ∑ k ∈ Finset.Icc 1 K, volume (Set.Ioo (1 / (k : ℝ) - δ) (1 / (k : ℝ) + δ)) := hunion
    _ ≤ ENNReal.ofReal (1 / (K : ℝ) + δ) + ENNReal.ofReal (2 * δ * (K : ℝ)) := by
        rw [hfirst]; gcongr
    _ = ENNReal.ofReal (1 / (K : ℝ) + δ + 2 * δ * (K : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (6 * Real.sqrt δ) := ENNReal.ofReal_le_ofReal hreal

#print axioms volume_badSet_le

end NormalNumbers.VandeheyS7
