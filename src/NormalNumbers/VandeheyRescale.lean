/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rescaling a Cesàro limit along a linearly growing index map

Vandehey's §6 counts occurrences of an output word in the output produced by the first `n` INPUT
digits, and separately shows the output LENGTH satisfies `ℓ(n) = c₁·n·(1+o(1))` (his Lemma 6.1).
But CF-normality of the image is a statement about the first `m` OUTPUT digits, for **every** `m`
— not only for the `m` that are values of `ℓ`.  This file is the glue: a monotone counting
function whose values along `ℓ` have Cesàro limit `L` has, over all indices, Cesàro limit
`L / c₁`.

The content is the two-sided squeeze at a general index `m`: with `N m` the least input index
whose output already reaches `m`, monotonicity gives `C (ℓ (N m - 1)) ≤ C m ≤ C (ℓ (N m))`, while
`ℓ (N m - 1) < m ≤ ℓ (N m)` together with linear growth gives `m / N m → c`.  Nothing here knows
about continued fractions, so it applies verbatim to the §5 occurrence count and to any other
monotone output statistic.

Main result: `tendsto_div_of_tendsto_comp_of_monotone`.
-/

namespace NormalNumbers.Rescale

open Filter

variable {C : ℕ → ℝ} {ℓ : ℕ → ℕ} {c L : ℝ}

/-- A linearly growing index map is cofinal: every output position is eventually reached. -/
lemma tendsto_atTop_of_tendsto_div (hc : 0 < c)
    (hlc : Tendsto (fun n => (ℓ n : ℝ) / n) atTop (nhds c)) :
    Tendsto ℓ atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  have hbase : Tendsto (fun n : ℕ => (c / 2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [hlc.eventually_const_lt (show c / 2 < c by linarith),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [lt_div_iff₀ hn0] at hn
  linarith

/-- `(n-1)/n → 1`: the shift is asymptotically invisible. -/
lemma tendsto_pred_div_self : Tendsto (fun n : ℕ => (((n - 1 : ℕ) : ℝ)) / n) atTop (nhds 1) := by
  have h : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  field_simp

/-- Shifting the index inside a Cesàro limit does not change it. -/
lemma tendsto_shift_of_tendsto {f : ℕ → ℝ} (hf : Tendsto (fun n => f n / n) atTop (nhds L)) :
    Tendsto (fun n : ℕ => f (n - 1) / n) atTop (nhds L) := by
  have h1 : Tendsto (fun n : ℕ => f (n - 1) / ((n - 1 : ℕ) : ℝ)) atTop (nhds L) :=
    hf.comp (tendsto_sub_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => (f (n - 1) / ((n - 1 : ℕ) : ℝ)) * (((n - 1 : ℕ) : ℝ) / n))
      atTop (nhds (L * 1)) := h1.mul tendsto_pred_div_self
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ n - 1 := by omega
    have : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  field_simp

/-- **The rescaling lemma.**  If a monotone counting function `C`, sampled along a linearly
growing index map `ℓ` with `ℓ n / n → c > 0`, has Cesàro limit `C (ℓ n) / n → L`, then over ALL
indices `C m / m → L / c`.

This is the step that turns Vandehey's §6 count (indexed by input digits) into a statement about
the output digits, which is what CF-normality of the image asks for. -/
theorem tendsto_div_of_tendsto_comp_of_monotone
    (hC : Monotone C) (hℓ : Monotone ℓ) (hc : 0 < c)
    (hlc : Tendsto (fun n => (ℓ n : ℝ) / n) atTop (nhds c))
    (hCL : Tendsto (fun n => C (ℓ n) / n) atTop (nhds L)) :
    Tendsto (fun m => C m / m) atTop (nhds (L / c)) := by
  classical
  have hℓtop : Tendsto ℓ atTop atTop := tendsto_atTop_of_tendsto_div hc hlc
  have hex : ∀ m : ℕ, ∃ n, m ≤ ℓ n := fun m => (hℓtop.eventually_ge_atTop m).exists
  set N : ℕ → ℕ := fun m => Nat.find (hex m) with hNdef
  have hNspec : ∀ m, m ≤ ℓ (N m) := fun m => Nat.find_spec (hex m)
  have hNmin : ∀ m k, k < N m → ℓ k < m := by
    intro m k hk
    have := Nat.find_min (hex m) hk
    omega
  -- `N` is cofinal
  have hNtop : Tendsto N atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨ℓ b + 1, fun a ha => ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : ℓ (N a) ≤ ℓ b := hℓ hcon.le
    have h2 : a ≤ ℓ (N a) := hNspec a
    omega
  -- the two sampled sequences, and their shifts, all have the stated limits
  have hg : Tendsto (fun n => C (ℓ n) / n) atTop (nhds L) := hCL
  have hG : Tendsto (fun n : ℕ => C (ℓ (n - 1)) / n) atTop (nhds L) :=
    tendsto_shift_of_tendsto (f := fun n => C (ℓ n)) hCL
  have hU : Tendsto (fun n : ℕ => (ℓ n : ℝ) / n) atTop (nhds c) := hlc
  have hLo : Tendsto (fun n : ℕ => ((ℓ (n - 1) : ℕ) : ℝ) / n) atTop (nhds c) :=
    tendsto_shift_of_tendsto (L := c) (f := fun n => ((ℓ n : ℕ) : ℝ)) hlc
  -- the numerator squeeze
  have hnum : Tendsto (fun m : ℕ => C m / (N m : ℝ)) atTop (nhds L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hG.comp hNtop) (hg.comp hNtop) ?_ ?_
    · filter_upwards [hNtop.eventually_ge_atTop 1] with m hm
      have hpos : (0 : ℝ) < N m := by exact_mod_cast hm
      have hlt : ℓ (N m - 1) < m := hNmin m (N m - 1) (by omega)
      exact div_le_div_of_nonneg_right (hC hlt.le) hpos.le
    · filter_upwards [hNtop.eventually_ge_atTop 1] with m hm
      have hpos : (0 : ℝ) < N m := by exact_mod_cast hm
      exact div_le_div_of_nonneg_right (hC (hNspec m)) hpos.le
  -- the denominator squeeze
  have hden : Tendsto (fun m : ℕ => (m : ℝ) / (N m : ℝ)) atTop (nhds c) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hLo.comp hNtop) (hU.comp hNtop) ?_ ?_
    · filter_upwards [hNtop.eventually_ge_atTop 1] with m hm
      have hpos : (0 : ℝ) < N m := by exact_mod_cast hm
      refine div_le_div_of_nonneg_right ?_ hpos.le
      have : ℓ (N m - 1) < m := hNmin m (N m - 1) (by omega)
      exact_mod_cast this.le
    · filter_upwards [hNtop.eventually_ge_atTop 1] with m hm
      have hpos : (0 : ℝ) < N m := by exact_mod_cast hm
      refine div_le_div_of_nonneg_right ?_ hpos.le
      exact_mod_cast hNspec m
  -- invert and multiply
  have hinv : Tendsto (fun m : ℕ => (N m : ℝ) / (m : ℝ)) atTop (nhds c⁻¹) := by
    have h1 := hden.inv₀ hc.ne'
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1, hNtop.eventually_ge_atTop 1] with m hm hmN
    have h2 : (0 : ℝ) < m := by exact_mod_cast hm
    have h3 : (0 : ℝ) < N m := by exact_mod_cast hmN
    rw [inv_div]
  have hfinal : Tendsto (fun m : ℕ => (C m / (N m : ℝ)) * ((N m : ℝ) / (m : ℝ))) atTop
      (nhds (L * c⁻¹)) := hnum.mul hinv
  rw [div_eq_mul_inv]
  refine hfinal.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hNtop.eventually_ge_atTop 1] with m hm hmN
  have h2 : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : (0 : ℝ) < N m := by exact_mod_cast hmN
  field_simp

end NormalNumbers.Rescale

section
open NormalNumbers.Rescale
#print axioms tendsto_div_of_tendsto_comp_of_monotone
end
