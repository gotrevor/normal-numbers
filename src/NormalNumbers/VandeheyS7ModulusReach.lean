/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-MR: how far a MODULUS reaches — it must be set-level, not cylinder-level

S7-MD showed the §7 route pays a modulus, `freq(w) ≤ ω(γ(I_w))`, not a constant multiple of
`γ(I_w)`, and recorded that "a modulus is all that absolute continuity of a limit point needs".
That is true only if the modulus holds for **arbitrary measurable targets**.  This module proves,
in the kernel, that a modulus on CYLINDERS alone is not enough, and therefore pins the shape the
next restatement of `OrbitACBound` must take.

## The obstruction

A modulus is concave-ish, hence **not subadditive**: splitting a set of mass `t` into `N` pieces
of mass `t/N` turns the bound `ω(t)` into `N·ω(t/N)`, which for `ω = √·` is `√(N t) → ∞`
(`sqrt_modulus_sum_unbounded`).  So the standard covering proof of absolute continuity —
cover a `γ`-null set by countably many cylinders of small total mass and sum the bounds — does
**not** run.  The sum of the bounds is unbounded no matter how small the total mass is.

Concretely this is not a proof artefact.  The Bernoulli measure on continued fractions with digits
restricted to `{1, 2}` is singular with respect to `γ` yet satisfies `ν(I_w) ≤ γ(I_w)^α` on every
cylinder for a suitable `α ∈ (0,1)`: both sides decay geometrically and the ratio of the rates is
exactly such an `α`.  So cylinder-level moduli genuinely fail to detect singularity, and the
counterexample lives in the very digit system at hand.

## What this fixes about the route

`OrbitACBound` must be stated as

    limsup_k  #{ i < k : Gⁱy ∈ E } / k   ≤   ω (γ E)     for every measurable `E ⊆ (0,1)`,

not merely for `E = I_w`.  The good news is that S7-MD's derivation already has this shape: its
two inputs — the pullback bound `γ(s⁻¹E) ≤ (2K/η)·γ(E)` (S7-PB) and `ClassFreqBound` — are both
statements about a set, and only the packaging specialised them to cylinders.  So the fix is a
restatement, not new mathematics; but it must be made before the AC step is attempted, or the
proof will not close.

## Guard rule

Content locator: at `N = 1` the statement is `C ≤ √t`, which is false for large `C` — so all the
content is in letting `N` grow, i.e. in the splitting.  Degenerate case: `t = 0` makes every term
zero and the claim false, which is why `0 < t` is required; a modulus says nothing about null sets
directly, and that is precisely the gap.
-/
import Mathlib.Analysis.Real.Sqrt

namespace NormalNumbers.VandeheyS7

/-- **A modulus is not subadditive.**  Splitting mass `t` into `N` equal pieces makes the summed
bound `N·√(t/N) = √(N·t)`, which exceeds any prescribed `C`.  So covering arguments cannot pass a
cylinder-level modulus to a general measurable set. -/
theorem sqrt_modulus_sum_unbounded {t : ℝ} (ht : 0 < t) (C : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ C ≤ (N : ℝ) * Real.sqrt (t / (N : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (C ^ 2 / t))
  have hN1 : (1:ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : (0:ℝ) < (N : ℝ) := by linarith
  have hNnat : 1 ≤ N := by exact_mod_cast hN1.le
  refine ⟨N, hNnat, ?_⟩
  have hid : (N : ℝ) * Real.sqrt (t / (N : ℝ)) = Real.sqrt ((N : ℝ) * t) := by
    have h1 : (N : ℝ) * Real.sqrt (t / (N : ℝ))
        = Real.sqrt ((N : ℝ) ^ 2) * Real.sqrt (t / (N : ℝ)) := by
      rw [Real.sqrt_sq hNpos.le]
    rw [h1, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp

  rw [hid]
  have hCt : C ^ 2 / t < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hCt' : C ^ 2 ≤ (N : ℝ) * t := by
    rw [div_lt_iff₀ ht] at hCt; linarith
  calc C ≤ |C| := le_abs_self C
    _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
    _ ≤ Real.sqrt ((N : ℝ) * t) := Real.sqrt_le_sqrt hCt'

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.sqrt_modulus_sum_unbounded

end Audit
