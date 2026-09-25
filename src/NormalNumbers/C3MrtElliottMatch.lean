/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtLinearForms
import ErdosProblems.Erdos67b.LogElliott

/-!
# Matching the `D = 2` data against `Erdos67b.NonasymptoticLogElliott`

`C3MrtLinearForms.inner_sum_linear_forms` puts the two-shift `ζ^ω` correlation into the form

    ∑_j F((de)j + a) · z₀^{Ω(e j + b₀)} · z₁^{Ω(d j + b₁)},   b₀ = (a+1)/d, b₁ = (a+2)/e.

`Erdos67b.NonasymptoticLogElliott` takes exactly two affine forms `a₁ n + b₁`, `a₂ n + b₂` with

* `0 < a₁`, `0 < a₂`;
* **`a₁ b₂ − a₂ b₁ ≠ 0`** (non-degeneracy: the two forms are not proportional);
* `IsMultiplicativeOnPositiveInt gᵢ`, which unfolds to `g(mn) = g(m)g(n)` for **all** positive
  `m, n` — i.e. *complete* multiplicativity on the positive integers.

This file verifies both structural hypotheses for our data.

## The determinant is exactly `1`

With `a₁ = e`, `b₁ = (a+1)/d`, `a₂ = d`, `b₂ = (a+2)/e` (and `d ∣ a+1`, `e ∣ a+2`, which
`exists_joint_class` supplies):

    a₁ b₂ − a₂ b₁ = e·((a+2)/e) − d·((a+1)/d) = (a+2) − (a+1) = 1 .

So the non-degeneracy hypothesis holds **automatically, for every coprime powerful pair**, with
determinant `1` — no side conditions to discharge, no exceptional moduli.  (This is the same
`(n+2) − (n+1) = 1` that forced coprimality in `coprime_of_joint_progression`: the two facts are
the same unit determinant seen once in `ℕ` and once in `ℤ`.)

## Complete multiplicativity

`z^Ω` is completely multiplicative on positives because `Ω(mn) = Ω(m) + Ω(n)` unconditionally,
whereas `ω(mn) = ω(m) + ω(n)` needs coprimality.  That asymmetry is the entire reason for the
`ω → Ω` bridge of `C3MrtOmegaBridge`: the Elliott statement admits no merely-multiplicative
input.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- `z^{Ω}`, extended to `ℤ` by zero off the positives, as required by the Elliott statement. -/
noncomputable def zOmInt (z : ℂ) : ℤ → ℂ :=
  Erdos67b.positiveIntExtension (fun n : ℕ => z ^ ArithmeticFunction.cardFactors n)

/-- **Complete multiplicativity on the positive integers** — the hypothesis
`NonasymptoticLogElliott` imposes on both of its functions, and the one `z^ω` fails. -/
theorem isCompletelyMultiplicative_zOm (z : ℂ) :
    Erdos67b.IsCompletelyMultiplicativeOnPositive
      (fun n : ℕ => z ^ ArithmeticFunction.cardFactors n) := by
  constructor
  · simp
  · intro m n hm hn
    simp only []
    rw [ArithmeticFunction.cardFactors_mul hm.ne' hn.ne', pow_add]

theorem isMultiplicativeOnPositiveInt_zOmInt (z : ℂ) :
    Erdos67b.IsMultiplicativeOnPositiveInt (zOmInt z) :=
  Erdos67b.positiveIntExtension_isMultiplicative (isCompletelyMultiplicative_zOm z)

/-- Unimodularity, the other pointwise hypothesis. -/
theorem norm_zOmInt_le_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℤ) : ‖zOmInt z n‖ ≤ 1 := by
  rw [zOmInt, Erdos67b.positiveIntExtension]
  by_cases h : 0 < n
  · rw [if_pos h, norm_pow, hz, one_pow]
  · rw [if_neg h, norm_zero]; norm_num

/-! ### The determinant of the two linear forms -/

/-- **The non-degeneracy hypothesis of `NonasymptoticLogElliott` holds automatically**, with
determinant exactly `1`, for the pair of linear forms produced by `inner_sum_linear_forms`.

`a₁ = e`, `b₁ = (a+1)/d`, `a₂ = d`, `b₂ = (a+2)/e`:
`a₁ b₂ − a₂ b₁ = (a+2) − (a+1) = 1`. -/
theorem linear_forms_det_eq_one {d e a : ℕ} (hd : 0 < d) (he : 0 < e)
    (hda : d ∣ a + 1) (hea : e ∣ a + 2) :
    (e : ℤ) * (((a + 2) / e : ℕ) : ℤ) - (d : ℤ) * (((a + 1) / d : ℕ) : ℤ) = 1 := by
  have h1 : d * ((a + 1) / d) = a + 1 := Nat.mul_div_cancel' hda
  have h2 : e * ((a + 2) / e) = a + 2 := Nat.mul_div_cancel' hea
  have h1' : (d : ℤ) * (((a + 1) / d : ℕ) : ℤ) = ((a : ℤ) + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h1
  have h2' : (e : ℤ) * (((a + 2) / e : ℕ) : ℤ) = ((a : ℤ) + 2) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h2
  rw [h1', h2']
  ring

/-- Restated in exactly the form the Elliott statement asks for. -/
theorem linear_forms_nondegenerate {d e a : ℕ} (hd : 0 < d) (he : 0 < e)
    (hda : d ∣ a + 1) (hea : e ∣ a + 2) :
    (e : ℤ) * (((a + 2) / e : ℕ) : ℤ) - (d : ℤ) * (((a + 1) / d : ℕ) : ℤ) ≠ 0 := by
  rw [linear_forms_det_eq_one hd he hda hea]
  norm_num

/-- The affine forms of `inner_sum_linear_forms` agree with `Erdos67b.integerAffine`. -/
theorem integerAffine_eq_linear_form (a₁ : ℕ) (b : ℕ) (j : ℕ) :
    Erdos67b.integerAffine a₁ (b : ℤ) j = ((a₁ * j + b : ℕ) : ℤ) := by
  rw [Erdos67b.integerAffine]
  push_cast
  ring

/-- Consequently the summand of `inner_sum_linear_forms` is literally the summand of
`Erdos67b.elliottLogCorrelation`, up to the harmonic weight. -/
theorem zOmInt_integerAffine (z : ℂ) (a₁ b j : ℕ) (hpos : 0 < a₁ * j + b) :
    zOmInt z (Erdos67b.integerAffine a₁ (b : ℤ) j)
      = z ^ ArithmeticFunction.cardFactors (a₁ * j + b) := by
  rw [integerAffine_eq_linear_form, zOmInt, Erdos67b.positiveIntExtension_natCast hpos]

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.linear_forms_det_eq_one
#print axioms NormalNumbers.CastingOut.isMultiplicativeOnPositiveInt_zOmInt
#print axioms NormalNumbers.CastingOut.zOmInt_integerAffine
