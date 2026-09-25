/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtElliottMatch

/-!
# Assembling the log-averaged `D = 2` rung

Laps 7–12 reduced the two-shift `ζ^ω` correlation to a finite sum, over coprime powerful pairs
`(d, e)` with `d, e ≤ Y`, of sums

    ∑_j  (weight) · ζ₀^{Ω(e j + b₀)} · ζ₁^{Ω(d j + b₁)} ,   b₀ = (a+1)/d, b₁ = (a+2)/e,

with a truncation error `(1 + log N) · bridgeTail(Y)` (lap 12) and both structural hypotheses of
`Erdos67b.NonasymptoticLogElliott` verified (lap 11, determinant exactly `1`).

One mismatch of *weights* remains between our sum and `Erdos67b.elliottLogCorrelation`: ours
carries the harmonic weight of the ORIGINAL variable `n = L j + a` (`L = de`), while the Elliott
correlation carries the harmonic weight of the PROGRESSION variable `j`.  This file shows the
two differ by an **absolutely bounded** amount:

    ∑_{j ≥ 1} | 1/(Lj + a) − 1/(Lj) |  =  ∑_{j ≥ 1} a / (Lj(Lj+a))  ≤  (a/L²)·∑ j⁻²  ≤  2/L ,

using `a < L` (which `exists_joint_class` provides).  Summed over the `(d, e)` with `d, e ≤ Y`
this is a constant `C(Y)` depending on `Y` **but not on `N`** — and since `Y` is chosen from `ε`
*before* `N → ∞`, it is negligible against the main term of size `≍ log W`.

That is the last structural obstruction.  What is then left is genuinely the deep input:
`Erdos67b.NonasymptoticLogElliott` itself, which in this repo is the open, ratified bet
`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott` (Tao, Forum Math. Pi 4 (2016), Thm 1.3).
Note it is the GENERAL two-function, two-form statement that is needed: the dependency's proved
`Erdos67b.unitCircleLogElliott` covers only `g₂ = conj g₁` along `n` and `n + h`, whereas our two
twists `ζ₀, ζ₁` are independent and our two forms have leading coefficients `e` and `d`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- `∑_{j=1}^{J} j⁻² ≤ 2 − 1/J`, by telescoping.  (Elementary; avoids invoking Basel.) -/
theorem sum_inv_sq_le (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ ≤ 2 - 1 / (J : ℝ) := by
  induction J with
  | zero => omega
  | succ J ih =>
    rcases Nat.eq_or_lt_of_le hJ with h1 | h1
    · have : J = 0 := by omega
      subst this
      norm_num
    · have hJ1 : 1 ≤ J := by omega
      have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ1
      have hJ1R : (0 : ℝ) < ((J : ℝ) + 1) := by linarith
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : (((J + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / (J : ℝ) - 1 / ((J : ℝ) + 1) := by
        have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have heq : 1 / (J : ℝ) - 1 / ((J : ℝ) + 1) = 1 / ((J : ℝ) * ((J : ℝ) + 1)) := by
          field_simp
          ring
        rw [heq, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have hcast2 : (((J + 1 : ℕ) : ℝ)) = (J : ℝ) + 1 := by push_cast; ring
      calc ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ + (((J + 1 : ℕ) : ℝ) ^ 2)⁻¹
          ≤ (2 - 1 / (J : ℝ)) + (1 / (J : ℝ) - 1 / ((J : ℝ) + 1)) :=
            add_le_add (ih hJ1) hstep
        _ = 2 - 1 / ((J : ℝ) + 1) := by ring
        _ = 2 - 1 / ((J + 1 : ℕ) : ℝ) := by rw [hcast2]

/-- **Weight transfer.**  Replacing the harmonic weight of the original variable `n = Lj + a`
by that of the progression variable `j` (scaled by `1/L`) costs at most `2/L`, uniformly in the
length `J` of the sum and in the summand `G`. -/
theorem weight_transfer {L a : ℕ} (hL : 0 < L) (haL : a < L) (J : ℕ) (G : ℕ → ℂ)
    (hG : ∀ j, ‖G j‖ ≤ 1) :
    ‖(∑ j ∈ Icc 1 J, (((L * j + a : ℕ) : ℝ))⁻¹ • G j)
        - (L : ℝ)⁻¹ • ∑ j ∈ Icc 1 J, ((j : ℝ))⁻¹ • G j‖ ≤ 2 / (L : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hrw : (∑ j ∈ Icc 1 J, (((L * j + a : ℕ) : ℝ))⁻¹ • G j)
      - (L : ℝ)⁻¹ • ∑ j ∈ Icc 1 J, ((j : ℝ))⁻¹ • G j
      = ∑ j ∈ Icc 1 J, ((((L * j + a : ℕ) : ℝ))⁻¹ - (L : ℝ)⁻¹ * ((j : ℝ))⁻¹) • G j := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, sub_smul]
  rw [hrw]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Icc 1 J,
      ‖((((L * j + a : ℕ) : ℝ))⁻¹ - (L : ℝ)⁻¹ * ((j : ℝ))⁻¹) • G j‖
        ≤ (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hjR : (0 : ℝ) < (j : ℝ) := by linarith
    have hcast : ((L * j + a : ℕ) : ℝ) = (L : ℝ) * (j : ℝ) + (a : ℝ) := by push_cast; ring
    have hden : (0 : ℝ) < (L : ℝ) * (j : ℝ) + (a : ℝ) := by positivity
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
    have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjR
    have hdne : (L : ℝ) * (j : ℝ) + (a : ℝ) ≠ 0 := ne_of_gt hden
    have hdiff : (((L * j + a : ℕ) : ℝ))⁻¹ - (L : ℝ)⁻¹ * ((j : ℝ))⁻¹
        = - ((a : ℝ) / (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ)))) := by
      rw [hcast]
      field_simp
      ring
    rw [norm_smul, hdiff]
    have hGj := hG j
    have hbound : ‖- ((a : ℝ) / (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ))))‖
        ≤ (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      have h1 : (L : ℝ) ^ 2 * (j : ℝ) ^ 2 ≤ ((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ)) := by
        have hprod : (0 : ℝ) ≤ (L : ℝ) * (j : ℝ) * (a : ℝ) :=
          mul_nonneg (mul_nonneg hLR.le hjR.le) (Nat.cast_nonneg a)
        nlinarith [hprod]
      have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      calc (a : ℝ) = (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ * ((L : ℝ) ^ 2 * (j : ℝ) ^ 2) := by
            field_simp
        _ ≤ (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ *
              (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ))) := by
            refine mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ‖- ((a : ℝ) / (((L : ℝ) * (j : ℝ)) * ((L : ℝ) * (j : ℝ) + (a : ℝ))))‖ * ‖G j‖
        ≤ ((a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹) * 1 :=
          mul_le_mul hbound hGj (norm_nonneg _) (by positivity)
      _ = (a : ℝ) / (L : ℝ) ^ 2 * ((j : ℝ) ^ 2)⁻¹ := mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · norm_num
    positivity
  · have hsum : ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ ≤ 2 := by
      refine (sum_inv_sq_le J hJ).trans ?_
      have : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
      have : 0 < 1 / (J : ℝ) := by positivity
      linarith
    have haL' : (a : ℝ) ≤ (L : ℝ) := by
      have : a ≤ L := le_of_lt haL
      exact_mod_cast this
    calc (a : ℝ) / (L : ℝ) ^ 2 * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹
        ≤ (a : ℝ) / (L : ℝ) ^ 2 * 2 := by
          refine mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (L : ℝ) / (L : ℝ) ^ 2 * 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact div_le_div_of_nonneg_right haL' (by positivity)
      _ = 2 / (L : ℝ) := by field_simp

/-! ### The window mismatch: an initial segment is a stack of Elliott windows

`Erdos67b.elliottLogCorrelation` lives on the window `X/W < j ≤ X`, while laps 8–12 produce an
initial segment `1 ≤ j ≤ J`.  With the window ratio held FIXED at `W = A` and `X = A^m`, the
window is exactly `(A^{m−1}, A^m]`, and these tile `(1, A^M]`.  So an initial segment of length
`A^M` is a stack of `M` Elliott windows plus the single point `j = 1`.

Each window contributes `≤ ε log W = ε log A` (that is what Elliott gives at fixed `A`), so the
stack contributes `≤ ε M log A = ε log(A^M)` — the bound is *proportional to the log-mass of the
initial segment*, which is exactly the shape needed.  The `log A` per window does not accumulate
into anything worse: `M log A` is the log of the length, not `M` times the answer.
-/

/-- With ratio `W = A` and endpoint `X = A^m` (`m ≥ 1`), the Elliott window is `(A^{m−1}, A^m]`. -/
theorem elliottLogWindow_pow {A m : ℕ} (hA : 0 < A) (hm : 1 ≤ m) :
    Erdos67b.elliottLogWindow (A ^ m) A = Ioc (A ^ (m - 1)) (A ^ m) := by
  ext n
  rw [Erdos67b.mem_elliottLogWindow, Finset.mem_Ioc]
  have hpow : A * A ^ (m - 1) = A ^ m := by
    rw [← pow_succ']
    congr 1
    omega
  constructor
  · rintro ⟨hn0, hnX, hXn⟩
    refine ⟨?_, hnX⟩
    rw [← hpow] at hXn
    exact lt_of_mul_lt_mul_left hXn (Nat.zero_le A)
  · rintro ⟨hlow, hnX⟩
    have hpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlow
    refine ⟨hpos, hnX, ?_⟩
    rw [← hpow]
    exact Nat.mul_lt_mul_of_pos_left hlow hA

/-- An initial segment decomposes as the point `1` plus a stack of consecutive windows. -/
theorem sum_Ioc_pow_decomp {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A : ℕ) (hA : 1 ≤ A)
    (m : ℕ) :
    ∑ j ∈ Ioc 0 (A ^ m), f j
      = ∑ j ∈ Ioc 0 1, f j + ∑ i ∈ Icc 1 m, ∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j := by
  have hIoc01 : Ioc 0 1 = ({1} : Finset ℕ) := by decide
  induction m with
  | zero => simp [hIoc01]
  | succ m ih =>
    have hpow : A ^ m ≤ A ^ (m + 1) := Nat.pow_le_pow_right hA (by omega)
    have h1 : A ^ 0 ≤ A ^ m := Nat.pow_le_pow_right hA (Nat.zero_le m)
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    have hsplit : ∑ j ∈ Ioc 0 (A ^ m), f j + ∑ j ∈ Ioc (A ^ m) (A ^ (m + 1)), f j
        = ∑ j ∈ Ioc 0 (A ^ (m + 1)), f j :=
      Finset.sum_Ioc_consecutive f (Nat.zero_le _) hpow
    rw [← hsplit, Nat.add_sub_cancel]

/-- **The stacking bound.**  If every Elliott window contributes at most `B`, then the initial
segment `1 ≤ j ≤ A^m` contributes at most `‖f 1‖ + m · B`.  (`f 1` is the one point no window
covers, and its harmonic weight is `1`.) -/
theorem norm_sum_Ioc_pow_le {A : ℕ} (hA : 1 ≤ A) (f : ℕ → ℂ) (m : ℕ) (B : ℝ)
    (hwin : ∀ i ∈ Icc 1 m, ‖∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j‖ ≤ B) :
    ‖∑ j ∈ Ioc 0 (A ^ m), f j‖ ≤ ‖f 1‖ + m * B := by
  rw [sum_Ioc_pow_decomp f A hA m]
  have hIoc01 : Ioc 0 1 = ({1} : Finset ℕ) := by decide
  have h1 : ‖∑ j ∈ Ioc 0 1, f j‖ = ‖f 1‖ := by rw [hIoc01]; simp
  have hrest : ‖∑ i ∈ Icc 1 m, ∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j‖ ≤ (m : ℝ) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ i ∈ Icc 1 m, ‖∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j‖
        ≤ ∑ _i ∈ Icc 1 m, B := Finset.sum_le_sum hwin
      _ = (m : ℝ) * B := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
  have := norm_add_le (∑ j ∈ Ioc 0 1, f j) (∑ i ∈ Icc 1 m, ∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j)
  rw [h1] at this
  linarith

/-! ### The conditional rung

Everything above is unconditional.  Here the named open input enters, and ONLY here:
`Erdos67b.NonasymptoticLogElliott` — in this repo the ratified bet
`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott` (Tao, Forum Math. Pi 4 (2016), Thm 1.3).

The theorem below takes it as a hypothesis and returns the bound on an *initial segment*, which
is the form laps 8–13 need.  Note what is NOT a hypothesis: multiplicativity, unimodularity and
non-degeneracy are all discharged internally from `C3MrtElliottMatch`.  The only hypothesis left
to the caller is non-pretentiousness of the first twist — the genuinely arithmetic input, and
the easier case of lap 5's certificate since `ζ^Ω` is constant on primes.
-/

/-- **The `D = 2` rung, conditional on the general two-point log-Elliott theorem.**

Given `ε > 0` there is a threshold `A₀` such that for every `A ≥ A₀` at which the first twist is
non-pretentious, and every `m`, the initial segment `1 ≤ j ≤ A^m` of the two-linear-form
correlation of `ζ₀^Ω` and `ζ₁^Ω` is bounded by `1 + m·ε·log A = 1 + ε·log(A^m)`.

The bound is `ε` times the log-mass of the segment, plus an absolute constant — i.e. `o(log J)`
on the initial segment of length `J`, which is exactly the rung. -/
theorem initial_segment_bound_of_elliott
    (helliott : Erdos67b.NonasymptoticLogElliott)
    {d e b₀ b₁ : ℕ} (hd : 0 < d) (he : 0 < e)
    (hdet : (e : ℤ) * (b₁ : ℤ) - (d : ℤ) * (b₀ : ℤ) ≠ 0)
    (z₀ z₁ : ℂ) (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A →
      (∀ X : ℕ, ∀ q : ℕ, 0 < q → q ≤ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
          |t| ≤ (A : ℝ) * X →
            (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist
              (Erdos67b.restrictToNat (zOmInt z₀)) χ t X) →
      ∀ m : ℕ,
        ‖∑ j ∈ Ioc 0 (A ^ m),
            (Erdos67b.harmonicWeight j : ℂ) * zOmInt z₀ (Erdos67b.integerAffine e (b₀ : ℤ) j) *
              zOmInt z₁ (Erdos67b.integerAffine d (b₁ : ℤ) j)‖
          ≤ 1 + (m : ℝ) * (ε * Real.log A) := by
  obtain ⟨A₀, hA₀2, hA₀⟩ := helliott e d (b₀ : ℤ) (b₁ : ℤ) he hd hdet ε hε
  refine ⟨A₀, hA₀2, fun A hA hpret m => ?_⟩
  have hA1 : 1 ≤ A := by omega
  set f : ℕ → ℂ := fun j =>
    (Erdos67b.harmonicWeight j : ℂ) * zOmInt z₀ (Erdos67b.integerAffine e (b₀ : ℤ) j) *
      zOmInt z₁ (Erdos67b.integerAffine d (b₁ : ℤ) j) with hf
  have hwin : ∀ i ∈ Icc 1 m, ‖∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j‖ ≤ ε * Real.log A := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hWX : A ≤ A ^ i := by
      calc A = A ^ 1 := (pow_one A).symm
        _ ≤ A ^ i := Nat.pow_le_pow_right hA1 hi.1
    have hcorr : ∑ j ∈ Ioc (A ^ (i - 1)) (A ^ i), f j
        = Erdos67b.elliottLogCorrelation (zOmInt z₀) (zOmInt z₁) e d (b₀ : ℤ) (b₁ : ℤ) (A ^ i) A := by
      rw [Erdos67b.elliottLogCorrelation, ← elliottLogWindow_pow (by omega) hi.1]
    rw [hcorr]
    exact hA₀ A (A ^ i) A hA (le_refl A) hWX (zOmInt z₀) (zOmInt z₁)
      (isMultiplicativeOnPositiveInt_zOmInt z₀) (isMultiplicativeOnPositiveInt_zOmInt z₁)
      (norm_zOmInt_le_one hz₀) (norm_zOmInt_le_one hz₁) (hpret (A ^ i))
  have hone : ‖f 1‖ ≤ 1 := by
    rw [hf]
    simp only []
    rw [norm_mul, norm_mul]
    have h1 : ‖((Erdos67b.harmonicWeight 1 : ℝ) : ℂ)‖ = 1 := by
      rw [Erdos67b.harmonicWeight]
      norm_num
    rw [h1, one_mul]
    exact mul_le_one₀ (norm_zOmInt_le_one hz₀ _) (norm_nonneg _) (norm_zOmInt_le_one hz₁ _)
  have := norm_sum_Ioc_pow_le hA1 f m (ε * Real.log A) hwin
  linarith

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.sum_inv_sq_le
#print axioms NormalNumbers.CastingOut.weight_transfer
#print axioms NormalNumbers.CastingOut.elliottLogWindow_pow
#print axioms NormalNumbers.CastingOut.norm_sum_Ioc_pow_le
#print axioms NormalNumbers.CastingOut.initial_segment_bound_of_elliott
