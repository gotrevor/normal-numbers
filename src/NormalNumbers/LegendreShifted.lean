/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Shifted Legendre polynomials and small linear forms in `log 2` (VENDORED)

**Provenance**: vendored 2026-08-29 from `~/src/collatz-moonshot`
`CollatzMoonshot/FrontA/Legendre.lean` (same mathlib pin), re-homed by copy into
`NormalNumbers.Legendre` per the dep re-homing decision — never via axioms.  That
module in turn adapts the shifted-Legendre backbone from ahhwuhu's Apache-2.0
`zeta_3_irrational` (commit `e8785315a01c8fbcddaa0fc03b3c8b29a61bc1f1`).  Only the
namespace and this header were changed here.

Headline: `legendre_log_two_small` — for every `n` a **nonzero** integer
combination `P + Q·log 2` with `|P + Q·log 2| ≤ lcm(1..n)·(1/5)ⁿ`.  The
coefficient-height and remainder-lower bounds the ExpSep discharge needs are NOT
here; they are proved in `LegendreHeight.lean` on top of this backbone.
-/

open scoped Nat
open BigOperators Finset Polynomial

namespace NormalNumbers.Legendre

variable {R : Type*}

/-- `shiftedLegendre n` is the shifted Legendre polynomial `(n!)⁻¹ · (d/dx)^n (x^n (1-x)^n)`. -/
noncomputable def shiftedLegendre (n : ℕ) : ℝ[X] :=
  C (n ! : ℝ)⁻¹ * derivative^[n] (X ^ n * (1 - X) ^ n)

private lemma Finsum_iterate_deriv [CommRing R] (k : ℕ) (h : ℕ → ℕ) :
    derivative^[k] (∑ m ∈ Finset.range (k + 1), (h m) • ((-1) ^ m : R[X]) * X ^ (k + m)) =
    ∑ m ∈ Finset.range (k + 1), (h m) • (-1) ^ m * derivative^[k] (X ^ (k + m)) := by
  induction' k + 1 with n hn
  · simp only [Finset.range_zero, Finset.sum_empty, iterate_map_zero]
  · rw [Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
    simp only [Fin.coe_castSucc, Fin.val_last, iterate_map_add, hn, add_right_inj]
    rw [nsmul_eq_mul, mul_assoc, ← nsmul_eq_mul, Polynomial.iterate_derivative_smul, nsmul_eq_mul,
      mul_assoc]
    rcases n.even_or_odd with (hn1 | hn2)
    · simp_all only [nsmul_eq_mul, Int.even_coe_nat, Even.neg_pow, one_pow, one_mul]
    · rw [Odd.neg_one_pow]
      simp only [neg_mul, one_mul, iterate_map_neg, mul_neg]
      exact_mod_cast hn2

/-- The expansion of `shiftedLegendre n` as an explicit polynomial sum. -/
theorem shiftedLegendre_eq_sum (n : ℕ) : shiftedLegendre n = ∑ k ∈ Finset.range (n + 1),
    C ((-1) ^ k : ℝ) * (Nat.choose n k : ℝ[X]) * (Nat.choose (n + k) n : ℝ[X]) * X ^ k := by
  have h : ((X : ℝ[X]) - X ^ 2) ^ n =
      ∑ m ∈ range (n + 1), n.choose m • (- 1) ^ m * X ^ (n + m) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw [neg_pow, pow_two, mul_pow, ← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw [Finset.mem_range] at hm
    linarith
  rw [shiftedLegendre, ← mul_pow, mul_one_sub, ← pow_two, h, Finsum_iterate_deriv,
    Finset.mul_sum]
  congr! 1 with x _
  rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div
    (by omega), show n + x - n = x by omega, nsmul_eq_mul, ← mul_assoc, mul_assoc,
    mul_comm]
  simp only [Int.reduceNeg, map_pow, map_neg, map_one]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, ← mul_assoc, ← mul_assoc, add_comm,
    Nat.add_choose, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm]
  nth_rewrite 5 [mul_comm]
  congr 1
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  nth_rewrite 3 [mul_comm]
  congr 1
  apply Polynomial.ext
  intro m
  simp only [one_div, coeff_mul_C, coeff_natCast_ite, Nat.cast_ite, CharP.cast_eq_zero, ite_mul,
    zero_mul]
  by_cases h : m = 0
  · simp only [h, ↓reduceIte]
    rw [Nat.cast_div]
    · rw [← one_div, ← div_mul_eq_div_mul_one_div]
      norm_cast
      rw [Nat.cast_div]
      · exact Nat.factorial_mul_factorial_dvd_factorial_add x n
      · norm_cast
        apply mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero n)
    · exact Nat.factorial_dvd_factorial (by omega)
    · norm_cast; exact Nat.factorial_ne_zero x
  · simp only [h, ↓reduceIte]

/-- **`shiftedLegendre n` is an integer polynomial.**  Coefficients
`(-1)^k · C(n,k) · C(n+k,n) ∈ ℤ`; this is the integrality that lets `lcm(1..n)` (leg 1) clear all
denominators of the approximant's linear form. -/
lemma shiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, shiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k : ℝ[X]) * X ^ k := by
  simp_rw [shiftedLegendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  congr! 1 with x
  push_cast
  simp only [map_pow, map_neg, map_one]

/-- **Vanishing at `0` to order `n` (Padé contact).**  For `m < n`, the `m`-th derivative of
`x^n (1-x)^n` vanishes at `0`.  Makes the boundary terms of the integration-by-parts identity (that
turns `∫₀¹ P_n·f` into the linear form) vanish. -/
lemma shiftedLegendre_poly_eval_zero_eq_zero (n : ℕ) {m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X, smul_eq_mul,
    mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', ne_eq,
    true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := h

/-- **Vanishing at `1` to order `n` (Padé contact).**  For `m < n`, the `m`-th derivative of
`x^n (1-x)^n` vanishes at `1`.  The companion boundary condition. -/
lemma shiftedLegendre_poly_eval_one_eq_zero (n : ℕ) {m : ℕ} (h : m < n) :
    eval 1 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; right
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul, eval_pow,
    eval_neg, eval_one, eval_sub, eval_X, sub_self, smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    true_and, false_or]
  right
  suffices n - x > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  linarith

/-- **Single integration-by-parts step against a Legendre-derivative polynomial.**  If a polynomial
`p` vanishes at both endpoints, then `∫₀¹ (p')·g = −∫₀¹ p·g'` (the boundary term dies).  This is the
inductive engine of the `n`-fold Legendre IBP identity. -/
private lemma legendre_ibp_step (p : ℝ[X]) (g g' : ℝ → ℝ)
    (hp0 : eval 0 p = 0) (hp1 : eval 1 p = 0)
    (hg : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' y) y)
    (hg' : ContinuousOn g' (Set.uIcc (0 : ℝ) 1)) :
    ∫ y in (0 : ℝ)..1, eval y (derivative p) * g y
      = - ∫ y in (0 : ℝ)..1, eval y p * g' y := by
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y => eval y p) (u' := fun y => eval y (derivative p)) (v := g) (v' := g')
    (fun y _ => p.hasDerivAt y) hg
    ((Polynomial.continuous (derivative p)).intervalIntegrable 0 1)
    hg'.intervalIntegrable
  rw [hp0, hp1] at key
  simp only [zero_mul, sub_zero, zero_sub] at key
  linarith [key]

/-- **Legendre integration-by-parts identity (leg 2 core).**  For any `f` whose iterated derivatives
`deriv^[k] f` (`k ≤ n`) are continuous on `[0,1]` and differentiable there (`k < n`),
`∫₀¹ P_n(y)·f(y) dy = ((-1)^n / n!) · ∫₀¹ y^n(1-y)^n · f⁽ⁿ⁾(y) dy`, where `P_n = shiftedLegendre n`.
Proof: `n`-fold integration by parts (`legendre_ibp_step`); every boundary term vanishes by
`shiftedLegendre_poly_eval_{zero,one}_eq_zero`.  Specialized to a Möbius kernel `f(y)=1/(1−(1−c)y)`
this yields the linear form `A_n + B_n·log c` with geometrically small remainder — the analytic heart
of Rhin's effective measure of `log₂3` (see `Gelfond.lean`). -/
theorem integral_shiftedLegendre_mul_eq (n : ℕ) (f : ℝ → ℝ)
    (hcont : ∀ k, k ≤ n → ContinuousOn (deriv^[k] f) (Set.uIcc (0 : ℝ) 1))
    (hderiv : ∀ k, k < n → ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (deriv^[k] f) (deriv^[k + 1] f y) y) :
    ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * f y
      = ((-1) ^ n / n !) * ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) * (deriv^[n] f) y := by
  have aux : ∀ m, m ≤ n →
      ∫ y in (0 : ℝ)..1, eval y (derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) * f y
        = (-1) ^ m * ∫ y in (0 : ℝ)..1,
            eval y (derivative^[n - m] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) * (deriv^[m] f) y := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hjn : j < n := hj
        rw [ih (le_of_lt hjn)]
        have hidx : derivative^[n - j] ((X : ℝ[X]) ^ n * (1 - X) ^ n)
            = derivative (derivative^[n - (j + 1)] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) := by
          have hnj : n - j = (n - (j + 1)) + 1 := by omega
          rw [hnj, Function.iterate_succ_apply']
        have hp := legendre_ibp_step (derivative^[n - (j + 1)] ((X : ℝ[X]) ^ n * (1 - X) ^ n))
          (deriv^[j] f) (deriv^[j + 1] f)
          (shiftedLegendre_poly_eval_zero_eq_zero n (by omega))
          (shiftedLegendre_poly_eval_one_eq_zero n (by omega))
          (hderiv j hjn) (hcont (j + 1) hj)
        rw [hidx, hp, pow_succ]
        ring
  have H := aux n le_rfl
  rw [Nat.sub_self] at H
  simp only [Function.iterate_zero, id_eq] at H
  have hUval : (fun y : ℝ => eval y ((X : ℝ[X]) ^ n * (1 - X) ^ n) * (deriv^[n] f) y)
      = fun y : ℝ => (y ^ n * (1 - y) ^ n) * (deriv^[n] f) y := by
    funext y; simp [eval_mul, eval_pow]
  rw [hUval] at H
  -- pull the constant `(n!)⁻¹` out of the shiftedLegendre integral
  have hLHS : (fun y : ℝ => eval y (shiftedLegendre n) * f y)
      = fun y : ℝ => (n ! : ℝ)⁻¹ * (eval y (derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) * f y) := by
    funext y; simp only [shiftedLegendre, eval_mul, eval_C]; ring
  rw [hLHS, intervalIntegral.integral_const_mul, H]
  ring

/-- **`n`-th derivative of the Möbius kernel `1/(1-a·x)`** wherever the denominator is nonzero:
`dⁿ/dxⁿ [1/(1-a·x)] = n!·aⁿ/(1-a·x)^(n+1)`.  Proved by neighborhood-congruence induction — the set
`{x | 1-a·x ≠ 0}` is open, so no singular-point analysis is needed.  This is the kernel derivative the
Legendre IBP identity (`integral_shiftedLegendre_mul_eq`) consumes to produce the linear form. -/
lemma mobius_iterate_deriv (a : ℝ) (n : ℕ) :
    ∀ x : ℝ, 1 - a * x ≠ 0 →
      deriv^[n] (fun x => 1 / (1 - a * x)) x = (n ! : ℝ) * a ^ n / (1 - a * x) ^ (n + 1) := by
  induction n with
  | zero => intro x hx; simp
  | succ n ih =>
      intro x hx
      have hopen : IsOpen {y : ℝ | 1 - a * y ≠ 0} := isOpen_ne.preimage (by fun_prop)
      have hU : {y : ℝ | 1 - a * y ≠ 0} ∈ nhds x := hopen.mem_nhds hx
      have hEq : deriv^[n] (fun x => 1 / (1 - a * x))
          =ᶠ[nhds x] fun y => (n ! : ℝ) * a ^ n / (1 - a * y) ^ (n + 1) :=
        Filter.eventually_of_mem hU (fun y hy => ih y hy)
      have h1 : HasDerivAt (fun y => 1 - a * y) (-a) x := by
        simpa using ((hasDerivAt_id x).const_mul a).const_sub 1
      have hg := (hasDerivAt_const x ((n ! : ℝ) * a ^ n)).div (h1.pow (n + 1))
        (pow_ne_zero _ hx)
      have hfn := hg.congr_of_eventuallyEq hEq
      rw [Function.iterate_succ_apply', hfn.deriv]
      simp only [Pi.pow_apply, Nat.add_sub_cancel]
      have hxp : (1 - a * x) ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
      field_simp
      rw [Nat.factorial_succ]
      push_cast
      ring

/-- **Padé remainder form of the Legendre–Möbius integral (leg 2, assembled).**  For `a < 1` (so
`1-a·y > 0` on `[0,1]`),
`∫₀¹ P_n(y)/(1-a·y) dy = (-a)ⁿ · ∫₀¹ yⁿ(1-y)ⁿ/(1-a·y)^(n+1) dy`.
Combines the `n`-fold IBP identity (`integral_shiftedLegendre_mul_eq`) with the kernel derivative
(`mobius_iterate_deriv`).  The right side is the geometrically small remainder: its integrand is
`(y(1-y)/(1-a·y))ⁿ · 1/(1-a·y)`, and `y(1-y)/(1-a·y) ≤ 1/4·(1/(1-a))` on `[0,1]`, so a suitable
`a` makes it `≤ ρⁿ` with `ρ < 1`.  Specializing `a` to values with `log(1-a) ∈ {±log2, ±log3}`
(from Rhin's kernel) turns the left side into the integer linear form `A_n + B_n·log c`. -/
theorem legendre_mobius_integral (a : ℝ) (n : ℕ) (ha : a < 1) :
    ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * (1 / (1 - a * y))
      = (-a) ^ n * ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1) := by
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 - a * y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · simp [← h]
    · nlinarith [mul_pos (sub_pos.2 ha) h, hy.2]
  have hopen : IsOpen {y : ℝ | 1 - a * y ≠ 0} := isOpen_ne.preimage (by fun_prop)
  -- continuity of each iterated derivative on `[0,1]`
  have hcont : ∀ k, k ≤ n → ContinuousOn (deriv^[k] (fun x => 1 / (1 - a * x)))
      (Set.uIcc (0 : ℝ) 1) := by
    intro k _
    have hgk : ContinuousOn (fun z => (k ! : ℝ) * a ^ k / (1 - a * z) ^ (k + 1))
        (Set.uIcc (0 : ℝ) 1) :=
      ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun z hz => pow_ne_zero _ (ne_of_gt (hpos z hz)))
    exact hgk.congr (fun z hz => mobius_iterate_deriv a k z (ne_of_gt (hpos z hz)))
  -- differentiability giving `HasDerivAt (deriv^[k] f) (deriv^[k+1] f y) y`
  have hderiv : ∀ k, k < n → ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (deriv^[k] (fun x => 1 / (1 - a * x)))
        (deriv^[k + 1] (fun x => 1 / (1 - a * x)) y) y := by
    intro k _ y hy
    have hyne : (1 : ℝ) - a * y ≠ 0 := ne_of_gt (hpos y hy)
    have hEqk : deriv^[k] (fun x => 1 / (1 - a * x))
        =ᶠ[nhds y] fun z => (k ! : ℝ) * a ^ k / (1 - a * z) ^ (k + 1) :=
      Filter.eventually_of_mem (hopen.mem_nhds hyne)
        (fun z hz => mobius_iterate_deriv a k z hz)
    have h1y : HasDerivAt (fun z => 1 - a * z) (-a) y := by
      simpa using ((hasDerivAt_id y).const_mul a).const_sub 1
    have hV := (hasDerivAt_const y ((k ! : ℝ) * a ^ k)).div (h1y.pow (k + 1))
      (pow_ne_zero _ hyne)
    have hdiff : DifferentiableAt ℝ (deriv^[k] (fun x => 1 / (1 - a * x))) y :=
      (hV.congr_of_eventuallyEq hEqk).differentiableAt
    have hh := hdiff.hasDerivAt
    have hval : deriv^[k + 1] (fun x => 1 / (1 - a * x)) y
        = deriv (deriv^[k] (fun x => 1 / (1 - a * x))) y := by
      rw [Function.iterate_succ_apply']
    rw [hval]; exact hh
  calc ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * (1 / (1 - a * y))
      = ((-1) ^ n / n !) * ∫ y in (0 : ℝ)..1,
          (y ^ n * (1 - y) ^ n) * (deriv^[n] (fun x => 1 / (1 - a * x)) y) :=
        integral_shiftedLegendre_mul_eq n _ hcont hderiv
    _ = ((-1) ^ n / n !) * ((n ! : ℝ) * a ^ n *
          ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1)) := by
        congr 1
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro y hy
        dsimp only
        rw [mobius_iterate_deriv a n y (ne_of_gt (hpos y hy))]
        ring
    _ = (-a) ^ n * ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1) := by
        have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        rw [neg_pow a n]
        field_simp
        ring

/-- **Remainder size bound (leg 2).**  For `0 ≤ a < 1`, the Padé remainder integral satisfies
`∫₀¹ yⁿ(1-y)ⁿ/(1-a·y)^(n+1) dy ≤ (1/4)ⁿ / (1-a)^(n+1)`.  Since `y(1-y) ≤ 1/4` and `1-a·y ≥ 1-a`
on `[0,1]`, the integrand is `≤ (1/4)ⁿ/(1-a)^(n+1)` pointwise.  Combined with
`legendre_mobius_integral`, `|∫₀¹ P_n/(1-a·y)| ≤ |a|ⁿ·(1/4)ⁿ/(1-a)^(n+1) = (|a|/(4(1-a)))ⁿ/(1-a)`,
which is `≤ ρⁿ` with `ρ = |a|/(4(1-a)) < 1` whenever `a < 4/5` — the geometric decay leg 2 needs. -/
theorem legendre_mobius_remainder_bound (a : ℝ) (n : ℕ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1)
      ≤ (1 / 4) ^ n / (1 - a) ^ (n + 1) := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hbound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1) ≤ (1 / 4) ^ n / (1 - a) ^ (n + 1) := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hday : 1 - a ≤ 1 - a * y := by nlinarith
    rw [← mul_pow]
    gcongr
    nlinarith [sq_nonneg (y - 1 / 2)]
  have hint : IntervalIntegrable (fun y => (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    exact pow_ne_zero _ (ne_of_gt (by nlinarith))
  calc ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1)
      ≤ ∫ _ in (0 : ℝ)..1, (1 / 4) ^ n / (1 - a) ^ (n + 1) :=
        intervalIntegral.integral_mono_on (by norm_num) hint
          (intervalIntegrable_const) hbound
    _ = (1 / 4) ^ n / (1 - a) ^ (n + 1) := by simp

/-- **Base Möbius integral (source of the log term).**  For `a < 1`, `a ≠ 0`,
`∫₀¹ 1/(1-a·y) dy = -log(1-a)/a`.  This is where the transcendental `log(1-a)` enters the linear
form `A_n + B_n·log(1-a)` extracted from `∫₀¹ P_n/(1-a·y)` (the higher moments `∫₀¹ yᵏ/(1-a·y)`
reduce to this one plus rationals).  Proved by FTC with antiderivative `-log(1-a·y)/a`. -/
theorem mobius_base_integral (a : ℝ) (ha : a < 1) (ha0 : a ≠ 0) :
    ∫ y in (0 : ℝ)..1, 1 / (1 - a * y) = -Real.log (1 - a) / a := by
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, (0 : ℝ) < 1 - a * y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    rcases le_total a 0 with h | h
    · nlinarith [hy.1]
    · nlinarith [hy.2, mul_nonneg h (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y)]
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => -Real.log (1 - a * y) / a) (1 / (1 - a * y)) y := by
    intro y hy
    have hyne : (1 : ℝ) - a * y ≠ 0 := ne_of_gt (hpos y hy)
    have h1 : HasDerivAt (fun y => 1 - a * y) (-a) y := by
      simpa using ((hasDerivAt_id y).const_mul a).const_sub 1
    have hlog : HasDerivAt (fun y => Real.log (1 - a * y)) (-a / (1 - a * y)) y :=
      h1.log hyne
    have hval : -(-a / (1 - a * y)) / a = 1 / (1 - a * y) := by
      field_simp
    rw [← hval]
    exact (hlog.neg).div_const a
  have hint : IntervalIntegrable (fun y => 1 / (1 - a * y)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun y hy => ne_of_gt (hpos y hy)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **Moment recursion** `a·∫₀¹ yᵏ⁺¹/(1-a·y) = ∫₀¹ yᵏ/(1-a·y) − 1/(k+1)`.  Pointwise
`a·yᵏ⁺¹/(1-a·y) = yᵏ/(1-a·y) − yᵏ` and `∫₀¹ yᵏ = 1/(k+1)`.  With `mobius_base_integral` (k=0), this
recursion shows every moment `∫₀¹ yᵏ/(1-a·y)` is `rational + rational·log(1-a)`, so expanding
`P_n` (integer coeffs) gives the linear form `A_n + B_n·log(1-a)` — the last analytic ingredient of
leg 2's linear-form extraction. -/
theorem mobius_moment_rec (a : ℝ) (ha : a < 1) (ha0 : a ≠ 0) (k : ℕ) :
    a * ∫ y in (0 : ℝ)..1, y ^ (k + 1) / (1 - a * y)
      = (∫ y in (0 : ℝ)..1, y ^ k / (1 - a * y)) - 1 / (k + 1) := by
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, (0 : ℝ) < 1 - a * y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    rcases le_total a 0 with h | h
    · nlinarith [hy.1]
    · nlinarith [hy.2, mul_nonneg h (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y)]
  have hI : ∀ j : ℕ, IntervalIntegrable (fun y => y ^ j / (1 - a * y))
      MeasureTheory.volume 0 1 := by
    intro j
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun y hy => ne_of_gt (hpos y hy)
  rw [← intervalIntegral.integral_const_mul]
  have hcongr : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      a * (y ^ (k + 1) / (1 - a * y)) = y ^ k / (1 - a * y) - y ^ k := by
    intro y hy
    have hyne : (1 : ℝ) - a * y ≠ 0 := ne_of_gt (hpos y hy)
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_sub (hI k) ((continuous_pow k).intervalIntegrable 0 1),
    integral_pow]
  norm_num

/-- **Closed form of the moments: `∫₀¹ yᵏ/(1-a·y) = rₖ − log(1-a)/aᵏ⁺¹`** for some real `rₖ`.
Induction from `mobius_base_integral` (k=0) via `mobius_moment_rec`.  Exhibits the log coefficient
explicitly (`−1/aᵏ⁺¹`); the remainder `rₖ` is a real number built from rationals (`rₖ₊₁ =
(rₖ − 1/(k+1))/a`), so `∫₀¹ P_n/(1-a·y) = A_n + B_n·log(1-a)` with `B_n = −∑ c_k/aᵏ⁺¹` and `A_n = ∑
c_k rₖ` (`c_k` = integer Legendre coeffs).  This packages leg 2's linear-form structure. -/
theorem mobius_moment_closed (a : ℝ) (ha : a < 1) (ha0 : a ≠ 0) : ∀ k : ℕ,
    ∃ r : ℝ, ∫ y in (0 : ℝ)..1, y ^ k / (1 - a * y) = r - Real.log (1 - a) / a ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [pow_zero, pow_one]
      rw [mobius_base_integral a ha ha0]
      ring
  | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨(r - 1 / (k + 1)) / a, ?_⟩
      have hrec := mobius_moment_rec a ha ha0 k
      have hI1 : ∫ y in (0 : ℝ)..1, y ^ (k + 1) / (1 - a * y)
          = ((∫ y in (0 : ℝ)..1, y ^ k / (1 - a * y)) - 1 / (k + 1)) / a := by
        rw [eq_div_iff ha0]; linarith [hrec]
      rw [hI1, hr]
      field_simp
      ring

/-! ### Single-log denominator/integrality tracking (leg 2 → a genuine effective measure)

For an **integer** `a ≤ -1` (so `1 - a ∈ {2, 3, …}`, giving `log 2` at `a = -1`, `log 3` at `a = -2`),
the linear form `Λ_n = A_n + B_n·log(1-a)` becomes an **integer** combination after clearing by
`lcm(1..n)·a^(n+1)`.  This is the denominator leg of the effective irrationality measure (mathlib has
no effective measure of a single log), and the exact bookkeeping leg 3 reuses two-kernel-wise. -/

/-- `i ∣ lcmUpto n` whenever `1 ≤ i ≤ n`. -/
lemma dvd_lcmUpto {i n : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) : i ∣ Nat.lcmUpto n := by
  have h := Finset.dvd_lcm (f := (id : ℕ → ℕ)) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  simpa [Nat.lcmUpto] using h

/-- `lcmUpto k ∣ lcmUpto (k+1)` (the range grows by one). -/
lemma lcmUpto_dvd_succ (k : ℕ) : Nat.lcmUpto k ∣ Nat.lcmUpto (k + 1) := by
  simp only [Nat.lcmUpto]
  apply Finset.lcm_dvd
  intro b hb
  rw [Finset.mem_Icc] at hb
  show b ∣ Nat.lcmUpto (k + 1)
  exact dvd_lcmUpto hb.1 (by omega)

/-- **Per-moment integrality (single-log denominator tracking).**  For an integer `a ≤ -1`, each
Möbius moment cleared by `lcm(1..k)·a^(k+1)` is an *integer* plus an *integer* multiple of
`log(1-a)`:
`∃ s : ℤ, lcm(1..k)·a^(k+1)·∫₀¹ yᵏ/(1-a·y) = s − lcm(1..k)·log(1-a)`.
Induction on `mobius_moment_rec`, from the base `∫₀¹ 1/(1-a·y) = −log(1-a)/a`.  The step stays
integral because `lcm(1..k) ∣ lcm(1..k+1)` (`lcmUpto_dvd_succ`) and `(k+1) ∣ lcm(1..k+1)`
(`dvd_lcmUpto`) clear, respectively, the recursion's remainder and its `1/(k+1)` term.  The log
coefficient is *exactly* `−lcm(1..k)`, an integer — the source-independent core of leg 3's
`D_n·Λ_n = p_n + q_n·log(1-a)`. -/
theorem mobius_moment_int_cleared (a : ℤ) (ha : a ≤ -1) (k : ℕ) :
    ∃ s : ℤ, (Nat.lcmUpto k : ℝ) * (a : ℝ) ^ (k + 1) *
        (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y))
      = (s : ℝ) - (Nat.lcmUpto k : ℝ) * Real.log (1 - (a : ℝ)) := by
  have haR : (a : ℝ) < 1 := by exact_mod_cast (by omega : a < 1)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      have h0 : (Nat.lcmUpto 0 : ℝ) = 1 := by norm_num [Nat.lcmUpto]
      simp only [pow_zero]
      rw [mobius_base_integral (a : ℝ) haR ha0, h0]
      simp only [zero_add, pow_one, one_mul, Int.cast_zero, zero_sub]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha0]
  | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨d, hd⟩ := lcmUpto_dvd_succ k
      obtain ⟨e, he⟩ := dvd_lcmUpto (i := k + 1) (n := k + 1) (by omega) le_rfl
      refine ⟨(d : ℤ) * s - (e : ℤ) * a ^ (k + 1), ?_⟩
      have hrec := mobius_moment_rec (a : ℝ) haR ha0 k
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hdR : (Nat.lcmUpto (k + 1) : ℝ) = (Nat.lcmUpto k : ℝ) * (d : ℝ) := by
        rw [hd]; push_cast; ring
      have heR : (Nat.lcmUpto (k + 1) : ℝ) = ((k : ℝ) + 1) * (e : ℝ) := by
        rw [he]; push_cast; ring
      have E1 : (Nat.lcmUpto (k + 1) : ℝ) * (a : ℝ) ^ (k + 1) *
            (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y))
          = (d : ℝ) * (s : ℝ) - (Nat.lcmUpto (k + 1) : ℝ) * Real.log (1 - (a : ℝ)) := by
        have hreassoc : (Nat.lcmUpto (k + 1) : ℝ) * (a : ℝ) ^ (k + 1) *
              (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y))
            = (d : ℝ) * ((Nat.lcmUpto k : ℝ) * (a : ℝ) ^ (k + 1) *
              (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y))) := by
          rw [hdR]; ring
        rw [hreassoc, hs, hdR]; push_cast; ring
      have E2 : (Nat.lcmUpto (k + 1) : ℝ) * (a : ℝ) ^ (k + 1) * (1 / ((k : ℝ) + 1))
          = (e : ℝ) * (a : ℝ) ^ (k + 1) := by
        rw [heR]; field_simp
      rw [show (Nat.lcmUpto (k + 1) : ℝ) * (a : ℝ) ^ (k + 1 + 1) *
            (∫ y in (0 : ℝ)..1, y ^ (k + 1) / (1 - (a : ℝ) * y))
          = (Nat.lcmUpto (k + 1) : ℝ) * (a : ℝ) ^ (k + 1) *
            ((a : ℝ) * (∫ y in (0 : ℝ)..1, y ^ (k + 1) / (1 - (a : ℝ) * y))) from by ring,
        hrec, mul_sub, E1, E2]
      push_cast; ring

/-- `lcmUpto k ∣ lcmUpto n` whenever `k ≤ n`. -/
lemma lcmUpto_dvd_of_le {k n : ℕ} (h : k ≤ n) : Nat.lcmUpto k ∣ Nat.lcmUpto n := by
  simp only [Nat.lcmUpto]
  apply Finset.lcm_dvd
  intro b hb
  rw [Finset.mem_Icc] at hb
  show b ∣ Nat.lcmUpto n
  exact dvd_lcmUpto hb.1 (by omega)

/-- A finite sum of terms each of the shape `(integer) + (integer)·L` is again of that shape. -/
private lemma sum_int_linear {L : ℝ} (f : ℕ → ℝ) :
    ∀ (s : Finset ℕ), (∀ k ∈ s, ∃ p q : ℤ, f k = (p : ℝ) + (q : ℝ) * L) →
      ∃ P Q : ℤ, ∑ k ∈ s, f k = (P : ℝ) + (Q : ℝ) * L := by
  intro s
  induction s using Finset.induction with
  | empty => intro _; exact ⟨0, 0, by simp⟩
  | @insert x s hx ih =>
      intro h
      obtain ⟨px, qx, hxeq⟩ := h x (Finset.mem_insert_self x s)
      obtain ⟨P, Q, hPQ⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
      exact ⟨px + P, qx + Q, by rw [Finset.sum_insert hx, hxeq, hPQ]; push_cast; ring⟩

/-- **Integer linear form (single-log denominator clearing).**  For an integer
`a ≤ -1`, the Legendre–Möbius approximant, cleared by `D_n = lcm(1..n)·a^(n+1)`, is an **integer**
combination of `1` and `log(1-a)`:
`∃ P Q : ℤ, lcm(1..n)·a^(n+1)·∫₀¹ P_n(y)/(1-a·y) = P + Q·log(1-a)`.
Expand `P_n = ∑ c_k yᵏ` (integer coeffs, `shiftedLegendre_eq_int_poly`) and clear each moment with
`mobius_moment_int_cleared`; the per-`k` cofactor `c_k·(lcm(1..n)/lcm(1..k))·a^(n-k)` is an integer
because `lcm(1..k) ∣ lcm(1..n)` (`lcmUpto_dvd_of_le`) and `k ≤ n`. With
`legendre_mobius_ne_zero` and the geometric remainder bound, this supplies ingredients for
small integer linear forms. It is not by itself an irrationality measure: that would require
the appropriate decay and coefficient-height estimates. At `a = -2`, the clearing factor
also overwhelms this kernel's remainder. It is the one-kernel prototype of leg 3's
`D_n·Λ_n = p_n + q_n·log`. -/
theorem legendre_mobius_int_linear_form (a : ℤ) (ha : a ≤ -1) (n : ℕ) :
    ∃ P Q : ℤ, (Nat.lcmUpto n : ℝ) * (a : ℝ) ^ (n + 1) *
        (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (a : ℝ) * y))
      = (P : ℝ) + (Q : ℝ) * Real.log (1 - (a : ℝ)) := by
  have haR : (a : ℝ) < 1 := by exact_mod_cast (by omega : a < 1)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  set L : ℝ := Real.log (1 - (a : ℝ)) with hLdef
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, (0 : ℝ) < 1 - (a : ℝ) * y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    rcases le_total (a : ℝ) 0 with h | h
    · nlinarith [hy.1]
    · nlinarith [hy.2, mul_nonneg h (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y)]
  obtain ⟨c, hc⟩ := shiftedLegendre_eq_int_poly n
  -- expand the integral into a sum of moments
  have hInt : ∀ k ∈ Finset.range (n + 1),
      IntervalIntegrable (fun y => (c k : ℝ) * (y ^ k / (1 - (a : ℝ) * y)))
        MeasureTheory.volume 0 1 := by
    intro k _
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun y hy => ne_of_gt (hpos y hy)
  have hΛ : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - (a : ℝ) * y))
      = ∑ k ∈ Finset.range (n + 1),
          (c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y)) := by
    have hintegrand : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        eval y (shiftedLegendre n) / (1 - (a : ℝ) * y)
          = ∑ k ∈ Finset.range (n + 1), (c k : ℝ) * (y ^ k / (1 - (a : ℝ) * y)) := by
      intro y _
      rw [hc, eval_finset_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      simp only [eval_mul, eval_intCast, eval_pow, eval_X]
      ring
    rw [intervalIntegral.integral_congr hintegrand, intervalIntegral.integral_finset_sum hInt]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul]
  -- per-moment integrality
  have per_k : ∀ k ∈ Finset.range (n + 1), ∃ p q : ℤ,
      (Nat.lcmUpto n : ℝ) * (a : ℝ) ^ (n + 1) *
          ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y)))
        = (p : ℝ) + (q : ℝ) * L := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    obtain ⟨s, hs⟩ := mobius_moment_int_cleared a ha k
    obtain ⟨w, hw⟩ := lcmUpto_dvd_of_le hkn
    refine ⟨c k * (w : ℤ) * a ^ (n - k) * s,
            -(c k * (w : ℤ) * a ^ (n - k) * (Nat.lcmUpto k : ℤ)), ?_⟩
    have hlcmR : (Nat.lcmUpto n : ℝ) = (Nat.lcmUpto k : ℝ) * (w : ℝ) := by
      rw [hw]; push_cast; ring
    have hpowR : (a : ℝ) ^ (n + 1) = (a : ℝ) ^ (n - k) * (a : ℝ) ^ (k + 1) := by
      rw [← pow_add]; congr 1; omega
    calc (Nat.lcmUpto n : ℝ) * (a : ℝ) ^ (n + 1) *
            ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y)))
        = ((c k : ℝ) * (w : ℝ) * (a : ℝ) ^ (n - k)) *
            ((Nat.lcmUpto k : ℝ) * (a : ℝ) ^ (k + 1) *
              (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y))) := by
          rw [hlcmR, hpowR]; ring
      _ = ((c k : ℝ) * (w : ℝ) * (a : ℝ) ^ (n - k)) * ((s : ℝ) - (Nat.lcmUpto k : ℝ) * L) := by
          rw [hs]
      _ = _ := by push_cast; ring
  rw [hΛ, Finset.mul_sum]
  exact sum_int_linear (L := L)
    (fun k => (Nat.lcmUpto n : ℝ) * (a : ℝ) ^ (n + 1) *
      ((c k : ℝ) * (∫ y in (0 : ℝ)..1, y ^ k / (1 - (a : ℝ) * y)))) _ per_k

/-- **Linear form: `∫₀¹ P_n(y)/(1-a·y) dy = A + B·log(1-a)`** (leg 2 assembled).  Expanding
`P_n = ∑ c_k yᵏ` (integer coeffs, `shiftedLegendre_eq_int_poly`) and integrating termwise with the
moment closed form (`mobius_moment_closed`) gives `A = ∑ c_k r_k`, `B = −∑ c_k/aᵏ⁺¹`.  This is the
linear form in `1` and `log(1-a)` that, paired with the geometric remainder bound
(`legendre_mobius_remainder_bound`), produces an effective irrationality measure of `log(1-a)`. -/
theorem legendre_mobius_linear_form (a : ℝ) (ha : a < 1) (ha0 : a ≠ 0) (n : ℕ) :
    ∃ A B : ℝ, ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - a * y)
      = A + B * Real.log (1 - a) := by
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) 1, (0 : ℝ) < 1 - a * y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    rcases le_total a 0 with h | h
    · nlinarith [hy.1]
    · nlinarith [hy.2, mul_nonneg h (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y)]
  choose r hr using mobius_moment_closed a ha ha0
  obtain ⟨c, hc⟩ := shiftedLegendre_eq_int_poly n
  have hInt : ∀ k ∈ Finset.range (n + 1),
      IntervalIntegrable (fun y => (c k : ℝ) * (y ^ k / (1 - a * y)))
        MeasureTheory.volume 0 1 := by
    intro k _
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun y hy => ne_of_gt (hpos y hy)
  refine ⟨∑ k ∈ Finset.range (n + 1), (c k : ℝ) * r k,
          -∑ k ∈ Finset.range (n + 1), (c k : ℝ) / a ^ (k + 1), ?_⟩
  have hintegrand : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      eval y (shiftedLegendre n) / (1 - a * y)
        = ∑ k ∈ Finset.range (n + 1), (c k : ℝ) * (y ^ k / (1 - a * y)) := by
    intro y _
    rw [hc, eval_finset_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [eval_mul, eval_intCast, eval_pow, eval_X]
    ring
  rw [intervalIntegral.integral_congr hintegrand, intervalIntegral.integral_finset_sum hInt]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (∫ y in (0 : ℝ)..1, (c k : ℝ) * (y ^ k / (1 - a * y)))
        = (c k : ℝ) * r k - (c k : ℝ) / a ^ (k + 1) * Real.log (1 - a) := by
    intro k _
    rw [intervalIntegral.integral_const_mul, hr k]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- **Non-vanishing `∫₀¹ P_n(y)/(1-a·y) dy ≠ 0`** (leg 3's source-independent half).  Via the Padé
remainder form `= (-a)ⁿ·∫₀¹ (y(1-y))ⁿ/(1-a·y)^(n+1)`: the remainder integrand is strictly positive on
`(0,1)` (for `a<1`), so the integral is positive, and `(-a)ⁿ ≠ 0`.  This is the `Λ_n ≠ 0` needed so the
integer linear form `D_n·Λ_n = p_n + q_n·log(1-a)` is a *nonzero* integer combination — the last
ingredient (besides the source-gated choice of `a`-pair) of the effective measure. -/
theorem legendre_mobius_ne_zero (a : ℝ) (ha : a < 1) (ha0 : a ≠ 0) (n : ℕ) :
    ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - a * y) ≠ 0 := by
  have hden : ∀ y ∈ Set.uIcc (0 : ℝ) 1, (0 : ℝ) < 1 - a * y := by
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    rcases le_total a 0 with h | h
    · nlinarith [hy.1]
    · nlinarith [hy.2, mul_nonneg h (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y)]
  have hform : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - a * y))
      = ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * (1 / (1 - a * y)) := by
    apply intervalIntegral.integral_congr
    intro y _; dsimp only; rw [mul_one_div]
  rw [hform, legendre_mobius_integral a n ha]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha0))
  have hpos : 0 < ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - a * y) ^ (n + 1) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      exact fun y hy => pow_ne_zero _ (ne_of_gt (hden y hy))
    · intro y hy
      obtain ⟨hy0, hy1⟩ := hy
      have hd : (0 : ℝ) < 1 - a * y := hden y (by
        rw [Set.uIcc_of_le (by norm_num)]; exact ⟨le_of_lt hy0, le_of_lt hy1⟩)
      have hnum : 0 < y ^ n * (1 - y) ^ n :=
        mul_pos (pow_pos hy0 n) (pow_pos (by linarith) n)
      exact div_pos hnum (pow_pos hd _)
  exact ne_of_gt hpos

/-! ### Small integer linear forms in `log 2` (`a = -1`)

At `a = -1` the clearing power `a^(n+1) = ±1` is harmless, so the geometric remainder genuinely beats
the `lcm(1..n) ≤ 4ⁿ·o(1)` denominator: the sharp rational bound `y(1-y)/(1+y) ≤ 1/5` gives
`|Λ_n| ≤ (1/5)ⁿ`, and `4·(1/5) < 1` makes `lcm(1..n)·(1/5)ⁿ → 0`.  This yields, for each `n`, a
**nonzero** integer combination `P + Q·log 2` of size `≤ lcm(1..n)·(1/5)ⁿ` — enough for a standard
irrationality argument for `log 2` (the `a = -2`/`log 3` case needs Rhin's kernel, since there
`a^(n+1) = ±2^(n+1)` swamps the remainder — see `FRONT-A-PARADOXICAL.md`). -/

/-- **Sharp rational remainder bound at `a = -1`.**  `∫₀¹ yⁿ(1-y)ⁿ/(1+y)^(n+1) ≤ (1/5)ⁿ`, from the
pointwise `y(1-y)/(1+y) ≤ 1/5` on `[0,1]` (`0 ≤ 5y²-4y+1 = ((5y-2)²+1)/5`) and `1+y ≥ 1`. -/
theorem legendre_remainder_neg_one_bound (n : ℕ) :
    (∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1)) ≤ (1 / 5 : ℝ) ^ n := by
  have hbound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) ≤ (1 / 5 : ℝ) ^ n := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have h1y : (0 : ℝ) < 1 + y := by linarith
    rw [div_le_iff₀ (by positivity)]
    calc y ^ n * (1 - y) ^ n
        = (y * (1 - y)) ^ n := by rw [mul_pow]
      _ ≤ ((1 / 5 : ℝ) * (1 + y)) ^ n := by
          apply pow_le_pow_left₀ (by nlinarith)
          nlinarith [sq_nonneg (5 * y - 2)]
      _ = (1 / 5 : ℝ) ^ n * (1 + y) ^ n := by rw [mul_pow]
      _ ≤ (1 / 5 : ℝ) ^ n * (1 + y) ^ (n + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by linarith) (by omega)
  have hint : IntervalIntegrable (fun y => (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    obtain ⟨hy0, _⟩ := hy
    exact pow_ne_zero _ (by positivity)
  calc (∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1))
      ≤ ∫ _ in (0 : ℝ)..1, (1 / 5 : ℝ) ^ n :=
        intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const hbound
    _ = (1 / 5 : ℝ) ^ n := by simp

/-- **Small nonzero integer linear forms in `log 2` (assembled).**  For every `n`
there is a **nonzero** integer combination `P + Q·log 2` with
`|P + Q·log 2| ≤ lcm(1..n)·(1/5)ⁿ`.  Assembles the integer linear form
(`legendre_mobius_int_linear_form` at `a = -1`), non-vanishing (`legendre_mobius_ne_zero`), and the
sharp remainder bound (`legendre_remainder_neg_one_bound` via `legendre_mobius_integral`).  Since
`4·(1/5) < 1` while `lcm(1..n) ≤ 4ⁿ·e^{2√n·log n}` (`Gelfond.lcmUpto_le`), the bound tends to zero.
No coefficient-height estimate or corpus-wide novelty claim is made here. -/
theorem legendre_log_two_small (n : ℕ) :
    ∃ P Q : ℤ, ((P : ℝ) + (Q : ℝ) * Real.log 2 ≠ 0) ∧
      |(P : ℝ) + (Q : ℝ) * Real.log 2| ≤ (Nat.lcmUpto n : ℝ) * (1 / 5 : ℝ) ^ n := by
  set A : ℝ := ((-1 : ℤ) : ℝ) with hAdef
  have hAlt : A < 1 := by rw [hAdef]; norm_num
  have hA0 : A ≠ 0 := by rw [hAdef]; norm_num
  have hA2 : (1 : ℝ) - A = 2 := by rw [hAdef]; norm_num
  -- integer linear form at a = -1
  obtain ⟨P, Q, heq⟩ := legendre_mobius_int_linear_form (-1) (by norm_num) n
  rw [← hAdef, hA2] at heq
  refine ⟨P, Q, ?_, ?_⟩
  · -- non-vanishing: LHS = lcm·A^(n+1)·Λ ≠ 0
    rw [← heq]
    have hΛ := legendre_mobius_ne_zero A hAlt hA0 n
    have hlcm : (Nat.lcmUpto n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.lcmUpto_pos n).ne'
    exact mul_ne_zero (mul_ne_zero hlcm (pow_ne_zero _ hA0)) hΛ
  · -- size: |lcm·A^(n+1)·Λ| = lcm·|Λ| ≤ lcm·(1/5)^n
    rw [← heq]
    -- Λ = (-A)^n · R via the integral form
    have hform : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - A * y))
        = (-A) ^ n * ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - A * y) ^ (n + 1) := by
      have hcongr : (∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - A * y))
          = ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * (1 / (1 - A * y)) := by
        apply intervalIntegral.integral_congr; intro y _; dsimp only; rw [mul_one_div]
      rw [hcongr, legendre_mobius_integral A n hAlt]
    -- the remainder integral equals the (1+y) form
    have hden : ∀ y : ℝ, 1 - A * y = 1 + y := fun y => by rw [hAdef]; ring
    have hReq : (∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 - A * y) ^ (n + 1))
        = ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
      apply intervalIntegral.integral_congr; intro y _; dsimp only; rw [hden]
    have hRnn : 0 ≤ ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) / (1 + y) ^ (n + 1) := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro y hy; obtain ⟨hy0, hy1⟩ := hy; positivity
    have hRbd := legendre_remainder_neg_one_bound n
    -- |Λ| ≤ (1/5)^n
    have hΛabs : |∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) / (1 - A * y)| ≤ (1 / 5 : ℝ) ^ n := by
      rw [hform, hReq, abs_mul]
      have hone : |(-A) ^ n| = 1 := by rw [hAdef]; norm_num
      rw [hone, one_mul, abs_of_nonneg hRnn]
      exact hRbd
    -- assemble: |lcm·A^(n+1)·Λ| = lcm·|Λ| ≤ lcm·(1/5)^n
    rw [abs_mul, abs_mul, abs_pow]
    have hlcmabs : |(Nat.lcmUpto n : ℝ)| = (Nat.lcmUpto n : ℝ) := abs_of_nonneg (by positivity)
    have hAn1 : |A| ^ (n + 1) = 1 := by rw [hAdef]; norm_num
    rw [hlcmabs, hAn1, mul_one]
    exact mul_le_mul_of_nonneg_left hΛabs (by positivity)

end NormalNumbers.Legendre
