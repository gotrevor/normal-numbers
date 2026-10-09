/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The 3-adic linear form in two logarithms: interpolation-determinant ingredients (P3)

The target is `SparseIdentity.Literature.PadicTwoLogs` (Bugeaud–Laurent 1996, rational case):
`3^g ∣ tᵟa − b`, `tᵟa ≠ b` ⇒ `g ≤ C (1 + log(δ+1))² (1 + log max(|a|,|b|))`.  The proof is
Laurent's interpolation determinant `Δ`, squeezed between

* (a) an **analytic** lower bound for `v₃(Δ)`: after the Mahler expansion of the entries in
  `x = t − 1` (`3 ∣ x` after replacing `t` by a power) and `y = w − 1` (`3^g ∣ y`, `w` the ratio),
  every entry is `Σ_μ P(i, μ) Q(μ, λ)` with `x^{μ₁} y^{μ₂} ∣ P(i, μ)`.  Cauchy–Binet makes
  `v₃(Δ) ≥ min_{injective J} Σ_{μ ∈ J} (μ₁ + g μ₂)` (`dvd_det_mul`, `dvd_det_mul_monomial`), and
  the weight count `sum_weight_ge` turns the minimum into `≈ T(L − T²/g)`, i.e. order
  `L^{3/2} g^{1/2}`: two variables are essential (one variable gives only `L²/2`, which leads to a
  bound quadratic in `log M`, not enough for the chain of `SparseIdentity`).
* (b) a **Liouville** upper bound (`Δ` times a denominator is a nonzero integer);
* (c) a **zero lemma** making `Δ ≠ 0` (`Literature.LaurentZeroLemma`, cited);
* (d) parameters, (e) the multiplicatively dependent case by LTE.

This file holds (a) (proved) and the statement of (c).
-/

open Matrix Finset

namespace PadicTwoLogs

/-- **Cauchy–Binet valuation bound (proved).**  If the `μ`-th column of `P` is divisible by
`p ^ w μ`, then `det (P * Q)` is divisible by `p ^ m` for every `m` below all the weights
`Σ_x w (f x)` of injective column selections `f`.  Proof: expand the rows of `(P Q)ᵀ`
multilinearly; a non-injective selection gives an alternating map with a repeated argument. -/
theorem dvd_det_mul {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    [CommRing R] (p : R) (P : Matrix n ι R) (Q : Matrix ι n R) (w : ι → ℕ)
    (hP : ∀ i μ, p ^ w μ ∣ P i μ) (m : ℕ)
    (hm : ∀ f : n → ι, Function.Injective f → m ≤ ∑ x, w (f x)) :
    p ^ m ∣ (P * Q).det := by
  choose P' hP' using hP
  set v : ι → n → R := fun μ j => P' j μ
  have hrow : (P * Q)ᵀ = fun x => ∑ μ, (Q μ x * p ^ w μ) • v μ := by
    ext x j
    simp only [transpose_apply, mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, hP']
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [← det_transpose, hrow]
  change p ^ m ∣ detRowAlternating (fun x => ∑ μ, (Q μ x * p ^ w μ) • v μ)
  have hs := (detRowAlternating (R := R) (n := n)).toMultilinearMap.map_sum
    (fun (x : n) (μ : ι) => (Q μ x * p ^ w μ) • v μ)
  simp only [AlternatingMap.coe_multilinearMap] at hs
  rw [hs]
  refine Finset.dvd_sum fun f _ => ?_
  change p ^ m ∣ detRowAlternating (fun x => (Q (f x) x * p ^ w (f x)) • v (f x))
  rw [AlternatingMap.map_smul_univ, smul_eq_mul]
  by_cases hf : Function.Injective f
  · refine Dvd.dvd.mul_right ?_ _
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact Dvd.dvd.mul_left (pow_dvd_pow p (hm f hf)) _
  · have : detRowAlternating (fun x => v (f x)) = 0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ fun h =>
        hf (Function.Injective.of_comp (f := v) h)
    rw [this, mul_zero]; exact dvd_zero _

/-- **The two-variable weight count (proved).**  `L` distinct lattice points `(a, b)` have total
weight `Σ (a + g b) ≥ T (L − T(T/g + 1))` for every threshold `T`: fewer than `T (T/g + 1)` points
have weight `< T`.  With `T ≈ √(gL/2)` this is of order `L^{3/2} g^{1/2}`. -/
theorem sum_weight_ge {n : Type*} [Fintype n] {g : ℕ} (hg : 1 ≤ g) (T : ℕ) (f : n → ℕ × ℕ)
    (hf : Function.Injective f) :
    T * (Fintype.card n - T * (T / g + 1)) ≤ ∑ x, ((f x).1 + g * (f x).2) := by
  classical
  set S := univ.filter fun x => (f x).1 + g * (f x).2 < T
  have hS : S.card ≤ T * (T / g + 1) := by
    have : S.card ≤ (range T ×ˢ range (T / g + 1)).card := by
      refine card_le_card_of_injOn f (fun x hx => ?_) hf.injOn
      simp only [S, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
      refine ⟨by omega, ?_⟩
      have : g * (f x).2 < T := by omega
      have : (f x).2 ≤ T / g := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
      omega
    simpa using this
  have hc : Fintype.card n - T * (T / g + 1) ≤
      (univ.filter fun x => ¬ ((f x).1 + g * (f x).2 < T)).card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset n))
      fun x => (f x).1 + g * (f x).2 < T
    rw [card_univ] at this; change S.card + _ = _ at this; omega
  calc T * (Fintype.card n - T * (T / g + 1))
      ≤ T * (univ.filter fun x => ¬ ((f x).1 + g * (f x).2 < T)).card := Nat.mul_le_mul_left _ hc
    _ = ∑ x ∈ univ.filter (fun x => ¬ ((f x).1 + g * (f x).2 < T)), T := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ univ.filter (fun x => ¬ ((f x).1 + g * (f x).2 < T)), ((f x).1 + g * (f x).2) :=
        sum_le_sum fun x hx => by simp only [mem_filter] at hx; omega
    _ ≤ ∑ x, ((f x).1 + g * (f x).2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- **Analytic bound (a), algebraic core (proved).**  If the columns of `P` carry the monomials
`x^{μ₁} y^{μ₂}` with `p ∣ x` and `p^g ∣ y` (the Mahler expansion in `t − 1` and `w − 1`), then
`p^{T (L − T(T/g+1))} ∣ det (P Q)` for every `T`, where `L` is the size of the matrix. -/
theorem dvd_det_mul_monomial {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {ι : Finset (ℕ × ℕ)} (p x y : R) {g : ℕ} (hg : 1 ≤ g) (hx : p ∣ x) (hy : p ^ g ∣ y)
    (c : Matrix n ι R) (Q : Matrix ι n R) (T : ℕ) :
    p ^ (T * (Fintype.card n - T * (T / g + 1))) ∣
      ((Matrix.of fun i (μ : ι) => c i μ * x ^ (μ : ℕ × ℕ).1 * y ^ (μ : ℕ × ℕ).2) * Q).det := by
  classical
  refine dvd_det_mul p _ Q (fun μ => (μ : ℕ × ℕ).1 + g * (μ : ℕ × ℕ).2) (fun i μ => ?_) _
    fun f hf => sum_weight_ge hg T (fun a => (f a : ℕ × ℕ)) (Subtype.val_injective.comp hf)
  rw [of_apply, pow_add, pow_mul, mul_assoc]
  exact Dvd.dvd.mul_left (mul_dvd_mul (pow_dvd_pow_of_dvd hx _) (pow_dvd_pow_of_dvd hy _)) _

namespace Literature

/-- **Laurent's zero lemma for two logarithms (cited; transcription from memory, unchecked).**
M. Laurent, *Linear forms in two logarithms and interpolation determinants*, Acta Arith. 66
(1994); in the form of Laurent–Mignotte–Nesterenko, J. Number Theory 55 (1995), Lemme 1.
Specialised to rationals: `α₁, α₂ ∈ ℚ` nonzero and multiplicatively independent, `b₁, b₂ ∈ ℤ`.
If `Card{r b₂ + s b₁ : r < R₁, s < S₁} ≥ L` and `Card{α₁^r α₂^s : r < R₂, s < S₂} > (K−1)L`,
then no nonzero `P = Σ_{k<K, l<L} p_{kl} Xᵏ Yˡ` vanishes at all points
`(r b₂ + s b₁, α₁^r α₂^s)`, `r < R₁ + R₂ − 1`, `s < S₁ + S₂ − 1`.  This is what makes the
interpolation determinant nonzero.  Sources requested (ON-LINE-REQUEST.md, 2026-10-08); the
step most needing an expert check is the exact form of the two cardinality conditions. -/
def LaurentZeroLemma : Prop :=
  ∀ (α₁ α₂ : ℚ) (b₁ b₂ : ℤ) (K L R₁ R₂ S₁ S₂ : ℕ),
    α₁ ≠ 0 → α₂ ≠ 0 → (∀ u v : ℤ, α₁ ^ u * α₂ ^ v = 1 → u = 0 ∧ v = 0) →
    L ≤ ((range R₁ ×ˢ range S₁).image fun rs : ℕ × ℕ =>
      (rs.1 : ℤ) * b₂ + (rs.2 : ℤ) * b₁).card →
    (K - 1) * L < ((range R₂ ×ˢ range S₂).image fun rs : ℕ × ℕ =>
      α₁ ^ rs.1 * α₂ ^ rs.2).card →
    ∀ p : ℕ → ℕ → ℚ,
      (∀ r < R₁ + R₂ - 1, ∀ s < S₁ + S₂ - 1,
        ∑ k ∈ range K, ∑ l ∈ range L,
          p k l * ((r : ℚ) * b₂ + (s : ℚ) * b₁) ^ k * (α₁ ^ r * α₂ ^ s) ^ l = 0) →
      ∀ k < K, ∀ l < L, p k l = 0

end Literature

end PadicTwoLogs
