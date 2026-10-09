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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.Order.Field.Power
import Mathlib.RingTheory.Int.Basic

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
open scoped fwdDiff

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

/-! ### The finite Mahler expansion (binomial basis) -/

/-- `z C(z,i) = (i+1) C(z,i+1) + i C(z,i)`. -/
theorem mul_choose_eq (z i : ℕ) :
    z * z.choose i = (i + 1) * z.choose (i + 1) + i * z.choose i := by
  have h := Nat.choose_succ_right_eq z i
  rcases le_or_gt i z with hi | hi
  · rw [mul_comm (i + 1), h, mul_comm i, ← mul_add, Nat.sub_add_cancel hi, mul_comm]
  · rw [Nat.choose_eq_zero_of_lt hi, Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- `z ↦ z^k C(z,j)` is an integer combination of `C(z,i)`, `i ≤ k+j`. -/
theorem pow_mul_choose_expand (k j : ℕ) : ∃ c : ℕ → ℤ, (∀ i, k + j < i → c i = 0) ∧
    ∀ (z : ℕ) N, k + j < N →
      ((z : ℤ) ^ k * (z.choose j : ℤ)) = ∑ i ∈ range N, c i * (z.choose i : ℤ) := by
  induction k with
  | zero =>
    refine ⟨fun i => if i = j then 1 else 0, fun i hi => by simp; omega, fun z N hN => ?_⟩
    simp only [pow_zero, one_mul, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [show j < N by omega]
  | succ k ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    refine ⟨fun i => (i : ℤ) * c i + (i : ℤ) * (if i = 0 then 0 else c (i - 1)), fun i hi => ?_,
      fun z N hN => ?_⟩
    · have : i ≠ 0 := by omega
      simp [this, hc0 i (by omega), hc0 (i - 1) (by omega)]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [pow_succ, mul_comm _ (z : ℤ), mul_assoc, hc z M (by omega), mul_sum]
      have key : ∀ i, (z : ℤ) * (z.choose i : ℤ) =
          (i + 1) * (z.choose (i + 1) : ℤ) + i * (z.choose i : ℤ) := by
        intro i; exact_mod_cast mul_choose_eq z i
      have hA : ∑ i ∈ range (M + 1), (i : ℤ) * c i * (z.choose i : ℤ) =
          ∑ i ∈ range M, (i : ℤ) * c i * (z.choose i : ℤ) := by
        rw [sum_range_succ, hc0 M (by omega)]; simp
      have hB : ∑ i ∈ range (M + 1), (i : ℤ) * (if i = 0 then 0 else c (i - 1)) * (z.choose i : ℤ) =
          ∑ i ∈ range M, ((i : ℤ) + 1) * c i * (z.choose (i + 1) : ℤ) := by
        rw [sum_range_succ']; simp
      simp only [add_mul]
      rw [sum_add_distrib, hA, hB, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_left_comm, key]; ring

/-- The weight count with the `x`-degree shifted down by `c` (proved). -/
theorem sum_weight_ge_shift {n : Type*} [Fintype n] {g : ℕ} (hg : 1 ≤ g) (T c : ℕ)
    (f : n → ℕ × ℕ) (hf : Function.Injective f) :
    T * (Fintype.card n - (T + c) * (T / g + 1)) ≤ ∑ x, ((f x).1 - c + g * (f x).2) := by
  classical
  set S := univ.filter fun x => (f x).1 - c + g * (f x).2 < T
  have hS : S.card ≤ (T + c) * (T / g + 1) := by
    have : S.card ≤ (range (T + c) ×ˢ range (T / g + 1)).card := by
      refine card_le_card_of_injOn f (fun x hx => ?_) hf.injOn
      simp only [S, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
      refine ⟨by omega, ?_⟩
      have : g * (f x).2 < T := by omega
      have : (f x).2 ≤ T / g := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
      omega
    simpa using this
  have hc : Fintype.card n - (T + c) * (T / g + 1) ≤
      (univ.filter fun x => ¬ ((f x).1 - c + g * (f x).2 < T)).card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset n))
      fun x => (f x).1 - c + g * (f x).2 < T
    rw [card_univ] at this; change S.card + _ = _ at this; omega
  calc T * (Fintype.card n - (T + c) * (T / g + 1))
      ≤ T * (univ.filter fun x => ¬ ((f x).1 - c + g * (f x).2 < T)).card :=
        Nat.mul_le_mul_left _ hc
    _ = ∑ x ∈ univ.filter (fun x => ¬ ((f x).1 - c + g * (f x).2 < T)), T := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ univ.filter (fun x => ¬ ((f x).1 - c + g * (f x).2 < T)),
          ((f x).1 - c + g * (f x).2) :=
        sum_le_sum fun x hx => by simp only [mem_filter] at hx; omega
    _ ≤ ∑ x, ((f x).1 - c + g * (f x).2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- Truncated binomial expansion of `(1 + a)^z`, `z ≤ N`. -/
theorem one_add_pow_eq_sum {R : Type*} [CommRing R] (a : R) {z N : ℕ} (h : z ≤ N) :
    (1 + a) ^ z = ∑ j ∈ range (N + 1), (z.choose j : R) * a ^ j := by
  rw [add_comm, add_pow]
  refine (sum_subset (range_subset_range.2 (by omega)) fun j _ hj => ?_).trans
    (sum_congr rfl fun j _ => by ring)
  rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]; simp

/-- **Analytic bound (a) for the interpolation determinant (proved; finite Mahler expansion).**
Let `p ∣ t − 1` and `pᵍ ∣ w − 1` in a commutative ring.  The `KL × KL` interpolation determinant
with columns `(k, l)` and rows the points `(z_x, s_x)`, entry `z^k t^{lz} w^{ls}`, is divisible by
`p^{T(KL − (T+K)(T/g+1))}` for every `T`.  Proof: `t^{lz} = Σ_j C(z,j)(t^l−1)ʲ`,
`w^{ls} = Σ_n C(s,n)(w^l−1)ⁿ`, `z^k C(z,j) = Σ_{i ≤ k+j} c·C(z,i)` (`pow_mul_choose_expand`) give
`M = P·Q` with `P(x,(i,n)) = C(z,i)C(s,n)` and the row `(i,n)` of `Q` divisible by
`p^{(i−K) + gn}`; then `dvd_det_mul` and `sum_weight_ge_shift`.  In the application
`z = r + δs`, `t ≡ 1`, `w = b/(a tᵟ)` in `ℤ_[3]`, `v₃(w − 1) ≥ g`; the bound is of order
`(KL)^{3/2} g^{1/2}` when `K ≲ √(gL)`. -/
theorem dvd_det_interp_gen {R : Type*} [CommRing R] (φ : ℕ → ℕ → ℤ)
    (hφ : ∀ k j : ℕ, ∃ c : ℕ → ℤ, (∀ i, k + j < i → c i = 0) ∧ ∀ (z : ℕ) N, k + j < N →
      φ k z * (z.choose j : ℤ) = ∑ i ∈ range N, c i * (z.choose i : ℤ)) (p t w : R) {g : ℕ} (hg : 1 ≤ g)
    (ht : p ∣ t - 1) (hw : p ^ g ∣ w - 1) (K L : ℕ) (z s : Fin K × Fin L → ℕ) (T : ℕ) :
    p ^ (T * (K * L - (T + K) * (T / g + 1))) ∣
      (Matrix.of fun (x l : Fin K × Fin L) =>
        (φ l.1 (z x) : R) * t ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x)).det := by
  classical
  choose c hc0 hc using hφ
  set Z := univ.sup z
  set S := univ.sup s
  have hzZ : ∀ x, z x ≤ Z := fun x => le_sup (f := z) (mem_univ x)
  have hsS : ∀ x, s x ≤ S := fun x => le_sup (f := s) (mem_univ x)
  set ι := Fin (Z + K + 1) × Fin (S + 1)
  let X : ℕ → R := fun l => t ^ l - 1
  let Y : ℕ → R := fun l => w ^ l - 1
  let P : Matrix (Fin K × Fin L) ι R := Matrix.of fun x μ =>
    ((z x).choose μ.1 : R) * ((s x).choose μ.2 : R)
  let Q : Matrix ι (Fin K × Fin L) R := Matrix.of fun μ l =>
    ∑ j ∈ range (Z + 1), (c l.1 j μ.1 : R) * X l.2 ^ j * Y l.2 ^ (μ.2 : ℕ)
  have hPQ : (Matrix.of fun (x l : Fin K × Fin L) =>
      (φ l.1 (z x) : R) * t ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x)) = P * Q := by
    ext x l
    have ez : (φ l.1 (z x) : R) * t ^ ((l.2 : ℕ) * z x) =
        ∑ j ∈ range (Z + 1), X l.2 ^ j *
          ∑ i ∈ range (Z + K + 1), (c l.1 j i : R) * ((z x).choose i : R) := by
      rw [pow_mul, show t ^ (l.2 : ℕ) = 1 + X l.2 by simp [X], one_add_pow_eq_sum _ (hzZ x),
        mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have := congrArg (Int.cast : ℤ → R) (hc l.1 j (z x) (Z + K + 1)
        (by have := l.1.isLt; simp at hj; omega))
      push_cast at this
      rw [← this]; ring
    have ew : w ^ ((l.2 : ℕ) * s x) = ∑ n ∈ range (S + 1), ((s x).choose n : R) * Y l.2 ^ n := by
      rw [pow_mul, show w ^ (l.2 : ℕ) = 1 + Y l.2 by simp [Y], one_add_pow_eq_sum _ (hsS x)]
    rw [← Fin.sum_univ_eq_sum_range (fun n => ((s x).choose n : R) * Y l.2 ^ n)] at ew
    simp_rw [← Fin.sum_univ_eq_sum_range (fun i => (c _ _ i : R) * ((z x).choose i : R))] at ez
    rw [of_apply, ez, ew, mul_apply, Fintype.sum_prod_type]
    simp only [P, Q, of_apply]
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    simp_rw [sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, n]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ =>
      Finset.sum_congr rfl fun i _ => ?_
    ring
  have hdiv : ∀ l μ, p ^ ((μ : ι).1 - K + g * (μ : ι).2) ∣ Qᵀ l μ := by
    intro l μ
    simp only [transpose_apply, Q, of_apply]
    refine dvd_sum fun j _ => ?_
    by_cases hcj : c l.1 j μ.1 = 0
    · simp [hcj]
    have hle : (μ.1 : ℕ) - K ≤ j := by
      have := mt (hc0 l.1 j μ.1) hcj; have := l.1.isLt; omega
    have hX : p ∣ X l.2 := ht.trans (by simpa [X] using sub_dvd_pow_sub_pow t 1 (l.2 : ℕ))
    have hY : p ^ g ∣ Y l.2 := hw.trans (by simpa [Y] using sub_dvd_pow_sub_pow w 1 (l.2 : ℕ))
    rw [pow_add, pow_mul, mul_assoc]
    exact Dvd.dvd.mul_left (mul_dvd_mul ((pow_dvd_pow p hle).trans (pow_dvd_pow_of_dvd hX _))
      (pow_dvd_pow_of_dvd hY _)) _
  rw [hPQ, ← det_transpose, transpose_mul]
  refine dvd_det_mul p Qᵀ Pᵀ (fun μ => (μ : ι).1 - K + g * (μ : ι).2) hdiv _ fun f hf => ?_
  have := sum_weight_ge_shift hg T K (fun a => (((f a).1 : ℕ), ((f a).2 : ℕ)))
    (fun a b h => hf (by simp only [Prod.mk.injEq] at h; exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)))
  simpa using this


/-- The `z^k` instance of `dvd_det_interp_gen`. -/
theorem dvd_det_interp {R : Type*} [CommRing R] (p t w : R) {g : ℕ} (hg : 1 ≤ g)
    (ht : p ∣ t - 1) (hw : p ^ g ∣ w - 1) (K L : ℕ) (z s : Fin K × Fin L → ℕ) (T : ℕ) :
    p ^ (T * (K * L - (T + K) * (T / g + 1))) ∣
      (Matrix.of fun (x l : Fin K × Fin L) =>
        (z x : R) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x)).det := by
  have := dvd_det_interp_gen (fun k z => (z : ℤ) ^ k) pow_mul_choose_expand p t w hg ht hw K L z s T
  simpa using this

/-- **(b), homogenised integer form (proved).**  With `V = a tᵟ`, `3 ∤ V`, `3 ∣ t − 1`,
`3ᵍ ∣ b − V`, the integer determinant `det[z^k t^{lz} b^{ls} V^{(L−1−l)s}]` (the rows of the
interpolation determinant for `w = b/V` scaled by `V^{(L−1)s}`) is divisible by
`3^{T(KL − (T+K)(T/g+1))}`.  Proof: in `ZMod 3^m` the scaling is a unit and `dvd_det_interp`
applies with `p^m = 0`. -/
theorem three_pow_dvd_det_hom (t a b : ℤ) (δ : ℕ) {g : ℕ} (hg : 1 ≤ g) (ht : 3 ∣ t - 1)
    (hV : ¬ (3 : ℤ) ∣ a * t ^ δ) (hab : (3 : ℤ) ^ g ∣ b - a * t ^ δ) (K L : ℕ)
    (z s : Fin K × Fin L → ℕ) (T : ℕ) :
    (3 : ℤ) ^ (T * (K * L - (T + K) * (T / g + 1))) ∣
      (Matrix.of fun (x l : Fin K × Fin L) => (z x : ℤ) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) *
        b ^ ((l.2 : ℕ) * s x) * (a * t ^ δ) ^ ((L - 1 - l.2) * s x)).det := by
  set m := T * (K * L - (T + K) * (T / g + 1))
  have h3 : ((3 ^ m : ℕ) : ℤ) = 3 ^ m := by push_cast; rfl
  rw [← h3, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set R := ZMod (3 ^ m)
  rw [show ((det _ : ℤ) : R) = (Int.castRingHom R) (det _) from rfl, RingHom.map_det]
  set V := a * t ^ δ
  have hcop : V.natAbs.Coprime (3 ^ m) := Nat.Coprime.pow_right m
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by
      intro h; exact hV (Int.natCast_dvd.2 h))).symm
  have hu : IsUnit (V : R) := by
    have := (ZMod.isUnit_iff_coprime _ _).2 hcop
    rcases Int.natAbs_eq V with h | h <;> rw [h]
    · rw [Int.cast_natCast]; exact this
    · rw [Int.cast_neg, Int.cast_natCast]; exact this.neg
  set u := hu.unit
  set w : R := (b : R) * ↑u⁻¹
  have hVu : (V : R) * ↑u⁻¹ = 1 := by simp [u]
  have hmat : (Int.castRingHom R).mapMatrix (Matrix.of fun (x l : Fin K × Fin L) =>
      (z x : ℤ) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) * b ^ ((l.2 : ℕ) * s x) *
        V ^ ((L - 1 - l.2) * s x)) = Matrix.of fun x l => (V : R) ^ ((L - 1) * s x) *
      ((z x : R) ^ (l.1 : ℕ) * (t : R) ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x)) := by
    ext x l
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, of_apply]
    have hl : (L - 1) * s x = (L - 1 - l.2) * s x + (l.2 : ℕ) * s x := by
      rw [← add_mul]; congr 1; have := l.2.isLt; omega
    have : (V : R) ^ ((l.2 : ℕ) * s x) * (↑u⁻¹ : R) ^ ((l.2 : ℕ) * s x) = 1 := by
      rw [← mul_pow, hVu, one_pow]
    simp only [map_mul, map_pow, eq_intCast, Int.cast_natCast]
    rw [hl, pow_add]
    simp only [w, mul_pow]
    linear_combination (-1 : R) * (↑(z x) ^ (l.1 : ℕ) * (t : R) ^ ((l.2 : ℕ) * z x) * (b : R) ^ ((l.2 : ℕ) * s x) *
      (V : R) ^ ((L - 1 - l.2) * s x)) * this
  have hcol := det_mul_column (fun x : Fin K × Fin L => (V : R) ^ ((L - 1) * s x))
    (Matrix.of fun (x l : Fin K × Fin L) =>
      (z x : R) ^ (l.1 : ℕ) * (t : R) ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x))
  simp only [of_apply] at hcol
  rw [hmat, hcol]
  have ht' : (3 : R) ∣ (t : R) - 1 := by
    simpa using (Int.castRingHom R).map_dvd ht
  have hw' : (3 : R) ^ g ∣ w - 1 := by
    obtain ⟨c, hc⟩ := hab
    have h : (3 : R) ^ g ∣ (b : R) - (V : R) := ⟨c, by
      have := congrArg (Int.castRingHom R) hc
      simp only [map_mul, map_pow, map_sub, eq_intCast, map_ofNat] at this; exact this⟩
    have : w - 1 = ((b : R) - (V : R)) * ↑u⁻¹ := by
      simp only [w]; rw [sub_mul, hVu]
    rw [this]; exact h.mul_right _
  obtain ⟨c, hc⟩ := dvd_det_interp (3 : R) (t : R) w hg ht' hw' K L z s T
  have h0 : (3 : R) ^ m = 0 := by
    rw [show (3 : R) ^ m = ((3 ^ m : ℕ) : R) by push_cast; rfl, ZMod.natCast_self]
  rw [hc, h0, zero_mul, mul_zero]

/-- **(b) Liouville (proved).**  If the homogenised determinant is nonzero and its entries are
bounded by `X`, then `3^{T(KL − (T+K)(T/g+1))} ≤ (KL)! X^{KL}`.  With (c) supplying `Δ ≠ 0` this
is the two-sided squeeze; (d) chooses `K, L, T` and the points. -/
theorem three_pow_le_of_det_ne_zero (t a b : ℤ) (δ : ℕ) {g : ℕ} (hg : 1 ≤ g) (ht : 3 ∣ t - 1)
    (hV : ¬ (3 : ℤ) ∣ a * t ^ δ) (hab : (3 : ℤ) ^ g ∣ b - a * t ^ δ) (K L : ℕ)
    (z s : Fin K × Fin L → ℕ) (T : ℕ) (X : ℤ)
    (hX : ∀ x l : Fin K × Fin L, |(z x : ℤ) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) *
        b ^ ((l.2 : ℕ) * s x) * (a * t ^ δ) ^ ((L - 1 - l.2) * s x)| ≤ X)
    (hΔ : (Matrix.of fun (x l : Fin K × Fin L) => (z x : ℤ) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) *
        b ^ ((l.2 : ℕ) * s x) * (a * t ^ δ) ^ ((L - 1 - l.2) * s x)).det ≠ 0) :
    (3 : ℤ) ^ (T * (K * L - (T + K) * (T / g + 1))) ≤ (K * L).factorial * X ^ (K * L) := by
  have h := three_pow_dvd_det_hom t a b δ hg ht hV hab K L z s T
  refine (Int.le_of_dvd (abs_pos.2 hΔ) ((dvd_abs _ _).2 h)).trans ?_
  have := Matrix.det_le (A := Matrix.of fun (x l : Fin K × Fin L) => (z x : ℤ) ^ (l.1 : ℕ) *
      t ^ ((l.2 : ℕ) * z x) * b ^ ((l.2 : ℕ) * s x) * (a * t ^ δ) ^ ((L - 1 - l.2) * s x))
    (abv := AbsoluteValue.abs) (fun x l => by simpa using hX x l)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-! ### Binomial columns and the grid form -/

section Newton
open Polynomial

/-- The polynomial `C(X,k)` over `ℚ`. -/
noncomputable def chooseP (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

theorem chooseP_eval (k n : ℕ) : (chooseP k).eval (n : ℚ) = (n.choose k : ℚ) := by
  rw [chooseP, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

theorem chooseP_natDegree (k : ℕ) : (chooseP k).natDegree ≤ k :=
  (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree ℚ k).le

/-- **Binomial-basis expansion of `C(z,k) C(z,j)` (proved).**  Integer coefficients, supported on
`i ≤ k + j`: Gregory–Newton (`shift_eq_sum_fwdDiff_iter`) with coefficients `Δⁱ f(0) ∈ ℤ`, which
vanish for `i > k+j` because `f` agrees on `ℕ` with a rational polynomial of degree `≤ k+j`.  This
lets the interpolation determinant use the columns `C(z,k)` (height `K log(ez/K)`, no `log K!`
loss), as in Bugeaud–Laurent's `b' = δ/B`. -/
theorem choose_mul_choose_expand (k j : ℕ) : ∃ c : ℕ → ℤ, (∀ i, k + j < i → c i = 0) ∧
    ∀ (z : ℕ) N, k + j < N →
      ((z.choose k : ℤ) * (z.choose j : ℤ)) = ∑ i ∈ range N, c i * (z.choose i : ℤ) := by
  set f : ℕ → ℤ := fun z => (z.choose k : ℤ) * (z.choose j : ℤ)
  set P := chooseP k * chooseP j
  have hP : ∀ n : ℕ, P.eval (n : ℚ) = (f n : ℚ) := by
    intro n; simp [P, f, chooseP_eval]
  have hdeg : P.natDegree ≤ k + j :=
    natDegree_mul_le.trans (add_le_add (chooseP_natDegree k) (chooseP_natDegree j))
  have hc0 : ∀ i, k + j < i → (fwdDiff 1)^[i] f 0 = 0 := by
    intro i hi
    have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) f i 0
    have h2 := fwdDiff_iter_eq_sum_shift (h := (1 : ℚ)) P.eval i 0
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)] at h2
    have : (((fwdDiff 1)^[i] f 0 : ℤ) : ℚ) = 0 := by
      rw [h1, Pi.zero_apply] at *
      push_cast
      rw [h2]
      refine sum_congr rfl fun m _ => ?_
      simp only [zsmul_eq_mul, smul_eq_mul, zero_add, nsmul_eq_mul, mul_one, Nat.cast_id]
      push_cast
      rw [hP]
    exact_mod_cast this
  refine ⟨fun i => (fwdDiff 1)^[i] f 0, hc0, fun z N hN => ?_⟩
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f z 0
  simp only [zero_add, smul_eq_mul, mul_one] at h
  change f z = _
  rw [h]
  have e1 : ∑ i ∈ range (z + 1), z.choose i • (fwdDiff 1)^[i] f 0 =
      ∑ i ∈ range (max (z + 1) N), z.choose i • (fwdDiff 1)^[i] f 0 :=
    sum_subset (range_subset_range.2 (le_max_left _ _)) fun i _ hi => by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hi), zero_smul]
  have e2 : ∑ i ∈ range N, (fwdDiff 1)^[i] f 0 * (z.choose i : ℤ) =
      ∑ i ∈ range (max (z + 1) N), (fwdDiff 1)^[i] f 0 * (z.choose i : ℤ) :=
    sum_subset (range_subset_range.2 (le_max_right _ _)) fun i _ hi => by
      rw [hc0 i (by simp at hi; omega), zero_mul]
  rw [e1, e2]
  refine sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, mul_comm]

end Newton

/-- **(b), homogenised form over the grid `(r, s)` (proved).**  For any column family `φ` with a
binomial-basis expansion (`z^k`: `pow_mul_choose_expand`; `C(z,k)`: `choose_mul_choose_expand`),
`3 ∣ t − 1`, `3 ∤ a`, `3ᵍ ∣ b − a tᵟ`: the integer determinant with entries
`φ_k(r + δs) · t^{lr} b^{ls} a^{(L−1−l)s}` (heights `log t` and `log max(|a|,|b|)` only) is divisible
by `3^{T(KL − (T+K)(T/g+1))}`.  In `ZMod 3^m`: the row scaling `a^{(L−1)s}` is a unit and the
entries become `φ_k(z) t^{lz} w^{ls}`, `z = r + δs`, `w = b/(a tᵟ)`, so `dvd_det_interp_gen`
applies with `3^m = 0`. -/
theorem three_pow_dvd_det_rs (φ : ℕ → ℕ → ℤ)
    (hφ : ∀ k j : ℕ, ∃ c : ℕ → ℤ, (∀ i, k + j < i → c i = 0) ∧ ∀ (z : ℕ) N, k + j < N →
      φ k z * (z.choose j : ℤ) = ∑ i ∈ range N, c i * (z.choose i : ℤ))
    (t a b : ℤ) (δ : ℕ) {g : ℕ} (hg : 1 ≤ g) (ht : 3 ∣ t - 1) (ha : ¬ (3 : ℤ) ∣ a)
    (hab : (3 : ℤ) ^ g ∣ b - a * t ^ δ) (K L : ℕ) (r s : Fin K × Fin L → ℕ) (T : ℕ) :
    (3 : ℤ) ^ (T * (K * L - (T + K) * (T / g + 1))) ∣
      (Matrix.of fun (x l : Fin K × Fin L) => φ l.1 (r x + δ * s x) * t ^ ((l.2 : ℕ) * r x) *
        b ^ ((l.2 : ℕ) * s x) * a ^ ((L - 1 - l.2) * s x)).det := by
  set m := T * (K * L - (T + K) * (T / g + 1))
  have h3 : ((3 ^ m : ℕ) : ℤ) = 3 ^ m := by push_cast; rfl
  rw [← h3, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set R := ZMod (3 ^ m)
  rw [show ((det _ : ℤ) : R) = (Int.castRingHom R) (det _) from rfl, RingHom.map_det]
  have hunit : ∀ y : ℤ, ¬ (3 : ℤ) ∣ y → IsUnit (y : R) := by
    intro y hy
    have hcop : y.natAbs.Coprime (3 ^ m) := Nat.Coprime.pow_right m
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by
        intro h; exact hy (Int.natCast_dvd.2 h))).symm
    have := (ZMod.isUnit_iff_coprime _ _).2 hcop
    rcases Int.natAbs_eq y with h | h <;> rw [h]
    · rw [Int.cast_natCast]; exact this
    · rw [Int.cast_neg, Int.cast_natCast]; exact this.neg
  have ht3 : ¬ (3 : ℤ) ∣ t := fun h => by
    have := (Int.dvd_sub h ht); simp at this
  obtain ⟨ua, hua⟩ := hunit a ha
  obtain ⟨ut, hut⟩ := hunit t ht3
  have hia : (a : R) * ↑ua⁻¹ = 1 := by rw [← hua]; simp
  have hit : (t : R) * ↑ut⁻¹ = 1 := by rw [← hut]; simp
  set w : R := (b : R) * ↑ua⁻¹ * (↑ut⁻¹ : R) ^ δ
  have hmat : (Int.castRingHom R).mapMatrix (Matrix.of fun (x l : Fin K × Fin L) =>
      φ l.1 (r x + δ * s x) * t ^ ((l.2 : ℕ) * r x) * b ^ ((l.2 : ℕ) * s x) *
        a ^ ((L - 1 - l.2) * s x)) = Matrix.of fun x l => (a : R) ^ ((L - 1) * s x) *
      ((φ l.1 (r x + δ * s x) : R) * (t : R) ^ ((l.2 : ℕ) * (r x + δ * s x)) *
        w ^ ((l.2 : ℕ) * s x)) := by
    ext x l
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, of_apply, of_apply]
    simp only [map_mul, map_pow, eq_intCast]
    have hl : (L - 1) * s x = (L - 1 - l.2) * s x + (l.2 : ℕ) * s x := by
      rw [← add_mul]; congr 1; have := l.2.isLt; omega
    have e1 : (a : R) ^ ((l.2 : ℕ) * s x) * (↑ua⁻¹ : R) ^ ((l.2 : ℕ) * s x) = 1 := by
      rw [← mul_pow, hia, one_pow]
    have e2 : (t : R) ^ (δ * ((l.2 : ℕ) * s x)) * (↑ut⁻¹ : R) ^ (δ * ((l.2 : ℕ) * s x)) = 1 := by
      rw [← mul_pow, hit, one_pow]
    rw [hl, pow_add, mul_add, pow_add, show (l.2 : ℕ) * (δ * s x) = δ * ((l.2 : ℕ) * s x) by ring]
    simp only [w, mul_pow, ← pow_mul]
    rw [show δ * ((l.2 : ℕ) * s x) = δ * ((l.2 : ℕ) * s x) from rfl]
    linear_combination (-1 : R) * ((φ l.1 (r x + δ * s x) : R) * (t : R) ^ ((l.2 : ℕ) * r x) *
      (b : R) ^ ((l.2 : ℕ) * s x) * (a : R) ^ ((L - 1 - l.2) * s x)) *
      ((t : R) ^ (δ * ((l.2 : ℕ) * s x)) * (↑ut⁻¹ : R) ^ (δ * ((l.2 : ℕ) * s x)) * e1 + e2)
  have hcol := det_mul_column (fun x : Fin K × Fin L => (a : R) ^ ((L - 1) * s x))
    (Matrix.of fun (x l : Fin K × Fin L) =>
      (φ l.1 (r x + δ * s x) : R) * (t : R) ^ ((l.2 : ℕ) * (r x + δ * s x)) * w ^ ((l.2 : ℕ) * s x))
  simp only [of_apply] at hcol
  rw [hmat, hcol]
  have ht' : (3 : R) ∣ (t : R) - 1 := by
    simpa using (Int.castRingHom R).map_dvd ht
  have hw' : (3 : R) ^ g ∣ w - 1 := by
    obtain ⟨c, hc⟩ := hab
    have h : (3 : R) ^ g ∣ (b : R) - (a : R) * (t : R) ^ δ := ⟨c, by
      have := congrArg (Int.castRingHom R) hc
      simp only [map_mul, map_pow, map_sub, eq_intCast, map_ofNat] at this; exact this⟩
    have : w - 1 = ((b : R) - (a : R) * (t : R) ^ δ) * (↑ua⁻¹ * (↑ut⁻¹ : R) ^ δ) := by
      simp only [w]
      have : (a : R) * (t : R) ^ δ * (↑ua⁻¹ * (↑ut⁻¹ : R) ^ δ) = 1 := by
        rw [show (a : R) * (t : R) ^ δ * (↑ua⁻¹ * (↑ut⁻¹ : R) ^ δ) =
          ((a : R) * ↑ua⁻¹) * ((t : R) * ↑ut⁻¹) ^ δ by ring, hia, hit]; simp
      linear_combination this
    rw [this]; exact h.mul_right _
  obtain ⟨c, hc⟩ := dvd_det_interp_gen φ hφ (3 : R) (t : R) w hg ht' hw' K L
    (fun x => r x + δ * s x) s T
  have h0 : (3 : R) ^ m = 0 := by
    rw [show (3 : R) ^ m = ((3 ^ m : ℕ) : R) by push_cast; rfl, ZMod.natCast_self]
  rw [hc, h0, zero_mul, mul_zero]

/-- Cauchy–Binet as a sum over column selections (proved). -/
theorem det_mul_eq_sum {n ι R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : Matrix n ι R) (Q : Matrix ι n R) :
    (P * Q).det = ∑ f : n → ι, (∏ x, Q (f x) x) * (P.submatrix id f).det := by
  have hrow : (P * Q)ᵀ = fun x => ∑ μ, Q μ x • fun j => P j μ := by
    ext x j
    simp only [transpose_apply, mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [← det_transpose, hrow]
  change detRowAlternating (fun x => ∑ μ, Q μ x • fun j => P j μ) = _
  have hs := (detRowAlternating (R := R) (n := n)).toMultilinearMap.map_sum
    (fun (x : n) (μ : ι) => Q μ x • fun j => P j μ)
  simp only [AlternatingMap.coe_multilinearMap] at hs
  rw [hs]
  refine Finset.sum_congr rfl fun f _ => ?_
  change detRowAlternating (fun x => Q (f x) x • fun j => P j (f x)) = _
  rw [AlternatingMap.map_smul_univ, smul_eq_mul]
  congr 1
  rw [← det_transpose]; rfl

/-- **(c), linear-algebra half (proved).**  A rational matrix with trivial kernel has a nonzero
maximal minor: `det(AᵀA) ≠ 0` (positive definite) and `det_mul_eq_sum`. -/
theorem exists_det_submatrix_ne_zero {G n : Type*} [Fintype G] [DecidableEq G] [Fintype n]
    [DecidableEq n] (A : Matrix G n ℚ) (hA : ∀ v, A *ᵥ v = 0 → v = 0) :
    ∃ f : n → G, (A.submatrix f id).det ≠ 0 := by
  have hdet : (Aᵀ * A).det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 h
    apply hv0 (hA v _)
    have : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
      rw [← mulVec_mulVec] at hv
      have := congrArg (v ⬝ᵥ ·) hv
      simp only [dotProduct_zero] at this
      rw [dotProduct_mulVec, vecMul_transpose] at this
      exact this
    exact dotProduct_self_eq_zero.1 this
  rw [det_mul_eq_sum] at hdet
  by_contra hcon
  push Not at hcon
  apply hdet
  refine Finset.sum_eq_zero fun f _ => ?_
  have : (Aᵀ.submatrix id f) = (A.submatrix f id)ᵀ := rfl
  rw [this, det_transpose, hcon f, mul_zero]

namespace Literature

/-- **Laurent's zero lemma for two logarithms (cited; transcription from memory, corrected once).**
M. Laurent, Acta Arith. 66 (1994); Laurent–Mignotte–Nesterenko, J. Number Theory 55 (1995),
Lemme 1, specialised to rationals: `α₁, α₂ ∈ ℚ` nonzero, multiplicatively independent, `b₁, b₂ ∈ ℤ`.
If `Card{α₁^r α₂^s : r < R₁, s < S₁} ≥ L` and `Card{r b₂ + s b₁ : r < R₂, s < S₂} > (K−1)L`, then a
polynomial `P(X, Y) = Σ_{l<L} q_l(X) Yˡ` with `deg q_l < K` vanishing at all
`(r b₂ + s b₁, α₁^r α₂^s)`, `r < R₁ + R₂ − 1`, `s < S₁ + S₂ − 1`, is zero.  Stated basis-free
(families `q_l`), so it applies to the binomial columns `C(X, k)` directly.  Sanity: `L = 1` is
"`< K` roots", `K = 1` is "`< L` roots in `Y`".  Confidence in the transcription: moderate (the first
attempt swapped the conditions and was refuted, `not_laurentZeroLemmaMisread`); sources requested
in ON-LINE-REQUEST.md.  Numerical evidence (2026-10-09, `scripts/zero_lemma_probe.py`, exact
rational rank): 1419 random admissible instances (`K, L, Rᵢ, Sᵢ ≤ 4`, `|bᵢ| ≤ 3`, five independent
pairs) all have full-rank evaluation matrix; control: the swapped (misread) conditions fail on 19 of
1535 instances. -/
def LaurentZeroLemma : Prop :=
  ∀ (α₁ α₂ : ℚ) (b₁ b₂ : ℤ) (K L R₁ R₂ S₁ S₂ : ℕ),
    α₁ ≠ 0 → α₂ ≠ 0 → (∀ u v : ℤ, α₁ ^ u * α₂ ^ v = 1 → u = 0 ∧ v = 0) →
    L ≤ ((range R₁ ×ˢ range S₁).image fun rs : ℕ × ℕ => α₁ ^ rs.1 * α₂ ^ rs.2).card →
    (K - 1) * L < ((range R₂ ×ˢ range S₂).image fun rs : ℕ × ℕ =>
      (rs.1 : ℤ) * b₂ + (rs.2 : ℤ) * b₁).card →
    ∀ q : ℕ → Polynomial ℚ, (∀ l < L, (q l).natDegree < K) →
      (∀ r < R₁ + R₂ - 1, ∀ s < S₁ + S₂ - 1,
        ∑ l ∈ range L, (q l).eval ((r : ℚ) * b₂ + (s : ℚ) * b₁) * (α₁ ^ r * α₂ ^ s) ^ l = 0) →
      ∀ l < L, q l = 0

/-- **REFUTED transcription (kept as a record; see `not_laurentZeroLemmaMisread`).**  The first
transcription of Laurent's zero lemma, with the two cardinality conditions swapped.  It is false:
`b₁ = b₂ = 0` makes every `X`-value `0`, and `P = X` vanishes on the grid.  Corrected statement:
`LaurentZeroLemma`.  Original docstring follows.
M. Laurent, *Linear forms in two logarithms and interpolation determinants*, Acta Arith. 66
(1994); in the form of Laurent–Mignotte–Nesterenko, J. Number Theory 55 (1995), Lemme 1.
Specialised to rationals: `α₁, α₂ ∈ ℚ` nonzero and multiplicatively independent, `b₁, b₂ ∈ ℤ`.
If `Card{r b₂ + s b₁ : r < R₁, s < S₁} ≥ L` and `Card{α₁^r α₂^s : r < R₂, s < S₂} > (K−1)L`,
then no nonzero `P = Σ_{k<K, l<L} p_{kl} Xᵏ Yˡ` vanishes at all points
`(r b₂ + s b₁, α₁^r α₂^s)`, `r < R₁ + R₂ − 1`, `s < S₁ + S₂ − 1`.  This is what makes the
interpolation determinant nonzero.  Sources requested (ON-LINE-REQUEST.md, 2026-10-08); the
step most needing an expert check is the exact form of the two cardinality conditions. -/
def LaurentZeroLemmaMisread : Prop :=
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

/-- `2` and `3` are multiplicatively independent. -/
theorem two_three_indep (u v : ℤ) (h : (2 : ℚ) ^ u * (3 : ℚ) ^ v = 1) : u = 0 ∧ v = 0 := by
  have h2 := congrArg (padicValRat 2) h
  have h3 := congrArg (padicValRat 3) h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [padicValRat.mul (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (by norm_num)), padicValRat.zpow, padicValRat.zpow] at h2 h3
  have a : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) (by norm_num)
  have b : padicValRat 3 (3 : ℚ) = 1 := by simpa using padicValRat.self (p := 3) (by norm_num)
  have c : padicValRat 2 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]; simp
  have d : padicValRat 3 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]; simp
  simp [a, b, c, d] at h2 h3
  exact ⟨h2, h3⟩

/-- **The swapped transcription is false (proved).** -/
theorem not_laurentZeroLemmaMisread : ¬ LaurentZeroLemmaMisread := by
  intro H
  have := H 2 3 0 0 2 1 1 2 1 2 (by norm_num) (by norm_num) two_three_indep (by decide)
    (Finset.one_lt_card.2 ⟨1, Finset.mem_image.2 ⟨(0, 0), by simp, by norm_num⟩,
      2, Finset.mem_image.2 ⟨(1, 0), by simp, by norm_num⟩, by norm_num⟩)
    (fun k l => if k = 1 then 1 else 0) (fun r _ s _ => by simp) 1
    (by norm_num) 0 (by norm_num)
  simp at this

end Literature


section ZeroWiring
open Polynomial

/-- Triangularity of the binomial basis: `Σ_{k<K} v_k C(n,k) = 0` for all `n` forces `v = 0`. -/
theorem choose_coeffs_eq_zero (K : ℕ) (v : ℕ → ℚ)
    (h : ∀ n : ℕ, ∑ k ∈ range K, v k * (n.choose k : ℚ) = 0) : ∀ k < K, v k = 0 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ j ih =>
    have hj := h j
    rw [← sum_range_add_sum_Ico _ (show j + 1 ≤ K by omega), sum_range_succ] at hj
    have e1 : ∑ k ∈ range j, v k * (j.choose k : ℚ) = 0 :=
      sum_eq_zero fun k hk' => by rw [ih k (by simpa using hk') (by simp at hk'; omega), zero_mul]
    have e2 : ∑ k ∈ Ico (j + 1) K, v k * (j.choose k : ℚ) = 0 :=
      sum_eq_zero fun k hk' => by
        rw [Nat.choose_eq_zero_of_lt (by simp at hk'; omega)]; simp
    rw [e1, e2, Nat.choose_self] at hj; simpa using hj

/-- **(c), zero-lemma half (proved from the cited `LaurentZeroLemma`).**  The grid matrix with
rows `(r, s)`, `r < R₁+R₂−1`, `s < S₁+S₂−1`, and columns `C(r+δs, k)·(α₁^r α₂^s)^l` has trivial
kernel: a kernel vector gives `q_l = Σ_k v_{kl} C(X,k)` vanishing on the grid. -/
theorem grid_ker_trivial (hZ : Literature.LaurentZeroLemma) (α₁ α₂ : ℚ) (δ : ℕ)
    (h1 : α₁ ≠ 0) (h2 : α₂ ≠ 0) (hind : ∀ u v : ℤ, α₁ ^ u * α₂ ^ v = 1 → u = 0 ∧ v = 0)
    (K L R₁ R₂ S₁ S₂ : ℕ)
    (hc1 : L ≤ ((range R₁ ×ˢ range S₁).image fun rs : ℕ × ℕ => α₁ ^ rs.1 * α₂ ^ rs.2).card)
    (hc2 : (K - 1) * L < ((range R₂ ×ˢ range S₂).image fun rs : ℕ × ℕ =>
      (rs.1 : ℤ) * 1 + (rs.2 : ℤ) * δ).card)
    (v : Fin K × Fin L → ℚ)
    (hv : (Matrix.of fun (x : Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1)) (kl : Fin K × Fin L) =>
      (((x.1 : ℕ) + δ * x.2).choose kl.1 : ℚ) * (α₁ ^ (x.1 : ℕ) * α₂ ^ (x.2 : ℕ)) ^ (kl.2 : ℕ))
        *ᵥ v = 0) : v = 0 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · funext x; exact x.1.elim0
  set q : ℕ → ℚ[X] := fun l => if hl : l < L then ∑ k : Fin K, C (v (k, ⟨l, hl⟩)) * chooseP k
    else 0
  have hdeg : ∀ l < L, (q l).natDegree < K := by
    intro l hl
    simp only [q, hl, dite_true]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := K - 1) fun k _ => ?_) (by omega)
    exact (natDegree_C_mul_le _ _).trans ((chooseP_natDegree k).trans (by omega))
  have hvan : ∀ r < R₁ + R₂ - 1, ∀ s < S₁ + S₂ - 1,
      ∑ l ∈ range L, (q l).eval ((r : ℚ) * ((1 : ℤ) : ℚ) + (s : ℚ) * ((δ : ℤ) : ℚ)) *
        (α₁ ^ r * α₂ ^ s) ^ l = 0 := by
    intro r hr s hs
    have := congrFun hv (⟨r, hr⟩, ⟨s, hs⟩)
    simp only [mulVec, dotProduct, of_apply, Pi.zero_apply, Fintype.sum_prod_type] at this
    rw [← this, Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [q, l.isLt, dite_true, eval_finsetSum, eval_mul, eval_C, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := chooseP_eval k (r + δ * s)
    push_cast at this ⊢
    rw [show (r : ℚ) * 1 + s * δ = r + δ * s by ring, this]
    ring
  have hq := hZ α₁ α₂ δ 1 K L R₁ R₂ S₁ S₂ h1 h2 hind hc1 hc2 q hdeg hvan
  funext ⟨k, l⟩
  have hql := hq l l.isLt
  simp only [q, l.isLt, dite_true] at hql
  have := choose_coeffs_eq_zero K (fun k => if hk : k < K then v (⟨k, hk⟩, l) else 0)
    (fun n => by
      have := congrArg (eval (n : ℚ)) hql
      simp only [eval_finsetSum, eval_mul, eval_C, chooseP_eval, eval_zero] at this
      rw [← this, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [k.isLt]) k k.isLt
  simpa [k.isLt] using this


/-- **(c) (proved from `LaurentZeroLemma`).**  Some `KL` grid points make the integer
homogenised determinant (binomial columns, entries `C(r+δs,k) t^{lr} b^{ls} a^{(L−1−l)s}`) nonzero. -/
theorem exists_det_hom_ne_zero (hZ : Literature.LaurentZeroLemma) (t a b : ℤ) (δ : ℕ)
    (ht : t ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hind : ∀ u v : ℤ, (t : ℚ) ^ u * ((b : ℚ) / a) ^ v = 1 → u = 0 ∧ v = 0)
    (K L R₁ R₂ S₁ S₂ : ℕ)
    (hc1 : L ≤ ((range R₁ ×ˢ range S₁).image fun rs : ℕ × ℕ =>
      (t : ℚ) ^ rs.1 * ((b : ℚ) / a) ^ rs.2).card)
    (hc2 : (K - 1) * L < ((range R₂ ×ˢ range S₂).image fun rs : ℕ × ℕ =>
      (rs.1 : ℤ) * 1 + (rs.2 : ℤ) * δ).card) :
    ∃ r s : Fin K × Fin L → ℕ, (∀ x, r x < R₁ + R₂ - 1) ∧ (∀ x, s x < S₁ + S₂ - 1) ∧
      (Matrix.of fun (x l : Fin K × Fin L) => (((r x + δ * s x).choose l.1 : ℕ) : ℤ) *
        t ^ ((l.2 : ℕ) * r x) * b ^ ((l.2 : ℕ) * s x) * a ^ ((L - 1 - l.2) * s x)).det ≠ 0 := by
  have hβ : (b : ℚ) / a ≠ 0 := div_ne_zero (by exact_mod_cast hb) (by exact_mod_cast ha)
  obtain ⟨f, hf⟩ := exists_det_submatrix_ne_zero _
    (grid_ker_trivial hZ (t : ℚ) ((b : ℚ) / a) δ (by exact_mod_cast ht) hβ hind K L R₁ R₂ S₁ S₂
      hc1 hc2)
  refine ⟨fun x => ((f x).1 : ℕ), fun x => ((f x).2 : ℕ), fun x => (f x).1.isLt,
    fun x => (f x).2.isLt, fun h => hf ?_⟩
  have hcast := congrArg (Int.cast : ℤ → ℚ) h
  rw [Int.cast_zero, Int.cast_det] at hcast
  have hmat : (Matrix.of fun (x l : Fin K × Fin L) => ((((((f x).1 : ℕ) + δ * ((f x).2 : ℕ)).choose
        l.1 : ℕ) : ℤ) * t ^ ((l.2 : ℕ) * ((f x).1 : ℕ)) * b ^ ((l.2 : ℕ) * ((f x).2 : ℕ)) *
        a ^ ((L - 1 - l.2) * ((f x).2 : ℕ)) : ℤ)).map (Int.cast : ℤ → ℚ) =
      Matrix.of fun x l => ((a : ℚ) ^ ((L - 1) * ((f x).2 : ℕ))) *
        ((Matrix.of fun (x : Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1)) (kl : Fin K × Fin L) =>
          (((x.1 : ℕ) + δ * x.2).choose kl.1 : ℚ) * ((t : ℚ) ^ (x.1 : ℕ) * ((b : ℚ) / a) ^ (x.2 : ℕ))
            ^ (kl.2 : ℕ)).submatrix f id) x l := by
    ext x l
    simp only [map_apply, of_apply, submatrix_apply, id]
    have hl : (L - 1) * ((f x).2 : ℕ) = (L - 1 - l.2) * ((f x).2 : ℕ) + (l.2 : ℕ) * ((f x).2 : ℕ) := by
      rw [← add_mul]; congr 1; have := l.2.isLt; omega
    rw [hl, pow_add]
    push_cast
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    simp only [mul_pow, div_pow, ← pow_mul]
    rw [mul_comm ((f x).1 : ℕ), mul_comm ((f x).2 : ℕ)]
    field_simp
  have hcol := det_mul_column (fun x : Fin K × Fin L => (a : ℚ) ^ ((L - 1) * ((f x).2 : ℕ)))
    ((Matrix.of fun (x : Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1)) (kl : Fin K × Fin L) =>
      (((x.1 : ℕ) + δ * x.2).choose kl.1 : ℚ) * ((t : ℚ) ^ (x.1 : ℕ) * ((b : ℚ) / a) ^ (x.2 : ℕ))
        ^ (kl.2 : ℕ)).submatrix f id)
  rw [hmat, hcol] at hcast
  exact (mul_eq_zero.1 hcast).resolve_left
    (Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (by exact_mod_cast ha))

/-- Entry bound for the homogenised grid determinant. -/
theorem entry_bound (t a b : ℤ) (M : ℕ) (hM1 : 1 ≤ M) (ht : 1 ≤ t) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (L Z P S : ℕ) (hZ : 1 ≤ Z) (z k l r s K : ℕ) (hz : z ≤ Z) (hk : k ≤ K) (hl : l < L)
    (hr : r ≤ P) (hs : s ≤ S) :
    |(((z.choose k : ℕ) : ℤ)) * t ^ (l * r) * b ^ (l * s) * a ^ ((L - 1 - l) * s)| ≤
      (Z : ℤ) ^ K * t ^ (L * P) * (M : ℤ) ^ (L * S) := by
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_of_pos (by omega : (0:ℤ) < t)]
  have h1 : |(((z.choose k : ℕ) : ℤ))| ≤ (Z : ℤ) ^ K := by
    rw [Nat.abs_cast]
    exact_mod_cast ((Nat.choose_le_pow z k).trans (Nat.pow_le_pow_left hz k)).trans
      (Nat.pow_le_pow_right hZ hk)
  have h2 : t ^ (l * r) ≤ t ^ (L * P) := pow_le_pow_right₀ ht (Nat.mul_le_mul (by omega) hr)
  have h3 : |b| ^ (l * s) * |a| ^ ((L - 1 - l) * s) ≤ (M : ℤ) ^ (L * S) := by
    calc |b| ^ (l * s) * |a| ^ ((L - 1 - l) * s) ≤ (M : ℤ) ^ (l * s) * (M : ℤ) ^ ((L - 1 - l) * s) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hb _) (pow_le_pow_left₀ (abs_nonneg _) ha _)
            (by positivity) (by positivity)
      _ = (M : ℤ) ^ ((L - 1) * s) := by rw [← pow_add, ← add_mul]; congr 2; omega
      _ ≤ (M : ℤ) ^ (L * S) := pow_le_pow_right₀ (by exact_mod_cast hM1)
          (Nat.mul_le_mul (by omega) hs)
  calc _ = |(((z.choose k : ℕ) : ℤ))| * t ^ (l * r) * (|b| ^ (l * s) * |a| ^ ((L - 1 - l) * s)) := by ring
    _ ≤ (Z : ℤ) ^ K * t ^ (L * P) * (M : ℤ) ^ (L * S) := by
      gcongr

/-- **(d), the squeeze (proved from `LaurentZeroLemma`).**  Independent case, `3 ∣ t − 1`,
`3 ∤ a`, heights `≤ M`.  For any parameters with `R₂ ≤ δ` (the values `r + δs` are distinct),
`(K−1)L < R₂S₂` (zero-lemma count; the other count uses `R₁ = L`, `S₁ = 1`) and the numeric
inequality `(KL)!·X^{KL} < 3^{T(KL−T−K)}`, `X = (L+R₂+δS₂)^K t^{L(L+R₂)} M^{LS₂}`: `g ≤ T`.  (If
`g > T`, then `T/g = 0`, the grid minor is nonzero, `3^{T(KL−T−K)}` divides it, and Liouville
contradicts `hnum`.)  Left for the assembly: choose the parameters (`L ≈ C(1+log δ)`,
`K ≈ C'L log t log M`, `R₂ ≈ K/log t`, `S₂ ≈ K/log M`, `T = ⌊KL/3⌋`) and prove `hnum`. -/
theorem g_le_of_squeeze (hZ : Literature.LaurentZeroLemma) (t a b : ℤ) (δ g : ℕ)
    (ht1 : 3 ∣ t - 1) (ht2 : 2 ≤ t) (ha : ¬ (3 : ℤ) ∣ a) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (M : ℕ) (hM1 : 1 ≤ M) (haM : |a| ≤ M) (hbM : |b| ≤ M)
    (hind : ∀ u v : ℤ, (t : ℚ) ^ u * ((b : ℚ) / a) ^ v = 1 → u = 0 ∧ v = 0)
    (hab : (3 : ℤ) ^ g ∣ b - a * t ^ δ) (K L R₂ S₂ T : ℕ) (hδ : R₂ ≤ δ)
    (hcount : (K - 1) * L < R₂ * S₂)
    (hnum : ((K * L).factorial : ℤ) * (((L + R₂ + δ * S₂ : ℕ) : ℤ) ^ K * t ^ (L * (L + R₂)) *
      (M : ℤ) ^ (L * S₂)) ^ (K * L) < 3 ^ (T * (K * L - (T + K)))) : g ≤ T := by
  by_contra hgT
  push Not at hgT
  have hg : 1 ≤ g := by omega
  have hR₂ : 1 ≤ R₂ := by
    rcases Nat.eq_zero_or_pos R₂ with h | h
    · rw [h] at hcount; simp at hcount
    · exact h
  have hβ : (b : ℚ) / a ≠ 0 := div_ne_zero (by exact_mod_cast hb0) (by exact_mod_cast ha0)
  have hc1 : L ≤ ((range L ×ˢ range 1).image fun rs : ℕ × ℕ =>
      (t : ℚ) ^ rs.1 * ((b : ℚ) / a) ^ rs.2).card := by
    rw [card_image_of_injOn]
    · simp
    · intro x hx y hy hxy
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hx hy
      have hx2 : x.2 = 0 := by omega
      have hy2 : y.2 = 0 := by omega
      simp only [hx2, hy2, pow_zero, mul_one] at hxy
      have ht' : (1 : ℚ) < t := by exact_mod_cast (by omega : (1 : ℤ) < t)
      exact Prod.ext ((pow_right_strictMono₀ ht').injective hxy) (by rw [hx2, hy2])
  have hc2 : (K - 1) * L < ((range R₂ ×ˢ range S₂).image fun rs : ℕ × ℕ =>
      (rs.1 : ℤ) * 1 + (rs.2 : ℤ) * δ).card := by
    rw [card_image_of_injOn]
    · simpa using hcount
    · intro x hx y hy hxy
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio] at hx hy
      simp only at hxy
      have h : x.1 + x.2 * δ = y.1 + y.2 * δ := by exact_mod_cast (by linarith : _)
      have hm := congrArg (· % δ) h
      simp only [Nat.add_mul_mod_self_right] at hm
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      have : x.2 * δ = y.2 * δ := by omega
      exact Prod.ext hm (Nat.eq_of_mul_eq_mul_right (by omega) this)
  obtain ⟨r, s, hr, hs, hdet⟩ := exists_det_hom_ne_zero hZ t a b δ (by omega) ha0 hb0 hind
    K L L R₂ 1 S₂ hc1 hc2
  have hdvd := three_pow_dvd_det_rs (fun k z => ((z.choose k : ℕ) : ℤ)) choose_mul_choose_expand
    t a b δ hg ht1 ha hab K L r s T
  rw [Nat.div_eq_of_lt hgT, zero_add, mul_one] at hdvd
  have hle := Int.le_of_dvd (abs_pos.2 hdet) ((dvd_abs _ _).2 hdvd)
  have hdl := Matrix.det_le (abv := AbsoluteValue.abs) (A := Matrix.of fun (x l : Fin K × Fin L) =>
      (((r x + δ * s x).choose l.1 : ℕ) : ℤ) * t ^ ((l.2 : ℕ) * r x) * b ^ ((l.2 : ℕ) * s x) *
        a ^ ((L - 1 - l.2) * s x))
    (x := ((L + R₂ + δ * S₂ : ℕ) : ℤ) ^ K * t ^ (L * (L + R₂)) * (M : ℤ) ^ (L * S₂))
    (fun x l => by
      have := hr x; have := hs x
      simpa using entry_bound t a b M hM1 (by omega) haM hbM L (L + R₂ + δ * S₂) (L + R₂) S₂
        (by omega) (r x + δ * s x) l.1 l.2 (r x) (s x) K
        (by have := Nat.mul_le_mul_left δ (show s x ≤ S₂ by omega); omega) l.1.isLt.le l.2.isLt (by omega) (by omega))
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul] at hdl
  have := hle.trans hdl
  linarith

theorem mul32_le_two_pow (x : ℕ) (hx : 8 ≤ x) : 32 * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem hm_aux (y K : ℕ) (hK : 64 * K ≤ 32 * y) (_hy : 8 ≤ y) :
    4 * y * (32 * y) ≤ 32 * y / 3 * (32 * y - (32 * y / 3 + K)) := by
  set T := 32 * y / 3
  set U := 32 * y - (T + K)
  have h1 : 30 * y ≤ 3 * T := by omega
  have h2 : 125 * y ≤ 6 * U := by omega
  have := Nat.mul_le_mul h1 h2
  nlinarith

/-- **(d), the numeric inequality (proved).**  With `t < 2^τ`, `δ < 2^D`, `M < 2^A` and
`E = D+τ+20`, `L = 64E`, `R₂ = 64AL`, `S₂ = 64τL`, `K = 4096τAL`, `T = ⌊KL/3⌋`, and `R₂ ≤ δ`:
`(KL)!·X^{KL} < 3^{T(KL−T−K)}` (every factor of `X` is `≤ 2^{KL/32}`, so the left side is
`≤ 2^{(KL)²/8}`).  These are the `hnum` of `g_le_of_squeeze`. -/
theorem numeric_core (t δ M τ D A E L R₂ S₂ K : ℕ) (ht : t < 2 ^ τ) (hδ2 : δ < 2 ^ D)
    (hM : M < 2 ^ A) (hτ : 1 ≤ τ) (hA : 1 ≤ A) (hEd : E = D + τ + 20) (hLd : L = 64 * E)
    (hRd : R₂ = 64 * A * L) (hSd : S₂ = 64 * τ * L) (hKd : K = 4096 * τ * A * L)
    (hδ : R₂ ≤ δ) :
    (K * L).factorial * ((L + R₂ + δ * S₂) ^ K * t ^ (L * (L + R₂)) * M ^ (L * S₂)) ^ (K * L) <
      3 ^ (K * L / 3 * (K * L - (K * L / 3 + K))) := by
  set x := 128 * τ * A * L * L with hx
  have hN : K * L = 32 * x := by rw [hKd, hx]; ring
  have hL : 64 ≤ L := by omega
  have hE : E < 2 ^ E := Nat.lt_two_pow_self
  -- (1) Z ≤ 2^(2E)
  have hZ : L + R₂ + δ * S₂ ≤ 2 ^ (2 * E) := by
    have hR : 64 * A * L ≤ δ := hRd ▸ hδ
    have hAL : 1 ≤ A * L := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hδ1 : 1 ≤ δ := by have : 64 * A * L = 64 * (A * L) := by ring
                           omega
    have h1 : L + R₂ + δ * S₂ ≤ 66 * δ * τ * L := by
      have a1 : L ≤ δ * τ * L := Nat.le_mul_of_pos_left _ (by positivity)
      have a2 : δ ≤ δ * τ * L := by
        calc δ = δ * 1 * 1 := by ring
          _ ≤ δ * τ * L := by (gcongr; omega)
      rw [hRd, hSd]
      have : δ * (64 * τ * L) = 64 * (δ * τ * L) := by ring
      have : 66 * δ * τ * L = 66 * (δ * τ * L) := by ring
      omega
    have h2 : 66 * δ * τ * L ≤ 2 ^ 13 * (2 ^ D * 2 ^ τ * 2 ^ E) := by
      have hτ2 : τ < 2 ^ τ := Nat.lt_two_pow_self
      have hL2 : L ≤ 64 * 2 ^ E := by omega
      calc 66 * δ * τ * L ≤ 66 * 2 ^ D * 2 ^ τ * (64 * 2 ^ E) :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 66 hδ2.le) hτ2.le) hL2
        _ = 4224 * (2 ^ D * 2 ^ τ * 2 ^ E) := by ring
        _ ≤ 2 ^ 13 * (2 ^ D * 2 ^ τ * 2 ^ E) := Nat.mul_le_mul_right _ (by norm_num)
    calc _ ≤ 2 ^ 13 * (2 ^ D * 2 ^ τ * 2 ^ E) := h1.trans h2
      _ = 2 ^ (13 + D + τ + E) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (2 * E) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hXZ : (L + R₂ + δ * S₂) ^ K ≤ 2 ^ x := by
    calc _ ≤ (2 ^ (2 * E)) ^ K := Nat.pow_le_pow_left hZ _
      _ = 2 ^ x := by rw [← pow_mul]; congr 1; rw [hx, hKd, hLd]; ring
  have hXt : t ^ (L * (L + R₂)) ≤ 2 ^ x := by
    calc _ ≤ (2 ^ τ) ^ (L * (L + R₂)) := Nat.pow_le_pow_left ht.le _
      _ = 2 ^ (τ * (L * (L + R₂))) := by rw [← pow_mul]
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by rw [hx, hRd]; nlinarith)
  have hXM : M ^ (L * S₂) ≤ 2 ^ x := by
    calc _ ≤ (2 ^ A) ^ (L * S₂) := Nat.pow_le_pow_left hM.le _
      _ = 2 ^ (A * (L * S₂)) := by rw [← pow_mul]
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by rw [hx, hSd]; nlinarith)
  have hNx : K * L ≤ 2 ^ x := by
    rw [hN]; exact mul32_le_two_pow x (by rw [hx]; nlinarith)
  have hNX : K * L * ((L + R₂ + δ * S₂) ^ K * t ^ (L * (L + R₂)) * M ^ (L * S₂)) ≤ 2 ^ (4 * x) := by
    calc _ ≤ 2 ^ x * (2 ^ x * 2 ^ x * 2 ^ x) := by gcongr
      _ = 2 ^ (4 * x) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  have hm : 4 * x * (K * L) ≤ K * L / 3 * (K * L - (K * L / 3 + K)) := by
    have hK : 64 * K ≤ K * L := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hL
    rw [hN] at hK ⊢
    exact hm_aux x K hK (by rw [hx]; nlinarith)
  calc (K * L).factorial * ((L + R₂ + δ * S₂) ^ K * t ^ (L * (L + R₂)) * M ^ (L * S₂)) ^ (K * L)
      ≤ (K * L) ^ (K * L) * ((L + R₂ + δ * S₂) ^ K * t ^ (L * (L + R₂)) * M ^ (L * S₂)) ^ (K * L) :=
        Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ = (K * L * ((L + R₂ + δ * S₂) ^ K * t ^ (L * (L + R₂)) * M ^ (L * S₂))) ^ (K * L) := by
        rw [mul_pow (K * L)]
    _ ≤ (2 ^ (4 * x)) ^ (K * L) := Nat.pow_le_pow_left hNX _
    _ = 2 ^ (4 * x * (K * L)) := by rw [← pow_mul]
    _ ≤ 2 ^ (K * L / 3 * (K * L - (K * L / 3 + K))) := Nat.pow_le_pow_right (by norm_num) hm
    _ < 3 ^ (K * L / 3 * (K * L - (K * L / 3 + K))) := by
        apply Nat.pow_lt_pow_left (by norm_num)
        have hx8 : 8 ≤ x := by rw [hx]; nlinarith
        have h0 : 0 < x := by omega
        have : 0 < 4 * x * (K * L) := by rw [hN]; positivity
        omega

/-- **The 3-adic two-log bound, independent case (proved from `LaurentZeroLemma`).**  For `t ≥ 2`,
`3 ∣ t − 1`, `3 ∤ a`, `t` and `b/a` multiplicatively independent, `|a|, |b| ≤ M`, `tᵟa ≠ b`,
`3ᵍ ∣ tᵟa − b`: `g ≤ 2²⁴ τ A (D + τ + 20)²` with `τ, A, D` the binary lengths of `t, M, δ`.
Large `δ`: `g_le_of_squeeze` + `numeric_core`; small `δ` (`δ < 4096 A E`): `3ᵍ ≤ 2M tᵟ`. -/
theorem g_le_indep (hZ : Literature.LaurentZeroLemma) (t : ℕ) (a b : ℤ) (δ g : ℕ)
    (ht1 : (3 : ℤ) ∣ (t : ℤ) - 1) (ht2 : 2 ≤ t) (ha : ¬ (3 : ℤ) ∣ a) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (M : ℕ) (hM1 : 1 ≤ M) (haM : |a| ≤ M) (hbM : |b| ≤ M)
    (hind : ∀ u v : ℤ, ((t : ℤ) : ℚ) ^ u * ((b : ℚ) / a) ^ v = 1 → u = 0 ∧ v = 0)
    (hne : (t : ℤ) ^ δ * a ≠ b) (hab : (3 : ℤ) ^ g ∣ (t : ℤ) ^ δ * a - b) :
    g ≤ 2 ^ 24 * (Nat.log 2 t + 1) * (Nat.log 2 M + 1) *
      (Nat.log 2 δ + 1 + (Nat.log 2 t + 1) + 20) ^ 2 := by
  set τ := Nat.log 2 t + 1
  set A := Nat.log 2 M + 1
  set D := Nat.log 2 δ + 1
  set E := D + τ + 20
  have ht : t < 2 ^ τ := Nat.lt_pow_succ_log_self (by norm_num) t
  have hM : M < 2 ^ A := Nat.lt_pow_succ_log_self (by norm_num) M
  have hδ2 : δ < 2 ^ D := Nat.lt_pow_succ_log_self (by norm_num) δ
  have hτ : 1 ≤ τ := by omega
  have hA : 1 ≤ A := by omega
  have hab' : (3 : ℤ) ^ g ∣ b - a * (t : ℤ) ^ δ := by
    rw [show b - a * (t : ℤ) ^ δ = -((t : ℤ) ^ δ * a - b) by ring]; exact (dvd_neg).2 hab
  rcases le_or_gt (64 * A * (64 * E)) δ with hδ | hδ
  · have h := g_le_of_squeeze hZ t a b δ g ht1 (by exact_mod_cast ht2) ha ha0 hb0 M hM1 haM hbM
      hind hab' (4096 * τ * A * (64 * E)) (64 * E) (64 * A * (64 * E)) (64 * τ * (64 * E))
      (4096 * τ * A * (64 * E) * (64 * E) / 3) hδ (by
        have : 1 ≤ 64 * E := by omega
        have : (4096 * τ * A * (64 * E) - 1) * (64 * E) < 4096 * τ * A * (64 * E) * (64 * E) := by
          have : 1 ≤ 4096 * τ * A * (64 * E) := Nat.one_le_iff_ne_zero.2 (by positivity)
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        calc _ < _ := this
          _ = 64 * A * (64 * E) * (64 * τ * (64 * E)) := by ring)
      (by
        have := numeric_core t δ M τ D A E (64 * E) (64 * A * (64 * E)) (64 * τ * (64 * E))
          (4096 * τ * A * (64 * E)) ht hδ2 hM hτ hA rfl rfl rfl rfl rfl hδ
        exact_mod_cast this)
    calc g ≤ _ := h
      _ ≤ 4096 * τ * A * (64 * E) * (64 * E) := Nat.div_le_self _ _
      _ = 2 ^ 24 * τ * A * E ^ 2 := by ring
  · -- small δ: Liouville directly
    have hne' : (t : ℤ) ^ δ * a - b ≠ 0 := sub_ne_zero.2 hne
    have h1 := Int.le_of_dvd (abs_pos.2 hne') ((dvd_abs _ _).2 hab)
    have h2 : |(t : ℤ) ^ δ * a - b| ≤ 2 * M * (t : ℤ) ^ δ := by
      have ht0 : (0 : ℤ) ≤ (t : ℤ) ^ δ := by positivity
      have ht1' : (1 : ℤ) ≤ (t : ℤ) ^ δ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ t))
      calc |(t : ℤ) ^ δ * a - b| ≤ |(t : ℤ) ^ δ * a| + |b| := abs_sub _ _
        _ = (t : ℤ) ^ δ * |a| + |b| := by rw [abs_mul, abs_of_nonneg ht0]
        _ ≤ (t : ℤ) ^ δ * M + M * (t : ℤ) ^ δ := by gcongr; nlinarith
        _ = 2 * M * (t : ℤ) ^ δ := by ring
    have h3 : (3 : ℤ) ^ g ≤ 2 ^ (1 + A + τ * δ) := by
      refine h1.trans (h2.trans ?_)
      rw [pow_add, pow_add, pow_mul]
      have : (M : ℤ) ≤ 2 ^ A := by exact_mod_cast hM.le
      have : ((t : ℕ) : ℤ) ^ δ ≤ ((2 : ℤ) ^ τ) ^ δ := by
        gcongr; exact_mod_cast ht.le
      nlinarith [pow_nonneg (show (0:ℤ) ≤ 2 by norm_num) A, pow_nonneg (show (0:ℤ) ≤ (t:ℤ) by positivity) δ]
    have h4 : (2 : ℤ) ^ g ≤ 2 ^ (1 + A + τ * δ) :=
      (pow_le_pow_left₀ (by norm_num) (by norm_num) g).trans h3
    have h5 : g ≤ 1 + A + τ * δ := (pow_le_pow_iff_right₀ (by norm_num)).1 h4
    have h6 : τ * δ ≤ τ * (64 * A * (64 * E)) := Nat.mul_le_mul_left _ hδ.le
    have h7 : τ * (64 * A * (64 * E)) = 4096 * (τ * A * E) := by ring
    have hE1 : 1 ≤ E := by omega
    have h8 : τ * A * E ≤ τ * A * E ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have h9 : A ≤ τ * A * E := by
      calc A = 1 * A * 1 := by ring
        _ ≤ τ * A * E := by gcongr
    have h10 : 2 ^ 24 * τ * A * E ^ 2 = 2 ^ 24 * (τ * A * E ^ 2) := by ring
    have h11 : 1 ≤ τ * A * E := le_trans hA h9
    omega

/-! ### Reductions: the dependent case -/


/-- LTE bound: `3 ∣ t − 1`, `3ᵍ ∣ tⁿ − 1` ⇒ `g ≤ log₃ t + log₃ n`. -/
theorem le_of_three_pow_dvd_pow_sub_one (t n g : ℕ) (ht : 2 ≤ t) (ht1 : 3 ∣ t - 1) (hn : 1 ≤ n)
    (h : 3 ^ g ∣ t ^ n - 1) : g ≤ Nat.log 3 t + Nat.log 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpos : t ^ n - 1 ≠ 0 := by
    have : 2 ≤ t ^ n := le_trans ht (Nat.le_self_pow (by omega) t)
    omega
  have hv := (padicValNat_dvd_iff_le hpos).1 h
  have hlte := padicValNat.pow_sub_pow (p := 3) (x := t) (y := 1) (by decide) (by omega) ht1
    (by intro h3; have := Nat.dvd_sub h3 ht1; rw [Nat.sub_sub_self (by omega)] at this
        norm_num at this) (n := n) (by omega)
  rw [one_pow] at hlte
  have h1 : padicValNat 3 (t - 1) ≤ Nat.log 3 t := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    exact (Nat.le_of_dvd (by omega) pow_padicValNat_dvd).trans (by omega)
  have h2 : padicValNat 3 n ≤ Nat.log 3 n :=
    Nat.le_log_of_pow_le (by norm_num) (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
  omega



/-- `v_p(b) ≤ log₂|b|`. -/
theorem padicValRat_int_le_log (p : ℕ) [Fact p.Prime] (b : ℤ) (hb : b ≠ 0) :
    padicValRat p (b : ℚ) ≤ Nat.log 2 b.natAbs := by
  rw [padicValRat.of_int, padicValInt]
  have hp2 := (Fact.out : p.Prime).two_le
  have : p ^ padicValNat p b.natAbs ≤ b.natAbs :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have : 2 ^ padicValNat p b.natAbs ≤ b.natAbs :=
    le_trans (Nat.pow_le_pow_left hp2 _) this
  exact_mod_cast Nat.le_log_of_pow_le (by norm_num) this

/-- **Dependent case, small relation (proved).**  If `t ≥ 2` and `β = b/a` are multiplicatively
dependent, then `β^{2e} = t^{2f}` with `1 ≤ e ≤ log₂ t`, `|f| ≤ log₂|a| + log₂|b|`: take a prime
`p ∣ t`, `e = v_p(t)`, `f = v_p(β)`; `x = t^{−2f}β^{2e} > 0` satisfies `x^v = 1`. -/
theorem small_relation (t : ℕ) (ht : 2 ≤ t) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (u v : ℤ)
    (huv : ¬ (u = 0 ∧ v = 0)) (hrel : (t : ℚ) ^ u * ((b : ℚ) / a) ^ v = 1) :
    ∃ e : ℕ, ∃ f : ℤ, 1 ≤ e ∧ e ≤ Nat.log 2 t ∧
      |f| ≤ Nat.log 2 a.natAbs + Nat.log 2 b.natAbs ∧ ((b : ℚ) / a) ^ (2 * e) = (t : ℚ) ^ (2 * f) := by
  set p := t.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  set β : ℚ := (b : ℚ) / a
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hβ : β ≠ 0 := div_ne_zero hb' ha'
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  set e := padicValNat p t
  set f := padicValRat p β
  have he1 : 1 ≤ e := one_le_padicValNat_of_dvd (by omega) (Nat.minFac_dvd t)
  have he2 : e ≤ Nat.log 2 t := by
    have : p ^ e ≤ t := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hp.two_le _) this)
  have hf : |f| ≤ Nat.log 2 a.natAbs + Nat.log 2 b.natAbs := by
    have hfd : f = padicValRat p (b : ℚ) - padicValRat p (a : ℚ) := padicValRat.div hb' ha'
    have h1 := padicValRat_int_le_log p b hb
    have h2 := padicValRat_int_le_log p a ha
    have h3 : 0 ≤ padicValRat p (b : ℚ) := by rw [padicValRat.of_int]; positivity
    have h4 : 0 ≤ padicValRat p (a : ℚ) := by rw [padicValRat.of_int]; positivity
    rw [abs_le]; constructor <;> omega
  have hval : u * e + v * f = 0 := by
    have := congrArg (padicValRat p) hrel
    rw [padicValRat.mul (zpow_ne_zero _ ht') (zpow_ne_zero _ hβ), padicValRat.zpow,
      padicValRat.zpow, padicValRat.one] at this
    simpa [e, padicValRat.of_nat] using this
  have hv : v ≠ 0 := by
    rintro rfl
    apply huv; refine ⟨?_, rfl⟩
    have : u * e = 0 := by simpa using hval
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · omega
  set x : ℚ := (t : ℚ) ^ (-2 * f) * β ^ (2 * (e : ℤ))
  have hx0 : 0 < x := by
    have : 0 < β ^ (2 * (e : ℤ)) := Even.zpow_pos (even_two_mul _) hβ
    have : 0 < (t : ℚ) ^ (-2 * f) := zpow_pos (by positivity) _
    positivity
  have hxv : x ^ v = 1 := by
    have h2 : ((t : ℚ) ^ u * β ^ v) ^ (2 * (e : ℤ)) = 1 := by rw [hrel, one_zpow]
    rw [mul_zpow, ← zpow_mul, ← zpow_mul] at h2
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← h2]
    congr 2
    · linear_combination (-2) * hval
    · ring
  have hx1 : x = 1 := by
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · have : x ^ (-v).toNat = 1 := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, hxv, inv_one]
      exact (pow_eq_one_iff_of_nonneg hx0.le (by omega)).1 this
    · have : x ^ v.toNat = 1 := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), hxv]
      exact (pow_eq_one_iff_of_nonneg hx0.le (by omega)).1 this
  refine ⟨e, f, he1, he2, hf, ?_⟩
  have : β ^ (2 * (e : ℤ)) = (t : ℚ) ^ (2 * f) := by
    have := hx1
    simp only [x] at this
    rw [show (-2 * f) = -(2 * f) by ring, zpow_neg] at this
    field_simp at this
    linarith [this]
  rw [← this, ← zpow_natCast]; push_cast; rfl



theorem three_coprime_pow {g : ℕ} {x : ℤ} (hx : ¬ (3 : ℤ) ∣ x) (k : ℕ) : IsCoprime ((3 : ℤ) ^ g) (x ^ k) :=
  ((Int.prime_three.coprime_iff_not_dvd.2 hx).pow_left).pow_right

theorem finish_lte (t n g B : ℕ) (ht : 2 ≤ t) (ht1 : (3 : ℤ) ∣ (t : ℤ) - 1) (hn : 1 ≤ n)
    (hnB : n ≤ B) (h : (3 : ℤ) ^ g ∣ (t : ℤ) ^ n - 1) : g ≤ Nat.log 3 t + Nat.log 3 B := by
  have h1 : 1 ≤ t ^ n := Nat.one_le_pow _ _ (by omega)
  have hN : 3 ^ g ∣ t ^ n - 1 := by
    have : ((t ^ n - 1 : ℕ) : ℤ) = (t : ℤ) ^ n - 1 := by push_cast [Nat.cast_sub h1]; ring
    rw [← this] at h; exact_mod_cast h
  have ht1' : 3 ∣ t - 1 := by
    have : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ t)]; ring
    rw [← this] at ht1; exact_mod_cast ht1
  exact (le_of_three_pow_dvd_pow_sub_one t n g ht ht1' hn hN).trans
    (Nat.add_le_add_left (Nat.log_mono_right hnB) _)

/-- **The 3-adic bound, dependent case (proved, no zero lemma).**  If `(b/a)^{2e} = t^{2f}`
(`small_relation`), `3 ∣ t − 1`, `3 ∤ a`, `tᵟa ≠ b`, `3ᵍ ∣ tᵟa − b`, then
`g ≤ log₃ t + log₃(2eδ + 2|f|)`: `tᵟa − b ∣ (tᵟa)^{2e} − b^{2e} = a^{2e} t^{−2Q}(t^{2eδ+2Q} − t^{2P})`,
then LTE; equal exponents force `tᵟa = −b`, so `g = 0`. -/
theorem g_le_dep (t : ℕ) (ht : 2 ≤ t) (ht1 : (3 : ℤ) ∣ (t : ℤ) - 1) (a b : ℤ) (ha0 : a ≠ 0)
    (ha3 : ¬ (3 : ℤ) ∣ a) (δ g e : ℕ) (f : ℤ) (he : 1 ≤ e)
    (hrel : ((b : ℚ) / a) ^ (2 * e) = (t : ℚ) ^ (2 * f))
    (hne : (t : ℤ) ^ δ * a ≠ b) (hab : (3 : ℤ) ^ g ∣ (t : ℤ) ^ δ * a - b) :
    g ≤ Nat.log 3 t + Nat.log 3 (2 * e * δ + 2 * f.natAbs) := by
  have ht3 : ¬ (3 : ℤ) ∣ (t : ℤ) := by
    intro h; have := Int.dvd_sub h ht1; norm_num at this
  set c := 2 * e
  set P := f.toNat
  set Q := (-f).toNat
  have hfPQ : f = P - Q := by omega
  have hPQ : f.natAbs = P + Q := by omega
  -- integer relation  b^c t^(2Q) = a^c t^(2P)
  have hint : b ^ c * (t : ℤ) ^ (2 * Q) = a ^ c * (t : ℤ) ^ (2 * P) := by
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
    have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    have h := hrel
    rw [hfPQ, mul_sub, zpow_sub₀ ht', div_pow] at h
    simp only [← Int.cast_natCast (R := ℚ)] at h
    have : ((b ^ c * (t : ℤ) ^ (2 * Q) : ℤ) : ℚ) = ((a ^ c * (t : ℤ) ^ (2 * P) : ℤ) : ℚ) := by
      push_cast
      rw [show (2 : ℤ) * (P : ℤ) = ((2 * P : ℕ) : ℤ) by push_cast; ring,
        show (2 : ℤ) * (Q : ℤ) = ((2 * Q : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast] at h
      field_simp at h
      linear_combination h
    exact_mod_cast this
  have hdvd1 : (3 : ℤ) ^ g ∣ a ^ c * ((t : ℤ) ^ (c * δ + 2 * Q) - (t : ℤ) ^ (2 * P)) := by
    have h1 : (3 : ℤ) ^ g ∣ ((t : ℤ) ^ δ * a) ^ c - b ^ c := hab.trans (sub_dvd_pow_sub_pow _ _ _)
    have : a ^ c * ((t : ℤ) ^ (c * δ + 2 * Q) - (t : ℤ) ^ (2 * P)) =
        (t : ℤ) ^ (2 * Q) * (((t : ℤ) ^ δ * a) ^ c - b ^ c) := by
      rw [mul_sub, mul_sub, mul_pow, ← pow_mul, pow_add, mul_comm δ c]
      linear_combination hint
    rw [this]; exact h1.mul_left _
  have hdvd2 : (3 : ℤ) ^ g ∣ (t : ℤ) ^ (c * δ + 2 * Q) - (t : ℤ) ^ (2 * P) :=
    (three_coprime_pow ha3 c).dvd_of_dvd_mul_left hdvd1
  rcases Nat.lt_trichotomy (c * δ + 2 * Q) (2 * P) with hlt | heq | hgt
  · obtain ⟨n, hn⟩ : ∃ n, 2 * P = c * δ + 2 * Q + n := ⟨_, (Nat.add_sub_cancel' hlt.le).symm⟩
    have h3 : (3 : ℤ) ^ g ∣ (t : ℤ) ^ n - 1 := by
      rw [hn, pow_add (t : ℤ) (c * δ + 2 * Q) n] at hdvd2
      have : (t : ℤ) ^ (c * δ + 2 * Q) - (t : ℤ) ^ (c * δ + 2 * Q) * (t : ℤ) ^ n =
          -((t : ℤ) ^ (c * δ + 2 * Q) * ((t : ℤ) ^ n - 1)) := by ring
      rw [this, dvd_neg] at hdvd2
      exact (three_coprime_pow ht3 _).dvd_of_dvd_mul_left hdvd2
    exact finish_lte t n g _ ht ht1 (by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · omega
      · exact h0) (by omega) h3
  · -- equal exponents: (tᵟa)^c = b^c, so tᵟa = −b and g = 0
    have hzero : ((t : ℤ) ^ δ * a) ^ c = b ^ c := by
      have : a ^ c * ((t : ℤ) ^ (c * δ + 2 * Q) - (t : ℤ) ^ (2 * P)) =
          (t : ℤ) ^ (2 * Q) * (((t : ℤ) ^ δ * a) ^ c - b ^ c) := by
        rw [mul_sub, mul_sub, mul_pow, ← pow_mul, pow_add, mul_comm δ c]
        linear_combination hint
      rw [heq, sub_self, mul_zero] at this
      have ht0 : (t : ℤ) ^ (2 * Q) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : t ≠ 0))
      exact sub_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left ht0)
    have habs : |(t : ℤ) ^ δ * a| = |b| := by
      have hc : c ≠ 0 := by omega
      have := congrArg abs hzero
      rw [abs_pow, abs_pow] at this
      exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hc).1 this
    have hneg : b = -((t : ℤ) ^ δ * a) := by
      rcases abs_eq_abs.1 habs with h | h
      · exact absurd h hne
      · linarith
    rw [hneg, sub_neg_eq_add, ← two_mul] at hab
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · omega
    · exfalso
      have h3 : (3 : ℤ) ∣ 2 * ((t : ℤ) ^ δ * a) := (dvd_pow_self 3 (by omega)).trans hab
      rcases (Int.prime_three.dvd_or_dvd h3) with h | h
      · norm_num at h
      · rcases (Int.prime_three.dvd_or_dvd h) with h' | h'
        · exact ht3 (Int.prime_three.dvd_of_dvd_pow h')
        · exact ha3 h'
  · obtain ⟨n, hn⟩ : ∃ n, c * δ + 2 * Q = 2 * P + n := ⟨_, (Nat.add_sub_cancel' hgt.le).symm⟩
    have h3 : (3 : ℤ) ^ g ∣ (t : ℤ) ^ n - 1 := by
      rw [hn, pow_add (t : ℤ) (2 * P) n] at hdvd2
      have : (t : ℤ) ^ (2 * P) * (t : ℤ) ^ n - (t : ℤ) ^ (2 * P) =
          (t : ℤ) ^ (2 * P) * ((t : ℤ) ^ n - 1) := by ring
      rw [this] at hdvd2
      exact (three_coprime_pow ht3 _).dvd_of_dvd_mul_left hdvd2
    exact finish_lte t n g _ ht ht1 (by omega) (by omega) h3

end ZeroWiring

end PadicTwoLogs
