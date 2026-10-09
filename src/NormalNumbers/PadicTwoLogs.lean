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
