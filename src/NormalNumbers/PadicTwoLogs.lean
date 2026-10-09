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
theorem dvd_det_interp {R : Type*} [CommRing R] (p t w : R) {g : ℕ} (hg : 1 ≤ g)
    (ht : p ∣ t - 1) (hw : p ^ g ∣ w - 1) (K L : ℕ) (z s : Fin K × Fin L → ℕ) (T : ℕ) :
    p ^ (T * (K * L - (T + K) * (T / g + 1))) ∣
      (Matrix.of fun (x l : Fin K × Fin L) =>
        (z x : R) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x)).det := by
  classical
  choose c hc0 hc using pow_mul_choose_expand
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
      (z x : R) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) * w ^ ((l.2 : ℕ) * s x)) = P * Q := by
    ext x l
    have ez : (z x : R) ^ (l.1 : ℕ) * t ^ ((l.2 : ℕ) * z x) =
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
