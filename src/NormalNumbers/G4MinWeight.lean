/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Tensor

/-!
# G4 §4A: the tensor matrix has minimum weight `2^K` and column mass `2^K`

Brief §4A lists, among the required facts about `A = D_s^{⊗K}`:

> For `q ≠ 0`, `w = Aᵀ q` has at least `2^K` nonzero entries and sup norm at most `2^K` times
> the sup norm of `q`.

Both are proved here, for a general `K`-fold Kronecker power.

* `wt w` is the Hamming weight (number of nonzero coordinates) of `w`.
* `MinWeight M d` says every nonzero `q ᵥ* M` has weight at least `d`.
* `minWeight_kronPow` is the **minimum distance of a product code**: if `M` has minimum weight
  `d`, then `M^{⊗K}` has minimum weight `d^K`.  The proof is the classical row/column argument:
  a nonzero `K+1`-fold transform restricted to one first-coordinate slice is a nonzero `K`-fold
  transform, so at least `d^K` slices survive, and each surviving slice spreads over at least
  `d` values of the peeled coordinate.
* `minWeight_diff`: the adjacent-difference matrix `D_s` has minimum weight `2` — its row sums
  vanish, so a nonzero image cannot be supported on a single coordinate, and `D_s D_sᵀ = T_s`
  with `det T_s = s+1 ≠ 0` makes `q ↦ q ᵥ* D_s` injective.
* Hence `minWeight_tensorDiff : MinWeight (tensorDiff K s) (2 ^ K)`.
* `abs_vecMul_kronPow_le`: `‖q ᵥ* M^{⊗K}‖∞ ≤ B^K ‖q‖∞` when every column of `M` has
  absolute-value sum at most `B`; `colSum_diff_le` gives `B = 2` for `D_s`, hence
  `abs_vecMul_tensorDiff_le`.
-/

open Finset Matrix
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### Hamming weight -/

section Weight

variable {R : Type*} [Zero R] [DecidableEq R]

/-- The number of nonzero coordinates of `w`. -/
def wt {ι : Type*} [Fintype ι] (w : ι → R) : ℕ := (univ.filter fun α => w α ≠ 0).card

lemma wt_eq_zero_iff {ι : Type*} [Fintype ι] (w : ι → R) : wt w = 0 ↔ w = 0 := by
  unfold wt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext α; by_contra hα; exact h (mem_univ α) hα
  · intro h α _; rw [h]; simp

lemma one_le_wt {ι : Type*} [Fintype ι] {w : ι → R} (hw : w ≠ 0) : 1 ≤ wt w :=
  Nat.one_le_iff_ne_zero.2 fun h => hw ((wt_eq_zero_iff w).1 h)

end Weight

/-- A vector with vanishing total sum and at least one nonzero coordinate has at least two. -/
lemma two_le_wt_of_sum_eq_zero {ι R : Type*} [Fintype ι] [AddCommMonoid R] [DecidableEq R]
    {w : ι → R} (hsum : ∑ α, w α = 0) (hw : w ≠ 0) : 2 ≤ wt w := by
  by_contra hlt
  interval_cases h : wt w
  · exact absurd h (by simpa using Nat.one_le_iff_ne_zero.1 (one_le_wt hw))
  · obtain ⟨α₀, hα₀⟩ := Finset.card_eq_one.1 h
    have hsub : (univ.filter fun α => w α ≠ 0) ⊆ univ := Finset.filter_subset _ _
    have hz : ∑ α ∈ (univ.filter fun α => w α ≠ 0), w α = ∑ α, w α := by
      refine Finset.sum_subset hsub ?_
      intro x _ hx
      simpa using (by simpa using hx : ¬ w x ≠ 0)
    rw [hα₀, Finset.sum_singleton, hsum] at hz
    have : α₀ ∈ (univ.filter fun α => w α ≠ 0) := by rw [hα₀]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.1 this).2 hz

/-! ### Minimum weight of a matrix and of its Kronecker powers -/

section MinWeight

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- `M` has minimum weight at least `d`: every nonzero left transform `q ᵥ* M` has at least `d`
nonzero coordinates. -/
def MinWeight {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n R) (d : ℕ) : Prop :=
  ∀ q : m → R, q ≠ 0 → d ≤ wt (M.vecMul q)

/-- The `K`-fold Kronecker power of `M`, indexed by tuples. -/
def kronPow (K : ℕ) {m n : Type*} (M : Matrix m n R) :
    Matrix (Fin K → m) (Fin K → n) R := fun a c => ∏ i, M (a i) (c i)

/-- Peeling the first coordinate of a sum over tuples. -/
lemma sum_cons_succ {β : Type*} [Fintype β] {K : ℕ} {S : Type*} [AddCommMonoid S]
    (f : (Fin (K + 1) → β) → S) :
    ∑ a, f a = ∑ a₀ : β, ∑ a' : Fin K → β, f (Fin.cons a₀ a') := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => β) f, Fintype.sum_prod_type]
  rfl

/-- Peeling the first coordinate in the Hamming weight of a tuple-indexed vector. -/
lemma wt_cons {β : Type*} [Fintype β] {K : ℕ} {S : Type*} [Zero S] [DecidableEq S]
    (w : (Fin (K + 1) → β) → S) :
    wt w = ∑ c' : Fin K → β, wt (fun c₀ : β => w (Fin.cons c₀ c')) := by
  unfold wt
  simp only [Finset.card_filter]
  rw [sum_cons_succ (fun a => if w a ≠ 0 then 1 else 0), Finset.sum_comm]

/-- The one-step recursion for the Kronecker transform. -/
lemma vecMul_kronPow_cons {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n R) (K : ℕ)
    (q : (Fin (K + 1) → m) → R) (c₀ : n) (c' : Fin K → n) :
    (kronPow (K + 1) M).vecMul q (Fin.cons c₀ c')
      = M.vecMul (fun a₀ => (kronPow K M).vecMul (fun a' => q (Fin.cons a₀ a')) c') c₀ := by
  simp only [Matrix.vecMul, dotProduct, kronPow]
  rw [sum_cons_succ (fun a : Fin (K + 1) → m =>
    q a * ∏ i, M (a i) ((Fin.cons c₀ c' : Fin (K + 1) → n) i))]
  refine Finset.sum_congr rfl fun a₀ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- **Minimum distance of a product code.**  A `K`-fold Kronecker power of a matrix of minimum
weight `d` has minimum weight `d ^ K`. -/
theorem minWeight_kronPow {m n : Type*} [Fintype m] [Fintype n] {M : Matrix m n R} {d : ℕ}
    (hM : MinWeight M d) : ∀ K, MinWeight (kronPow K M) (d ^ K) := by
  intro K
  induction K with
  | zero =>
    intro q hq
    rw [pow_zero]
    refine one_le_wt ?_
    intro hcontra
    refine hq (funext fun a => ?_)
    have h0 := congrFun hcontra (Fin.elim0 : Fin 0 → n)
    have hu : ∀ x : Fin 0 → m, x = a := fun x => funext fun i => i.elim0
    rw [Matrix.vecMul, dotProduct,
      Finset.sum_eq_single a (fun b _ hb => absurd (hu b) hb) (fun h => absurd (mem_univ a) h)] at h0
    simpa [kronPow] using h0
  | succ K ih =>
    intro q hq
    obtain ⟨a, ha⟩ : ∃ a, q a ≠ 0 := by
      by_contra h
      push Not at h
      exact hq (funext h)
    have hslice : (fun a' => q (Fin.cons (a 0) a')) ≠ 0 := by
      intro h
      have h2 := congrFun h (Fin.tail a)
      rw [Fin.cons_self_tail] at h2
      exact ha h2
    set F : Finset (Fin K → n) := univ.filter
      (fun c' => (kronPow K M).vecMul (fun a' => q (Fin.cons (a 0) a')) c' ≠ 0) with hF
    have hC : d ^ K ≤ F.card := ih _ hslice
    have key : ∀ c' ∈ F,
        d ≤ wt (fun c₀ : n => (kronPow (K + 1) M).vecMul q (Fin.cons c₀ c')) := by
      intro c' hc'
      have hne : (fun b : m => (kronPow K M).vecMul (fun a' => q (Fin.cons b a')) c') ≠ 0 := by
        intro h
        have := congrFun h (a 0)
        rw [hF] at hc'
        exact (Finset.mem_filter.1 hc').2 this
      have hfun : (fun c₀ : n => (kronPow (K + 1) M).vecMul q (Fin.cons c₀ c'))
          = M.vecMul (fun b : m => (kronPow K M).vecMul (fun a' => q (Fin.cons b a')) c') := by
        funext c₀
        exact vecMul_kronPow_cons M K q c₀ c'
      rw [hfun]
      exact hM _ hne
    calc d ^ (K + 1) = d ^ K * d := by ring
      _ ≤ F.card * d := Nat.mul_le_mul_right _ hC
      _ = ∑ _c' ∈ F, d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c' ∈ F, wt (fun c₀ : n => (kronPow (K + 1) M).vecMul q (Fin.cons c₀ c')) :=
          Finset.sum_le_sum key
      _ ≤ ∑ c' : Fin K → n, wt (fun c₀ : n => (kronPow (K + 1) M).vecMul q (Fin.cons c₀ c')) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ F)
      _ = wt ((kronPow (K + 1) M).vecMul q) := (wt_cons _).symm


/-! ### The adjacent-difference matrix has minimum weight two -/

/-- Each row of `D_s` sums to zero. -/
lemma sum_diff_row (s : ℕ) (a : Fin s) : ∑ c, diff s a c = 0 := by
  simp [diff, Pi.single_apply, Finset.sum_sub_distrib]

/-- `q ↦ q ᵥ* D_s` is injective: `D_s D_sᵀ = T_s` and `det T_s = s + 1 ≠ 0`. -/
lemma vecMul_diff_eq_zero (s : ℕ) {q : Fin s → ℝ} (h : (diff s).vecMul q = 0) : q = 0 := by
  have hdet : IsUnit (gram s).det := by
    rw [det_gram]
    exact isUnit_iff_ne_zero.2 (by positivity)
  have h1 : (gram s).vecMul q = 0 := by
    rw [← diff_mul_transpose, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]
  calc q = (q ᵥ* gram s) ᵥ* (gram s)⁻¹ := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = 0 := by rw [show q ᵥ* gram s = 0 from h1, Matrix.zero_vecMul]

/-- **`D_s` has minimum weight two.**  The image of a nonzero `q` is nonzero (injectivity) and
has vanishing total sum (telescoping), so it cannot be supported on one coordinate. -/
theorem minWeight_diff (s : ℕ) : MinWeight (diff s) 2 := by
  intro q hq
  refine two_le_wt_of_sum_eq_zero ?_ (fun h => hq (vecMul_diff_eq_zero s h))
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.mul_sum, sum_diff_row, mul_zero]

/-- **Brief §4A**: for `q ≠ 0`, `w = q ᵥ* D_s^{⊗K}` has at least `2^K` nonzero entries. -/
theorem minWeight_tensorDiff (K s : ℕ) : MinWeight (tensorDiff K s) (2 ^ K) := by
  have h : kronPow K (diff s) = tensorDiff K s := rfl
  rw [← h]
  exact minWeight_kronPow (minWeight_diff s) K

/-! ### The sup-norm bound `‖q ᵥ* A‖∞ ≤ 2^K ‖q‖∞` -/

/-- The absolute column mass of a Kronecker power is the product of the column masses. -/
lemma colSum_kronPow {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) (K : ℕ)
    (c : Fin K → n) : ∑ a : Fin K → m, |kronPow K M a c| = ∏ i, ∑ b, |M b (c i)| := by
  simp only [kronPow, Finset.abs_prod]
  rw [Fintype.prod_sum (fun i b => |M b (c i)|)]

/-- `‖q ᵥ* M^{⊗K}‖∞ ≤ B^K ‖q‖∞` when every column of `M` has absolute mass at most `B`. -/
theorem abs_vecMul_kronPow_le {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) (K : ℕ)
    {B Q : ℝ} (hB : ∀ c : n, ∑ b, |M b c| ≤ B) (hQ : 0 ≤ Q)
    (q : (Fin K → m) → ℝ) (hq : ∀ a, |q a| ≤ Q) (c : Fin K → n) :
    |(kronPow K M).vecMul q c| ≤ B ^ K * Q := by
  calc |(kronPow K M).vecMul q c| = |∑ a : Fin K → m, q a * kronPow K M a c| := rfl
    _ ≤ ∑ a : Fin K → m, |q a * kronPow K M a c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin K → m, |q a| * |kronPow K M a c| := by
        exact Finset.sum_congr rfl fun a _ => abs_mul _ _
    _ ≤ ∑ a : Fin K → m, Q * |kronPow K M a c| :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hq a) (abs_nonneg _)
    _ = Q * ∑ a : Fin K → m, |kronPow K M a c| := by rw [Finset.mul_sum]
    _ = Q * ∏ i, ∑ b, |M b (c i)| := by rw [colSum_kronPow]
    _ ≤ Q * ∏ _i : Fin K, B := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod ?_ ?_) hQ
        · exact fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _
        · exact fun i _ => hB (c i)
    _ = B ^ K * Q := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring

/-- At most two entries of any column of `D_s` are nonzero, each of absolute value one. -/
lemma sum_indicator_le_one {s : ℕ} (f : Fin s → Fin (s + 1)) (hf : Function.Injective f)
    (c : Fin (s + 1)) : ∑ b : Fin s, (if c = f b then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ b, c = f b
  · obtain ⟨b0, rfl⟩ := h
    rw [Finset.sum_eq_single b0 (fun b _ hb => if_neg fun hc => hb (hf hc.symm))
      (fun hb => absurd (mem_univ b0) hb)]
    simp
  · push Not at h
    rw [Finset.sum_eq_zero fun b _ => if_neg (h b)]
    norm_num

lemma colSum_diff_le (s : ℕ) (c : Fin (s + 1)) : ∑ b : Fin s, |diff s b c| ≤ 2 := by
  have h1 : ∀ b : Fin s, |diff s b c|
      ≤ (if c = b.castSucc then (1 : ℝ) else 0) + (if c = b.succ then (1 : ℝ) else 0) := by
    intro b
    simp only [diff, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num
  calc ∑ b : Fin s, |diff s b c|
      ≤ ∑ b : Fin s, ((if c = b.castSucc then (1 : ℝ) else 0)
          + (if c = b.succ then (1 : ℝ) else 0)) := Finset.sum_le_sum fun b _ => h1 b
    _ = (∑ b : Fin s, if c = b.castSucc then (1 : ℝ) else 0)
          + ∑ b : Fin s, (if c = b.succ then (1 : ℝ) else 0) := Finset.sum_add_distrib
    _ ≤ 1 + 1 := add_le_add (sum_indicator_le_one _ (Fin.castSucc_injective s) c)
          (sum_indicator_le_one _ (Fin.succ_injective s) c)
    _ = 2 := by norm_num

/-- **Brief §4A**: `‖q ᵥ* D_s^{⊗K}‖∞ ≤ 2^K ‖q‖∞`. -/
theorem abs_vecMul_tensorDiff_le (K s : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) (q : (Fin K → Fin s) → ℝ)
    (hq : ∀ a, |q a| ≤ Q) (c : Fin K → Fin (s + 1)) :
    |(tensorDiff K s).vecMul q c| ≤ 2 ^ K * Q := by
  have h : kronPow K (diff s) = tensorDiff K s := rfl
  rw [← h]
  exact abs_vecMul_kronPow_le (diff s) K (colSum_diff_le s) hQ q hq c

end MinWeight

end NormalNumbers.G4
