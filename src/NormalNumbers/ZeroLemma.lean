/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PadicTwoLogs
import Mathlib.Algebra.Polynomial.Taylor
import Architect

/-!
# Laurent's zero lemma for `G_a × G_m` (proved)

`laurentZeroLemma : Literature.LaurentZeroLemma`.  The formerly cited two-variable zero lemma behind the
3-adic two-logarithm bound has a short elementary proof (review lap 13, 2026-10-09).

Let `P(X, Y) = Σ_{l<L} q_l(X) Yˡ ≠ 0` vanish at `φ(σ + γ)` for `σ ∈ Σ₁ = [0,R₁)×[0,S₁)`,
`γ ∈ Σ₂ = [0,R₂)×[0,S₂)`, where `φ(r,s) = (x, y) = (r b₂ + s b₁, α₁ʳ α₂ˢ)` is additive in `x` and
multiplicative in `y`.  Let `S = {l : q_l ≠ 0}`, `m = #S`.
1. *Rows.*  The vectors `(yˡ)_{l∈S}`, `y` running over the `y`-values of `Σ₁`, span `ℚ^S`: a kernel
   vector `v` gives `Σ_{l∈S} v_l Xˡ` of degree `< L` with `≥ L` roots.  So some `σ₁, …, σ_m ∈ Σ₁`
   make `V = [y_{σᵢ}ˡ]_{i, l∈S}` nonsingular (`exists_det_submatrix_ne_zero`).
2. *The determinant.*  `D(X) = det[q_l(X + x_{σᵢ}) y_{σᵢ}ˡ]_{i, l∈S}` has degree `≤ Σ_{l∈S} deg q_l
   ≤ (K−1)L`, and vanishes at every `x`-value `ξ = x_γ` of `Σ₂`: the evaluated matrix kills the
   nonzero vector `(y_γˡ)_{l∈S}`, since `Σ_l q_l(x_γ + x_{σᵢ})(y_{σᵢ} y_γ)ˡ = P(φ(σᵢ + γ)) = 0`.
   There are `> (K−1)L` such `ξ`, so `D = 0`.
3. *Leading coefficient.*  Column `l` has degree `≤ deg q_l`, so the coefficient of
   `X^{Σ deg q_l}` in `D` is `det` of the column-leading coefficients,
   `(∏_{l∈S} lc q_l) · det V ≠ 0` (`coeff_det_of_col`).  Contradiction.
Multiplicative independence of `α₁, α₂` is not used: it enters only through the two cardinality
hypotheses.
-/

open Polynomial Finset Matrix

namespace PadicTwoLogs

/-- The coefficient of a product at the sum of degree bounds. -/
theorem coeff_prod_sum_of_natDegree_le {ι R : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → R[X]) (d : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (h a (mem_insert_self _ _))
        (le_trans (natDegree_prod_le _ _) (sum_le_sum fun i hi => h i (mem_insert_of_mem hi))),
      ih fun i hi => h i (mem_insert_of_mem hi)]

/-- Degree of a determinant whose column `j` has degree `≤ d j`. -/
theorem natDegree_det_le_of_col {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R[X]) (d : n → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j, d j := by
  rw [det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [← C_eq_intCast]
  exact (natDegree_C_mul_le _ _).trans (le_trans (natDegree_prod_le _ _) (sum_le_sum fun i _ => h _ _))

/-- **The top coefficient of a determinant with column degree bounds (proved).**  If column `j`
has degree `≤ d j`, the coefficient of `X^{Σ d j}` in `det M` is the determinant of the matrix of
column-top coefficients. -/
theorem coeff_det_of_col {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R[X]) (d : n → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.coeff (∑ j, d j) = (Matrix.of fun i j => (M i j).coeff (d j)).det := by
  rw [det_apply', det_apply', finsetSum_coeff]
  refine sum_congr rfl fun σ _ => ?_
  rw [← C_eq_intCast, coeff_C_mul,
    coeff_prod_sum_of_natDegree_le _ _ _ fun i _ => h _ _]
  rfl

/-- **Laurent's zero lemma, rational two-variable form (PROVED).**  See the module docstring for
the argument; `Literature.LaurentZeroLemma` for the statement and its source. -/
@[blueprint (title := "Laurent's two-variable zero lemma, elementary proof")]
theorem laurentZeroLemma : Literature.LaurentZeroLemma := by
  intro α₁ α₂ b₁ b₂ K L R₁ R₂ S₁ S₂ hα₁ hα₂ _hind hY hX q hdeg hvan
  classical
  by_contra hne
  push Not at hne
  obtain ⟨l₀, hl₀L, hl₀⟩ := hne
  set S := (range L).filter fun l => q l ≠ 0 with hS
  have hl₀S : l₀ ∈ S := by simp [hS, hl₀L, hl₀]
  have hSL : ∀ l ∈ S, l < L := fun l hl => by simpa using (mem_filter.1 hl).1
  have hSq : ∀ l ∈ S, q l ≠ 0 := fun l hl => (mem_filter.1 hl).2
  -- the points
  set G₁ := range R₁ ×ˢ range S₁ with hG₁
  let x : ℕ × ℕ → ℚ := fun rs => (rs.1 : ℚ) * b₂ + (rs.2 : ℚ) * b₁
  let y : ℕ × ℕ → ℚ := fun rs => α₁ ^ rs.1 * α₂ ^ rs.2
  have hy0 : ∀ rs, y rs ≠ 0 := fun rs => mul_ne_zero (pow_ne_zero _ hα₁) (pow_ne_zero _ hα₂)
  -- 1. rows: a nonsingular generalized Vandermonde minor
  let A : Matrix G₁ S ℚ := fun σ l => y σ.1 ^ (l : ℕ)
  have hA : ∀ v, A *ᵥ v = 0 → v = 0 := by
    intro v hv
    set p : ℚ[X] := ∑ l : S, C (v l) * X ^ (l : ℕ) with hp
    have hpdeg : p.natDegree < L := by
      have : p.natDegree ≤ L - 1 :=
        natDegree_sum_le_of_forall_le _ _ fun l _ =>
          (natDegree_C_mul_X_pow_le _ _).trans (by have := hSL l l.2; omega)
      have := hSL l₀ hl₀S
      omega
    have hp0 : p = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p
        (G₁.image fun rs : ℕ × ℕ => α₁ ^ rs.1 * α₂ ^ rs.2) (fun z hz => ?_)
        (lt_of_lt_of_le hpdeg hY)
      obtain ⟨rs, hrs, rfl⟩ := mem_image.1 hz
      have := congrFun hv ⟨rs, hrs⟩
      simp only [mulVec, dotProduct, Pi.zero_apply, A] at this
      rw [hp, eval_finsetSum]
      rw [← this]
      exact sum_congr rfl fun l _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
    funext l
    have hc := congrArg (fun p : ℚ[X] => p.coeff (l : ℕ)) hp0
    simp only [hp, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
    rw [Fintype.sum_eq_single l fun l' hl' => if_neg fun h => hl' (Subtype.ext h.symm)] at hc
    simpa using hc
  obtain ⟨f, hf⟩ := exists_det_submatrix_ne_zero A hA
  -- 2. the polynomial determinant
  let M : Matrix S S ℚ[X] := fun i l => taylor (x (f i).1) (q l) * C (y (f i).1 ^ (l : ℕ))
  have hMdeg : ∀ i l, (M i l).natDegree ≤ (q l).natDegree := fun i l =>
    (natDegree_mul_C_le _ _).trans (natDegree_taylor _ _).le
  set X₂ : Finset ℤ := (range R₂ ×ˢ range S₂).image fun rs : ℕ × ℕ =>
    (rs.1 : ℤ) * b₂ + (rs.2 : ℤ) * b₁ with hX₂
  have hMzero : M.det = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (X₂.image (Int.cast : ℤ → ℚ))
      (fun ξ hξ => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := mem_image.1 hξ
      obtain ⟨γ, hγ, rfl⟩ := mem_image.1 hz
      obtain ⟨hγ1, hγ2⟩ := mem_product.1 hγ
      rw [mem_range] at hγ1 hγ2
      rw [← coe_evalRingHom, RingHom.map_det]
      refine (exists_mulVec_eq_zero_iff).1 ⟨fun l => y γ ^ (l : ℕ), fun h0 => ?_, ?_⟩
      · have := congrFun h0 ⟨l₀, hl₀S⟩
        exact pow_ne_zero _ (hy0 γ) this
      · funext i
        obtain ⟨hi1, hi2⟩ := mem_product.1 (f i).2
        rw [mem_range] at hi1 hi2
        have hv := hvan ((f i).1.1 + γ.1) (by omega) ((f i).1.2 + γ.2) (by omega)
        set ξ : ℚ := (((γ.1 : ℤ) * b₂ + (γ.2 : ℤ) * b₁ : ℤ) : ℚ) with hξ
        let g : ℕ → ℚ := fun l => eval ξ (taylor (x (f i).1) (q l) * C (y (f i).1 ^ l)) * y γ ^ l
        change ∑ l : S, g l = 0
        rw [sum_coe_sort S g, hS, sum_filter]
        refine Eq.trans (sum_congr rfl ?_) hv
        intro l _
        split_ifs with hq
        · simp only [g, eval_mul, taylor_eval, eval_C, x, y, hξ]
          push_cast
          ring_nf
        · rw [not_not] at hq
          simp [hq]
    · calc M.det.natDegree ≤ ∑ l : S, (q l).natDegree := natDegree_det_le_of_col M _ hMdeg
        _ ≤ ∑ _l : S, (K - 1) := sum_le_sum fun l _ => by
            have := hdeg l (hSL l l.2); omega
        _ = S.card * (K - 1) := by simp
        _ ≤ L * (K - 1) := by
            gcongr
            calc S.card ≤ (range L).card := card_filter_le _ _
              _ = L := card_range L
        _ = (K - 1) * L := mul_comm _ _
        _ < X₂.card := hX
        _ = (X₂.image (Int.cast : ℤ → ℚ)).card :=
            (card_image_of_injective _ Int.cast_injective).symm
  -- 3. the top coefficient
  have htop := coeff_det_of_col M (fun l => (q l).natDegree) hMdeg
  rw [hMzero, coeff_zero] at htop
  have hcol : (Matrix.of fun i l => (M i l).coeff (q l).natDegree) =
      Matrix.of fun i (l : S) => (q (l : ℕ)).leadingCoeff * (A.submatrix f id) i l := by
    ext i l
    simp only [of_apply, M, coeff_mul_C]
    rw [← natDegree_taylor (q l) (x (f i).1), coeff_natDegree, leadingCoeff_taylor]
    show _ = (q l).leadingCoeff * y (f i).1 ^ (l : ℕ)
    ring
  rw [hcol, det_mul_row] at htop
  refine (mul_ne_zero (prod_ne_zero_iff.2 fun l _ => ?_) hf) htop.symm
  exact leadingCoeff_ne_zero.2 (hSq l l.2)

end PadicTwoLogs
