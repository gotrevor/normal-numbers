/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Spectral

/-!
# G4 disjunctivity, §4B: the tensor power `AAᵀ = T_s^{⊗K}` and `det(I + AAᵀ)`

`tensorGram K s` is the `K`-fold Kronecker power of `gram s`, indexed by `Fin K → Fin s`.
Its eigenvectors are the product sine vectors `tensorVec j a = ∏ᵢ sineVec s (j i) (a i)` with
eigenvalues `tensorLam j = ∏ᵢ lam s (j i)`; they are pairwise orthogonal and nonzero, hence an
eigenbasis, and

  `det (1 + tensorGram K s) = ∏_j (1 + tensorLam j)`   (`det_one_add_tensorGram`).
-/

open Matrix Finset Real
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### Abstract: an orthogonal eigenbasis diagonalises `det (1 + M)` -/

section abstract
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `M` has a family `v` of pairwise-orthogonal, non-null eigenvectors indexed by `n` itself,
then `det M = ∏ μ`. -/
theorem det_of_orthogonal_eigenbasis (M : Matrix n n ℝ) (v : n → n → ℝ) (μ : n → ℝ)
    (heig : ∀ j, M.mulVec (v j) = μ j • v j)
    (horth : ∀ j j', j ≠ j' → v j ⬝ᵥ v j' = 0)
    (hself : ∀ j, v j ⬝ᵥ v j ≠ 0) :
    M.det = ∏ j, μ j := by
  -- `P` has the eigenvectors as columns
  let P : Matrix n n ℝ := Matrix.of fun a j => v j a
  have hMP : M * P = P * diagonal μ := by
    ext a j
    rw [mul_diagonal, Matrix.mul_apply]
    have := congrFun (heig j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [P, Matrix.of_apply]
    rw [this]; ring
  have hPtP : Pᵀ * P = diagonal (fun j => v j ⬝ᵥ v j) := by
    ext j j'
    rw [Matrix.mul_apply, diagonal_apply]
    simp only [P, transpose_apply, Matrix.of_apply]
    by_cases h : j = j'
    · subst h; simp [dotProduct]
    · rw [if_neg h]; exact horth j j' h
  have hdetP : P.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPtP
    rw [det_mul, det_transpose, h0, mul_zero, det_diagonal] at this
    exact (Finset.prod_ne_zero_iff.mpr fun j _ => hself j) this.symm
  have := congrArg Matrix.det hMP
  rw [det_mul, det_mul, det_diagonal] at this
  exact mul_right_cancel₀ hdetP (by rw [this, mul_comm])

/-- The `1 + M` form: `det (1 + M) = ∏ (1 + μ)`. -/
theorem det_one_add_of_orthogonal_eigenbasis (M : Matrix n n ℝ) (v : n → n → ℝ) (μ : n → ℝ)
    (heig : ∀ j, M.mulVec (v j) = μ j • v j)
    (horth : ∀ j j', j ≠ j' → v j ⬝ᵥ v j' = 0)
    (hself : ∀ j, v j ⬝ᵥ v j ≠ 0) :
    (1 + M).det = ∏ j, (1 + μ j) :=
  det_of_orthogonal_eigenbasis (1 + M) v (fun j => 1 + μ j)
    (fun j => by rw [Matrix.add_mulVec, Matrix.one_mulVec, heig, add_smul, one_smul]) horth hself

end abstract

/-! ### The tensor power -/

variable (K s : ℕ)

/-- The `K`-fold Kronecker power of `gram s`. -/
def tensorGram : Matrix (Fin K → Fin s) (Fin K → Fin s) ℝ :=
  fun a b => ∏ i, gram s (a i) (b i)

/-- Product sine eigenvector indexed by the multi-index `j`. -/
noncomputable def tensorVec (j : Fin K → Fin s) : (Fin K → Fin s) → ℝ :=
  fun a => ∏ i, sineVec s (j i) (a i)

/-- Product eigenvalue. -/
noncomputable def tensorLam (j : Fin K → Fin s) : ℝ := ∏ i, lam s (j i)

variable {K s}

theorem tensorGram_mulVec_tensorVec (j : Fin K → Fin s) :
    (tensorGram K s).mulVec (tensorVec K s j) = tensorLam K s j • tensorVec K s j := by
  funext a
  simp only [Matrix.mulVec, dotProduct, tensorGram, tensorVec, tensorLam, Pi.smul_apply,
    smul_eq_mul]
  have : ∀ b : Fin K → Fin s, (∏ i, gram s (a i) (b i)) * ∏ i, sineVec s (j i) (b i)
      = ∏ i, gram s (a i) (b i) * sineVec s (j i) (b i) := fun b => (Finset.prod_mul_distrib).symm
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i c => gram s (a i) c * sineVec s (j i) c),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := congrFun (gram_mulVec_sineVec s (j i)) (a i)
  simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this

theorem tensorVec_dotProduct (j j' : Fin K → Fin s) :
    tensorVec K s j ⬝ᵥ tensorVec K s j' = ∏ i, sineVec s (j i) ⬝ᵥ sineVec s (j' i) := by
  simp only [dotProduct, tensorVec]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i c => sineVec s (j i) c * sineVec s (j' i) c)]

theorem tensorVec_orthogonal {j j' : Fin K → Fin s} (h : j ≠ j') :
    tensorVec K s j ⬝ᵥ tensorVec K s j' = 0 := by
  rw [tensorVec_dotProduct]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sineVec_orthogonal s hi)

theorem tensorVec_self_pos (j : Fin K → Fin s) : 0 < tensorVec K s j ⬝ᵥ tensorVec K s j := by
  rw [tensorVec_dotProduct]
  exact Finset.prod_pos fun i _ => sineVec_self_pos (j i)

/-- **`det (I + T_s^{⊗K}) = ∏_j (1 + ∏ᵢ λ_{jᵢ})`.** -/
theorem det_one_add_tensorGram :
    (1 + tensorGram K s).det = ∏ j : Fin K → Fin s, (1 + tensorLam K s j) :=
  det_one_add_of_orthogonal_eigenbasis _ _ _ tensorGram_mulVec_tensorVec
    (fun _ _ h => tensorVec_orthogonal h) (fun j => (tensorVec_self_pos j).ne')

theorem tensorLam_pos (j : Fin K → Fin s) : 0 < tensorLam K s j :=
  Finset.prod_pos fun i _ => lam_pos (j i)

/-- `∏_j λ_j = det T_s = s + 1`. -/
theorem prod_lam (s : ℕ) : ∏ j, lam s j = s + 1 := by
  have := det_of_orthogonal_eigenbasis (gram s) (sineVec s) (lam s) (gram_mulVec_sineVec s)
    (fun _ _ h => sineVec_orthogonal s h) (fun j => (sineVec_self_pos j).ne')
  rw [det_gram] at this; exact this.symm

/-- First log-moment of the spectrum: `∑_j log λ_j = log (s + 1)` — the cancellation that
makes the tensor bound `O(r√K)` instead of `O(rK)`. -/
theorem sum_log_lam (s : ℕ) : ∑ j, Real.log (lam s j) = Real.log (s + 1) := by
  rw [← prod_lam s, Real.log_prod (fun j _ => (lam_pos j).ne')]

/-! ### Second moment of `log Λ_j` over the multi-indices

For any `ℓ : Fin s → ℝ`, with `L₁ = ∑ ℓ`, `L₂ = ∑ ℓ²` and `X_j = ∑ᵢ ℓ (j i)`:

  `s · ∑_j X_j = K s^K L₁`,   `s² · ∑_j X_j² = K s^{K+1} L₂ + K(K−1) s^K L₁²`.

Both by induction on `K`, splitting `Fin (K+1) → Fin s ≃ Fin s × (Fin K → Fin s)`. -/

section moments
variable {s : ℕ}

lemma sum_pi_succ {K : ℕ} (f : (Fin (K + 1) → Fin s) → ℝ) :
    ∑ j, f j = ∑ a : Fin s, ∑ j' : Fin K → Fin s, f (Fin.cons a j' : Fin (K + 1) → Fin s) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin s) f, Fintype.sum_prod_type]
  rfl

theorem sum_pi_linear (ℓ : Fin s → ℝ) (K : ℕ) :
    (s : ℝ) * ∑ j : Fin K → Fin s, ∑ i, ℓ (j i) = K * (s : ℝ) ^ K * ∑ k, ℓ k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_pi_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    push_cast
    linear_combination (s : ℝ) * ih

theorem sum_pi_sq (ℓ : Fin s → ℝ) (K : ℕ) :
    (s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 2
      = K * (s : ℝ) ^ (K + 1) * (∑ k, ℓ k ^ 2) + K * (K - 1) * (s : ℝ) ^ K * (∑ k, ℓ k) ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_pi_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_sq, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Fintype.card_fin,
      nsmul_eq_mul]
    have e1 : ∑ x : Fin s, ∑ x_1 : Fin K → Fin s, 2 * ℓ x * ∑ i, ℓ (x_1 i)
        = 2 * ((∑ k, ℓ k) * ∑ j : Fin K → Fin s, ∑ i, ℓ (j i)) := by
      rw [Finset.sum_mul_sum]; simp_rw [Finset.mul_sum, mul_assoc]
    rw [e1, ← Finset.mul_sum]
    have h1 := sum_pi_linear ℓ K
    have : (s : ℝ) ^ 2 * ((s : ℝ) ^ K * ∑ k, ℓ k ^ 2
          + 2 * ((∑ k, ℓ k) * ∑ j : Fin K → Fin s, ∑ i, ℓ (j i))
          + (s : ℝ) * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 2)
        = (s : ℝ) ^ (K + 2) * ∑ k, ℓ k ^ 2
          + 2 * (∑ k, ℓ k) * (s : ℝ) * ((s : ℝ) * ∑ j : Fin K → Fin s, ∑ i, ℓ (j i))
          + (s : ℝ) * ((s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, ℓ (j i)) ^ 2) := by ring
    rw [h1, ih] at this
    push_cast at this ⊢
    linear_combination this

end moments

/-! ### The bound `log det (I + T_s^{⊗K}) ≤ r (log 2 + C √K)` -/

/-- `log (1 + Λ) ≤ log 2 + |log Λ|` for `Λ > 0`. -/
lemma log_one_add_le_log_two_add_abs_log {Λ : ℝ} (h : 0 < Λ) :
    Real.log (1 + Λ) ≤ Real.log 2 + |Real.log Λ| := by
  rcases le_or_gt Λ 1 with h1 | h1
  · have := Real.log_le_log (by positivity) (show 1 + Λ ≤ 2 by linarith)
    linarith [abs_nonneg (Real.log Λ)]
  · have := Real.log_le_log (by positivity) (show 1 + Λ ≤ 2 * Λ by linarith)
    rw [Real.log_mul (by norm_num) h.ne'] at this
    linarith [le_abs_self (Real.log Λ)]

/-- `∑ |X_j| ≤ √(card · ∑ X_j²)` (Cauchy–Schwarz). -/
lemma sum_abs_le_sqrt_card_mul_sum_sq {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    ∑ j, |X j| ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ j, X j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |X j|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq_abs] at h
  rw [Real.le_sqrt (Finset.sum_nonneg fun j _ => abs_nonneg _) (by positivity)]
  linarith

/-- `log Λ_j = ∑ᵢ log λ_{jᵢ}`. -/
lemma log_tensorLam (j : Fin K → Fin s) :
    Real.log (tensorLam K s j) = ∑ i, Real.log (lam s (j i)) := by
  unfold tensorLam
  rw [Real.log_prod (fun i _ => (lam_pos (j i)).ne')]

/-- **General spectral bound.**  For `s ≥ 1`,
`log det (I + T_s^{⊗K}) ≤ s^K (log 2 + √(K μ₂ + K(K−1) μ₁²))` with
`μ₁ = log(s+1)/s` the mean and `μ₂ = (1/s) ∑ log² λ` the second log-moment. -/
theorem log_det_one_add_tensorGram_le {s : ℕ} (hs : 1 ≤ s) (K : ℕ) :
    Real.log (1 + tensorGram K s).det
      ≤ (s : ℝ) ^ K * (Real.log 2 + Real.sqrt (K * ((∑ k, Real.log (lam s k) ^ 2) / s)
          + K * (K - 1) * (Real.log (s + 1) / s) ^ 2)) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [det_one_add_tensorGram, Real.log_prod (fun j _ => by linarith [tensorLam_pos (K := K) j])]
  calc ∑ j : Fin K → Fin s, Real.log (1 + tensorLam K s j)
      ≤ ∑ j : Fin K → Fin s, (Real.log 2 + |Real.log (tensorLam K s j)|) :=
        Finset.sum_le_sum fun j _ => log_one_add_le_log_two_add_abs_log (tensorLam_pos j)
    _ = (s : ℝ) ^ K * Real.log 2 + ∑ j : Fin K → Fin s, |∑ i, Real.log (lam s (j i))| := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        simp_rw [log_tensorLam]; push_cast; ring
    _ ≤ (s : ℝ) ^ K * Real.log 2 + Real.sqrt ((Fintype.card (Fin K → Fin s) : ℝ)
          * ∑ j : Fin K → Fin s, (∑ i, Real.log (lam s (j i))) ^ 2) := by
        gcongr; exact sum_abs_le_sqrt_card_mul_sum_sq _
    _ = (s : ℝ) ^ K * Real.log 2 + Real.sqrt (((s : ℝ) ^ K) ^ 2
          * (K * ((∑ k, Real.log (lam s k) ^ 2) / s)
            + K * (K - 1) * (Real.log (s + 1) / s) ^ 2)) := by
        congr 2
        have h := sum_pi_sq (fun k => Real.log (lam s k)) K
        rw [sum_log_lam] at h
        simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        have hs2 : (s : ℝ) ^ 2 ≠ 0 := by positivity
        rw [show (s : ℝ) ^ K * ∑ j : Fin K → Fin s, (∑ i, Real.log (lam s (j i))) ^ 2
            = (s : ℝ) ^ K * ((s : ℝ) ^ 2 * ∑ j : Fin K → Fin s, (∑ i, Real.log (lam s (j i))) ^ 2)
              / (s : ℝ) ^ 2 by field_simp, h]
        field_simp
        ring
    _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; ring

/-- **The `O(r√K)` bound at `s = K²`:**
`log det (I + T_{K²}^{⊗K}) ≤ (K²)^K (log 2 + 23 √K)`. -/
theorem log_det_one_add_tensorGram_le' {K : ℕ} (hK : 1 ≤ K) :
    Real.log (1 + tensorGram K (K ^ 2)).det
      ≤ ((K : ℝ) ^ 2) ^ K * (Real.log 2 + 23 * Real.sqrt K) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
  have h := log_det_one_add_tensorGram_le hs K
  push_cast at h
  refine h.trans ?_
  gcongr
  -- `√(K μ₂ + K(K−1) μ₁²) ≤ 23 √K` from `μ₂ ≤ 520` and `K(K−1) μ₁² ≤ 4`
  have hμ₂ : (∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2 ≤ 520 := by
    rw [div_le_iff₀ (by positivity)]
    have := sum_sq_log_lam_le' hs
    push_cast at this
    linarith
  have hμ₁ : (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2 ≤ 4 := by
    have hlog : Real.log ((K : ℝ) ^ 2 + 1) ≤ 2 * K := by
      have h1 : Real.log ((K : ℝ) ^ 2 + 1) ≤ Real.log (((K : ℝ) + 1) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at h1
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 1 by positivity)
      push_cast at h1
      linarith
    have hl0 : 0 ≤ Real.log ((K : ℝ) ^ 2 + 1) := Real.log_nonneg (by nlinarith)
    have hKK : (K : ℝ) * (K - 1) ≤ (K : ℝ) ^ 2 := by nlinarith
    calc (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2
        ≤ (K : ℝ) ^ 2 * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (Real.log ((K : ℝ) ^ 2 + 1) / K) ^ 2 := by field_simp
      _ ≤ 2 ^ 2 := by
          gcongr
          rw [div_le_iff₀ (by positivity)]; linarith
      _ = 4 := by norm_num
  have hin : (K : ℝ) * ((∑ k, Real.log (lam (K ^ 2) k) ^ 2) / (K : ℝ) ^ 2)
      + (K : ℝ) * (K - 1) * (Real.log ((K : ℝ) ^ 2 + 1) / (K : ℝ) ^ 2) ^ 2 ≤ 23 ^ 2 * K := by
    nlinarith [mul_le_mul_of_nonneg_left hμ₂ (by positivity : (0 : ℝ) ≤ K)]
  calc Real.sqrt _ ≤ Real.sqrt (23 ^ 2 * K) := Real.sqrt_le_sqrt hin
    _ = 23 * Real.sqrt K := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]


/-! ### The difference matrix `D_s` and `A = D_s^{⊗K}` with `A Aᵀ = T_s^{⊗K}` -/

/-- The `s × (s+1)` adjacent-difference matrix: row `a` is `e_a − e_{a+1}`. -/
def diff (s : ℕ) : Matrix (Fin s) (Fin (s + 1)) ℝ :=
  fun a => Pi.single a.castSucc (1 : ℝ) - Pi.single a.succ 1

lemma diff_dotProduct_diff (s : ℕ) (a b : Fin s) : diff s a ⬝ᵥ diff s b = gram s a b := by
  simp only [diff, dotProduct_sub, dotProduct_single, Pi.sub_apply, Pi.single_apply, mul_one,
    gram, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

theorem diff_mul_transpose (s : ℕ) : diff s * (diff s)ᵀ = gram s := by
  ext a b
  rw [Matrix.mul_apply]
  exact diff_dotProduct_diff s a b

/-- `A = D_s^{⊗K}`, indexed by `(Fin K → Fin s) × (Fin K → Fin (s+1))`. -/
def tensorDiff (K s : ℕ) : Matrix (Fin K → Fin s) (Fin K → Fin (s + 1)) ℝ :=
  fun a c => ∏ i, diff s (a i) (c i)

theorem tensorDiff_mul_transpose (K s : ℕ) :
    tensorDiff K s * (tensorDiff K s)ᵀ = tensorGram K s := by
  ext a b
  simp only [Matrix.mul_apply, transpose_apply, tensorDiff, tensorGram]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i c => diff s (a i) c * diff s (b i) c)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact diff_dotProduct_diff s (a i) (b i)


end NormalNumbers.G4
