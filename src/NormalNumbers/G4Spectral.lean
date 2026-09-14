/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# G4 disjunctivity, §4B (spectral half): the adjacent-difference Gram matrix

The zonotope/ellipsoid tube bound of draft §5 rests on

  `log det(I + AAᵀ) = O(r√K)`,   `A = D_s^{⊗K}`,

which in turn rests on the spectrum of the one-dimensional Gram matrix `T_s = D_s D_sᵀ`
(the `s × s` tridiagonal `(−1, 2, −1)` matrix):

* `det T_s = s + 1` (`det_gram`), proved by the explicit `L D Lᵀ` factorisation with unit
  lower-bidiagonal `L` (subdiagonal `−k/(k+1)`) and `D = diag((k+2)/(k+1))`;
* the sine eigenvectors `v_j(k) = sin(π(j+1)(k+1)/(s+1))` with eigenvalues
  `λ_j = 2 − 2cos(π(j+1)/(s+1)) = 4 sin²(π(j+1)/(2(s+1)))` (`gram_mulVec_sineVec`);
* the eigenvalues are distinct and positive, the eigenvectors nonzero and (by symmetry of `T_s`)
  pairwise orthogonal.

The tensor-power step and the log-moment bound follow in the same file once these are in place.
-/

open Matrix Finset Real
open scoped BigOperators

namespace NormalNumbers.G4

/-! ### The Gram matrix and its `L D Lᵀ` factorisation -/

/-- The `s × s` Gram matrix `D_s D_sᵀ` of the adjacent-difference operator:
`2` on the diagonal, `−1` on the two neighbouring diagonals. -/
def gram (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun a b => if a = b then 2 else if (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a then -1 else 0

/-- Unit lower-bidiagonal factor: `L a (a-1) = −a/(a+1)`. -/
noncomputable def gramL (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun a c => if a = c then 1 else if (c : ℕ) + 1 = a then -((c : ℝ) + 1) / ((c : ℝ) + 2) else 0

/-- Diagonal factor `D a = (a+2)/(a+1)`. -/
noncomputable def gramD (s : ℕ) : Fin s → ℝ := fun a => ((a : ℝ) + 2) / ((a : ℝ) + 1)

lemma gramL_isLowerTriangular (s : ℕ) : (gramL s).IsLowerTriangular := by
  intro i j hij
  simp only [OrderDual.toDual_lt_toDual] at hij
  unfold gramL
  rw [if_neg (ne_of_gt hij).symm, if_neg]
  intro h
  have := Fin.lt_def.mp hij
  omega

lemma det_gramL (s : ℕ) : (gramL s).det = 1 := by
  rw [det_of_isLowerTriangular _ (gramL_isLowerTriangular s)]
  simp [gramL]

lemma prod_gramD (s : ℕ) : ∏ a, gramD s a = s + 1 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    have : (∏ a : Fin n, gramD (n + 1) a.castSucc) = ∏ a : Fin n, gramD n a := by
      refine Finset.prod_congr rfl fun a _ => ?_
      simp [gramD]
    rw [this, ih]
    simp only [gramD, Fin.val_last]
    push_cast
    field_simp
    ring

lemma gramL_mul_diagonal (s : ℕ) :
    gramL s * diagonal (gramD s) = fun a c => gramL s a c * gramD s c := by
  ext a c; exact mul_diagonal _ _ _ _

/-- The summand of `(L D Lᵀ)_{ab}`. -/
noncomputable def ldlSummand (s : ℕ) (a b c : Fin s) : ℝ := gramL s a c * gramD s c * gramL s b c

lemma ldlSummand_eq_zero {s : ℕ} {a b c : Fin s} (hca : c ≠ a) (hcb : c ≠ b)
    (h : ¬ ((c : ℕ) + 1 = a ∧ (c : ℕ) + 1 = b)) : ldlSummand s a b c = 0 := by
  unfold ldlSummand gramL
  rw [if_neg hca.symm, if_neg hcb.symm]
  by_cases h1 : (c : ℕ) + 1 = a
  · rw [if_pos h1, if_neg (fun h2 => h ⟨h1, h2⟩)]; ring
  · rw [if_neg h1]; ring

/-- The factorisation `T = L D Lᵀ`, entrywise. -/
lemma ldl_apply (s : ℕ) (a b : Fin s) :
    (gramL s * diagonal (gramD s) * (gramL s)ᵀ) a b = ∑ c, ldlSummand s a b c := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_diagonal, transpose_apply]
  rfl

lemma gram_eq_LDLt (s : ℕ) : gram s = gramL s * diagonal (gramD s) * (gramL s)ᵀ := by
  ext a b
  rw [ldl_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : (a : ℕ) = 0
    · -- only `c = a` contributes
      rw [Finset.sum_eq_single a]
      · unfold ldlSummand gramL gramD gram
        simp [ha]
      · intro c _ hc
        exact ldlSummand_eq_zero hc hc (by omega)
      · simp
    · -- `c = a` and `c = a − 1` contribute
      have hlt : (a : ℕ) - 1 < s := by omega
      set a' : Fin s := ⟨(a : ℕ) - 1, hlt⟩ with ha'
      have hne : a ≠ a' := by
        intro h; rw [Fin.ext_iff] at h; simp [ha'] at h; omega
      rw [Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
      · unfold ldlSummand gramL gramD gram
        have h1 : (a' : ℕ) + 1 = a := by simp [ha']; omega
        simp only [if_true, if_neg hne, h1]
        have : ((a : ℕ) : ℝ) = ((a' : ℕ) : ℝ) + 1 := by
          rw [ha']; simp; push_cast [Nat.cast_sub (by omega : 1 ≤ (a : ℕ))]; ring
        rw [this]
        have hpos : ((a' : ℕ) : ℝ) + 1 ≠ 0 := by positivity
        have hpos2 : ((a' : ℕ) : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
      · intro c _ hc
        refine ldlSummand_eq_zero hc.1 hc.1 ?_
        rintro ⟨h1, -⟩
        apply hc.2
        rw [Fin.ext_iff, ha']; simp; omega
  · -- off-diagonal: at most one contributing term
    have hno : ∀ c : Fin s, ¬ ((c : ℕ) + 1 = a ∧ (c : ℕ) + 1 = b) := by
      rintro c ⟨h1, h2⟩; exact hab (Fin.ext (by omega))
    by_cases h1 : (a : ℕ) + 1 = b
    · -- `c = a`
      rw [Finset.sum_eq_single a]
      · unfold ldlSummand gramL gramD gram
        simp [hab, Ne.symm hab, h1]
        have hpos : ((a : ℕ) : ℝ) + 1 ≠ 0 := by positivity
        have hpos2 : ((a : ℕ) : ℝ) + 2 ≠ 0 := by positivity
        field_simp
        ring
      · intro c _ hc
        by_cases hcb : c = b
        · subst hcb
          have : ¬ ((c : ℕ) + 1 = a) := by omega
          simp [ldlSummand, gramL, Ne.symm hc, this]
        · exact ldlSummand_eq_zero hc hcb (hno c)
      · simp
    · by_cases h2 : (b : ℕ) + 1 = a
      · -- `c = b`
        rw [Finset.sum_eq_single b]
        · unfold ldlSummand gramL gramD gram
          simp [hab, h2]
          have hpos : ((b : ℕ) : ℝ) + 1 ≠ 0 := by positivity
          have hpos2 : ((b : ℕ) : ℝ) + 2 ≠ 0 := by positivity
          field_simp
          ring
        · intro c _ hc
          by_cases hca : c = a
          · subst hca
            have : ¬ ((c : ℕ) + 1 = b) := by omega
            simp [ldlSummand, gramL, Ne.symm hab, this]
          · exact ldlSummand_eq_zero hca hc (hno c)
        · simp
      · rw [Finset.sum_eq_zero]
        · unfold gram
          rw [if_neg hab, if_neg (by tauto)]
        · intro c _
          by_cases hca : c = a
          · subst hca
            simp [ldlSummand, gramL, hab, Ne.symm hab, h1]
          · by_cases hcb : c = b
            · subst hcb
              simp [ldlSummand, gramL, hab, Ne.symm hab, h2]
            · exact ldlSummand_eq_zero hca hcb (hno c)

/-- **`det T_s = s + 1`.** -/
theorem det_gram (s : ℕ) : (gram s).det = s + 1 := by
  rw [gram_eq_LDLt, det_mul, det_mul, det_gramL, det_transpose, det_gramL, det_diagonal,
    prod_gramD]
  ring

/-! ### Sine eigenvectors -/

/-- The three-term shape of a row of `gram`. -/
lemma gram_apply_eq (s : ℕ) (k c : Fin s) :
    gram s k c = 2 * (if c = k then 1 else 0) - (if (k : ℕ) + 1 = c then 1 else 0)
      - (if (c : ℕ) + 1 = k then 1 else 0) := by
  unfold gram
  by_cases hck : c = k
  · subst hck; simp
  · have hkc : k ≠ c := Ne.symm hck
    rw [if_neg hkc, if_neg hck]
    by_cases h1 : (k : ℕ) + 1 = c
    · have h2 : ¬ ((c : ℕ) + 1 = k) := by omega
      simp [h1, h2]
    · by_cases h2 : (c : ℕ) + 1 = k
      · simp [h1, h2]
      · simp [h1, h2]

lemma sum_ite_succ {s : ℕ} (k : Fin s) (v : Fin s → ℝ) :
    ∑ c : Fin s, (if (k : ℕ) + 1 = c then v c else 0) =
      if h : (k : ℕ) + 1 < s then v ⟨(k : ℕ) + 1, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(k : ℕ) + 1, h⟩]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro h'; apply hc; ext; simp [← h']
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro h'
    exact h (h' ▸ c.isLt)

lemma sum_ite_pred {s : ℕ} (k : Fin s) (v : Fin s → ℝ) :
    ∑ c : Fin s, (if (c : ℕ) + 1 = k then v c else 0) =
      if h : 0 < (k : ℕ) then v ⟨(k : ℕ) - 1, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(k : ℕ) - 1, by omega⟩]
    · simp only
      rw [if_pos (by omega)]
    · intro c _ hc
      rw [if_neg]
      intro h'; apply hc; ext; simp; omega
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    omega

/-- `(T v)_k = 2 v_k − v_{k+1} − v_{k−1}` with the boundary terms read as `0`. -/
lemma gram_mulVec_apply {s : ℕ} (v : Fin s → ℝ) (k : Fin s) :
    (gram s).mulVec v k = 2 * v k
      - (if h : (k : ℕ) + 1 < s then v ⟨(k : ℕ) + 1, h⟩ else 0)
      - (if h : 0 < (k : ℕ) then v ⟨(k : ℕ) - 1, by omega⟩ else 0) := by
  rw [← sum_ite_succ, ← sum_ite_pred]
  simp only [Matrix.mulVec, dotProduct, gram_apply_eq]
  simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The angle `θ_j = π (j+1)/(s+1)`. -/
noncomputable def angle (s : ℕ) (j : Fin s) : ℝ := π * ((j : ℝ) + 1) / ((s : ℝ) + 1)

/-- The eigenvalue `λ_j = 2 − 2 cos θ_j = 4 sin²(θ_j/2)`. -/
noncomputable def lam (s : ℕ) (j : Fin s) : ℝ := 2 - 2 * Real.cos (angle s j)

/-- The sine eigenvector `v_j(k) = sin((k+1) θ_j)`. -/
noncomputable def sineVec (s : ℕ) (j : Fin s) : Fin s → ℝ :=
  fun k => Real.sin (((k : ℝ) + 1) * angle s j)

lemma angle_pos {s : ℕ} (j : Fin s) : 0 < angle s j := by
  unfold angle; positivity

lemma angle_lt_pi {s : ℕ} (j : Fin s) : angle s j < π := by
  unfold angle
  rw [div_lt_iff₀ (by positivity)]
  have : ((j : ℝ) + 1) < (s : ℝ) + 1 := by
    have := j.isLt; exact_mod_cast Nat.succ_lt_succ this
  nlinarith [Real.pi_pos]

lemma angle_strictMono {s : ℕ} {j j' : Fin s} (h : j < j') : angle s j < angle s j' := by
  unfold angle
  have : ((j : ℝ) + 1) < (j' : ℝ) + 1 := by
    have := Fin.lt_def.mp h; exact_mod_cast Nat.succ_lt_succ this
  have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  rw [div_lt_div_iff_of_pos_right hs]
  nlinarith [Real.pi_pos]

lemma lam_pos {s : ℕ} (j : Fin s) : 0 < lam s j := by
  unfold lam
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (angle_lt_pi j).le (angle_pos j)
  rw [Real.cos_zero] at this
  linarith

lemma lam_le_four {s : ℕ} (j : Fin s) : lam s j ≤ 4 := by
  unfold lam; linarith [Real.neg_one_le_cos (angle s j)]

lemma lam_strictMono {s : ℕ} {j j' : Fin s} (h : j < j') : lam s j < lam s j' := by
  unfold lam
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (angle_pos j).le (angle_lt_pi j').le
    (angle_strictMono h)
  linarith

lemma lam_injective (s : ℕ) : Function.Injective (lam s) := by
  intro j j' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (lam_strictMono hlt).ne
  · exact absurd h (lam_strictMono hlt).ne'

/-- The extended sine sequence vanishes at `m = 0` and `m = s + 1`. -/
lemma sin_angle_succ_s {s : ℕ} (j : Fin s) : Real.sin (((s : ℝ) + 1) * angle s j) = 0 := by
  unfold angle
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  rw [show ((s : ℝ) + 1) * (π * ((j : ℝ) + 1) / ((s : ℝ) + 1)) = ((j : ℕ) + 1 : ℕ) * π by
    push_cast; field_simp]
  exact Real.sin_nat_mul_pi _

lemma sineVec_succ {s : ℕ} (j k : Fin s) :
    (if h : (k : ℕ) + 1 < s then sineVec s j ⟨(k : ℕ) + 1, h⟩ else 0)
      = Real.sin ((((k : ℝ) + 1) + 1) * angle s j) := by
  split_ifs with h
  · simp [sineVec]
  · have hk : (k : ℕ) + 1 = s := by have := k.isLt; omega
    have hk' : (((k : ℝ) + 1) + 1) = (s : ℝ) + 1 := by
      have := congrArg (Nat.cast (R := ℝ)) hk
      push_cast at this
      linarith
    rw [hk']
    exact (sin_angle_succ_s j).symm

lemma sineVec_pred {s : ℕ} (j k : Fin s) :
    (if h : 0 < (k : ℕ) then sineVec s j ⟨(k : ℕ) - 1, by omega⟩ else 0)
      = Real.sin ((((k : ℝ) + 1) - 1) * angle s j) := by
  split_ifs with h
  · simp only [sineVec]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ (k : ℕ))]
    push_cast; ring
  · have hk : (k : ℕ) = 0 := by omega
    simp [hk]

/-- **Eigenvector equation** `T v_j = λ_j v_j`. -/
theorem gram_mulVec_sineVec (s : ℕ) (j : Fin s) :
    (gram s).mulVec (sineVec s j) = lam s j • sineVec s j := by
  funext k
  rw [gram_mulVec_apply, sineVec_succ, sineVec_pred]
  simp only [Pi.smul_apply, smul_eq_mul, sineVec, lam]
  have key : ∀ m θ : ℝ, 2 * Real.sin m - Real.sin (m + θ) - Real.sin (m - θ)
      = (2 - 2 * Real.cos θ) * Real.sin m := by
    intro m θ; rw [Real.sin_add, Real.sin_sub]; ring
  rw [show (((k : ℝ) + 1) + 1) * angle s j = ((k : ℝ) + 1) * angle s j + angle s j by ring,
    show (((k : ℝ) + 1) - 1) * angle s j = ((k : ℝ) + 1) * angle s j - angle s j by ring]
  exact key _ _

/-- `gram` is symmetric. -/
lemma gram_transpose (s : ℕ) : (gram s)ᵀ = gram s := by
  ext a b
  rw [transpose_apply]
  simp only [gram]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]
    simp only [or_comm]

/-- Eigenvectors of the symmetric `gram` for distinct eigenvalues are orthogonal. -/
theorem sineVec_orthogonal (s : ℕ) {j j' : Fin s} (h : j ≠ j') :
    sineVec s j ⬝ᵥ sineVec s j' = 0 := by
  have h1 : sineVec s j ⬝ᵥ (gram s).mulVec (sineVec s j') = lam s j' * (sineVec s j ⬝ᵥ sineVec s j') := by
    rw [gram_mulVec_sineVec, dotProduct_smul, smul_eq_mul]
  have h2 : sineVec s j ⬝ᵥ (gram s).mulVec (sineVec s j') = lam s j * (sineVec s j ⬝ᵥ sineVec s j') := by
    rw [dotProduct_mulVec, ← mulVec_transpose, gram_transpose, gram_mulVec_sineVec, smul_dotProduct,
      smul_eq_mul]
  have hne : lam s j - lam s j' ≠ 0 := sub_ne_zero.mpr (fun e => h (lam_injective s e))
  have : (lam s j - lam s j') * (sineVec s j ⬝ᵥ sineVec s j') = 0 := by
    rw [sub_mul, ← h2, ← h1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

lemma sineVec_apply_zero_pos {s : ℕ} (j : Fin s) (k : Fin s) (hk : (k : ℕ) = 0) :
    0 < sineVec s j k := by
  unfold sineVec
  rw [hk]
  simp only [Nat.cast_zero, zero_add, one_mul]
  exact Real.sin_pos_of_pos_of_lt_pi (angle_pos j) (angle_lt_pi j)

lemma sineVec_self_pos {s : ℕ} (j : Fin s) : 0 < sineVec s j ⬝ᵥ sineVec s j := by
  have hs : 0 < s := Nat.pos_of_ne_zero (fun h => by subst h; exact j.elim0)
  unfold dotProduct
  refine (Finset.sum_pos' (fun k _ => mul_self_nonneg _) ⟨⟨0, hs⟩, Finset.mem_univ _, ?_⟩)
  have := sineVec_apply_zero_pos j ⟨0, hs⟩ rfl
  positivity


/-! ### Log moments of the one-dimensional spectrum

`λ_j = 4 sin²(θ_j/2) ≥ 4 ((j+1)/(s+1))²` (Jordan), so `|log λ_j| ≤ log 4 + 2 log((s+1)/(j+1))`,
and `∑_j log²((s+1)/(j+1)) ≤ 32 (s+1)` via `log² y ≤ 16 √y` and `∑_{m ≤ s} m^{-1/2} ≤ 2√s`.
Hence `∑_j log² λ_j ≤ 520 s`: the second log-moment of the spectrum is `O(s)`, which is what makes
the tensor-power bound `O(r√K)` rather than `O(rK)`. -/

lemma lam_eq_four_mul_sin_sq {s : ℕ} (j : Fin s) :
    lam s j = 4 * Real.sin (angle s j / 2) ^ 2 := by
  unfold lam
  have := Real.cos_two_mul_eq_one_sub (angle s j / 2)
  rw [show 2 * (angle s j / 2) = angle s j by ring] at this
  rw [this]; ring

/-- Jordan's inequality gives the lower bound `λ_j ≥ 4 ((j+1)/(s+1))²`. -/
lemma lam_ge {s : ℕ} (j : Fin s) : 4 * (((j : ℝ) + 1) / ((s : ℝ) + 1)) ^ 2 ≤ lam s j := by
  rw [lam_eq_four_mul_sin_sq]
  have h0 : 0 ≤ angle s j / 2 := by linarith [angle_pos j]
  have hle : angle s j / 2 ≤ π / 2 := by linarith [angle_lt_pi j]
  have hj := Real.mul_le_sin h0 hle
  have : 2 / π * (angle s j / 2) = ((j : ℝ) + 1) / ((s : ℝ) + 1) := by
    unfold angle; field_simp
  rw [this] at hj
  have hnn : 0 ≤ ((j : ℝ) + 1) / ((s : ℝ) + 1) := by positivity
  have := pow_le_pow_left₀ hnn hj 2
  linarith

lemma one_le_ratio {s : ℕ} (j : Fin s) : 1 ≤ ((s : ℝ) + 1) / ((j : ℝ) + 1) := by
  rw [le_div_iff₀ (by positivity)]
  have := j.isLt
  have : ((j : ℕ) : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast this
  linarith

lemma log_lam_le {s : ℕ} (j : Fin s) : Real.log (lam s j) ≤ Real.log 4 :=
  Real.log_le_log (lam_pos j) (lam_le_four j)

lemma log_lam_ge {s : ℕ} (j : Fin s) :
    Real.log 4 - 2 * Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ≤ Real.log (lam s j) := by
  have h := Real.log_le_log (by positivity) (lam_ge j)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_div (by positivity) (by positivity)] at h
  rw [Real.log_div (by positivity) (by positivity)]
  push_cast at h
  linarith

lemma sq_log_lam_le {s : ℕ} (j : Fin s) :
    Real.log (lam s j) ^ 2
      ≤ 2 * Real.log 4 ^ 2 + 8 * Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 2 := by
  have ha : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hb : 0 ≤ Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) := Real.log_nonneg (one_le_ratio j)
  have h1 := log_lam_le j
  have h2 := log_lam_ge j
  set a := Real.log 4
  set b := Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1))
  set x := Real.log (lam s j)
  have hx1 : x ≤ a + 2 * b := by linarith
  have hx2 : -(a + 2 * b) ≤ x := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hx2), sq_nonneg (a - 2 * b)]

/-- `log² y ≤ 16 √y` for `y ≥ 1` (via `log y = 4 log y^{1/4} ≤ 4 y^{1/4}`). -/
lemma sq_log_le_sixteen_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 16 * Real.sqrt y := by
  have h0 : 0 ≤ y := by linarith
  have h1 : Real.log y = 4 * Real.log (Real.sqrt (Real.sqrt y)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt h0]; ring
  have hq : 1 ≤ Real.sqrt (Real.sqrt y) := by
    have : 1 ≤ Real.sqrt y := (Real.le_sqrt zero_le_one h0).mpr (by rw [one_pow]; exact hy)
    exact (Real.le_sqrt zero_le_one (Real.sqrt_nonneg _)).mpr (by rw [one_pow]; exact this)
  have h2 : Real.log (Real.sqrt (Real.sqrt y)) ≤ Real.sqrt (Real.sqrt y) := by
    have := Real.log_le_sub_one_of_pos (x := Real.sqrt (Real.sqrt y)) (by linarith)
    linarith
  have h3 : 0 ≤ Real.log (Real.sqrt (Real.sqrt y)) := Real.log_nonneg hq
  have h4 : Real.log (Real.sqrt (Real.sqrt y)) ^ 2 ≤ Real.sqrt (Real.sqrt y) ^ 2 :=
    pow_le_pow_left₀ h3 h2 2
  rw [Real.sq_sqrt (Real.sqrt_nonneg y)] at h4
  rw [h1, mul_pow]
  linarith

/-- `∑_{m=1}^{s} m^{-1/2} ≤ 2 √s`. -/
lemma sum_inv_sqrt_le (s : ℕ) :
    ∑ k ∈ Finset.range s, 1 / Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt s := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : 1 / Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt n := by
      have hp : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
      have hsq1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
      rw [div_le_iff₀ hp]
      nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n), Real.sqrt_nonneg (n : ℝ)]
    push_cast
    linarith

lemma sum_sq_log_ratio_le (s : ℕ) :
    ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 2 ≤ 32 * ((s : ℝ) + 1) := by
  calc ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 2
      ≤ ∑ j : Fin s, 16 * Real.sqrt (((s : ℝ) + 1) / ((j : ℝ) + 1)) :=
        Finset.sum_le_sum fun j _ => sq_log_le_sixteen_sqrt (one_le_ratio j)
    _ = 16 * Real.sqrt ((s : ℝ) + 1) * ∑ k ∈ Finset.range s, 1 / Real.sqrt ((k : ℝ) + 1) := by
        rw [Finset.mul_sum, Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.sqrt_div (by positivity)]; ring
    _ ≤ 16 * Real.sqrt ((s : ℝ) + 1) * (2 * Real.sqrt s) := by
        gcongr; exact sum_inv_sqrt_le s
    _ ≤ 32 * ((s : ℝ) + 1) := by
        have := Real.sqrt_le_sqrt (show (s : ℝ) ≤ s + 1 by linarith)
        have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ s + 1 by positivity)
        nlinarith [Real.sqrt_nonneg (s : ℝ), Real.sqrt_nonneg ((s : ℝ) + 1)]

/-- Second log-moment of the spectrum: `∑_j log² λ_j ≤ 2 s log² 4 + 256 (s+1)`. -/
theorem sum_sq_log_lam_le (s : ℕ) :
    ∑ j : Fin s, Real.log (lam s j) ^ 2 ≤ 2 * s * Real.log 4 ^ 2 + 256 * ((s : ℝ) + 1) := by
  calc ∑ j : Fin s, Real.log (lam s j) ^ 2
      ≤ ∑ j : Fin s, (2 * Real.log 4 ^ 2 + 8 * Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 2) :=
        Finset.sum_le_sum fun j _ => sq_log_lam_le j
    _ = 2 * s * Real.log 4 ^ 2
          + 8 * ∑ j : Fin s, Real.log (((s : ℝ) + 1) / ((j : ℝ) + 1)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        ring
    _ ≤ _ := by linarith [sum_sq_log_ratio_le s]

lemma log_four_lt_two : Real.log 4 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have := Real.exp_one_gt_d9
  nlinarith

/-- Clean form: `∑_j log² λ_j ≤ 520 s` for `s ≥ 1`. -/
theorem sum_sq_log_lam_le' {s : ℕ} (hs : 1 ≤ s) :
    ∑ j : Fin s, Real.log (lam s j) ^ 2 ≤ 520 * s := by
  have h4 := log_four_lt_two
  have := sum_sq_log_lam_le s
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsq : Real.log 4 ^ 2 ≤ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * s)]


end NormalNumbers.G4
