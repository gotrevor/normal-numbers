/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitPQ

open Polynomial

namespace NormalNumbers.ExplicitPQ

open ExplicitSquare ExplicitOmegaK OmegaKApprox PQGrid

/-! ### Exact grid inverse of `Q` on the branch -/

section Grid

variable (Q : ℤ[X]) (u : ℕ)

/-- The sign of `c`. -/
noncomputable def sgnQ : ℤ := if 0 ≤ cQ Q u then 1 else -1

/-- Coefficient list of `σ Q`. -/
noncomputable def lR : List ℤ := (List.range (Q.natDegree + 1)).map fun j => sgnQ Q u * Q.coeff j

theorem polyOfList_smul_coeffs (p : ℤ[X]) (s : ℤ) :
    polyOfList ((List.range (p.natDegree + 1)).map fun j => s * p.coeff j) = C s * p := by
  ext j
  rw [coeff_polyOfList, coeff_C_mul]
  by_cases hj : j < p.natDegree + 1
  · simp [List.getD_eq_getElem?_getD, hj]
  · rw [getD_eq_zero_of_le (by simp; omega), coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

theorem aeval_lR (x : ℝ) : aeval x (polyOfList (lR Q u)) = (sgnQ Q u : ℝ) * aeval x Q := by
  rw [lR, polyOfList_smul_coeffs]; simp

/-- `(σ a)⁺`, `(σ a)⁻`, `|c|`. -/
noncomputable def apQ : ℕ := (sgnQ Q u * aQ Q u).toNat
noncomputable def amQ : ℕ := (-(sgnQ Q u * aQ Q u)).toNat
noncomputable def cnQ : ℕ := (cQ Q u).natAbs

/-- The grid test `σ Q(N/2^T) ≤ σ(a + c · yN q / 2^{2|q|+1})`, `N = (u+1) 2^T + j`, in `ℕ`. -/
noncomputable def gC (T : ℕ) (q : List Bool) (j : ℕ) : Prop :=
  evP (lR Q u) ((u + 1) * 2 ^ T + j) T * 2 ^ (2 * q.length + 1) +
      2 ^ (T * (lR Q u).length) * amQ Q u * 2 ^ (2 * q.length + 1) ≤
    evM (lR Q u) ((u + 1) * 2 ^ T + j) T * 2 ^ (2 * q.length + 1) +
      2 ^ (T * (lR Q u).length) * (apQ Q u * 2 ^ (2 * q.length + 1) + cnQ Q u * yN q)

noncomputable instance (T : ℕ) (q : List Bool) : DecidablePred (gC Q u T q) := fun j => by
  unfold gC; infer_instance

theorem sgnQ_mul_cQ : ((sgnQ Q u : ℤ) : ℝ) * (cQ Q u : ℝ) = (cnQ Q u : ℝ) := by
  unfold sgnQ cnQ
  split_ifs with h
  · rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h)]; simp
  · push Not at h
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]; push_cast; ring

theorem gC_iff (T : ℕ) (q : List Bool) (j : ℕ) :
    gC Q u T q j ↔ (sgnQ Q u : ℝ) * aeval ((((u + 1) * 2 ^ T + j : ℕ) : ℝ) / 2 ^ T) Q ≤
      (sgnQ Q u : ℝ) * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * ((yN q : ℝ) / 2 ^ (2 * q.length + 1))) := by
  set N := (u + 1) * 2 ^ T + j
  have hev := evP_sub_evM (lR Q u) N T
  rw [aeval_lR] at hev
  have hapm : ((apQ Q u : ℕ) : ℝ) - (amQ Q u : ℝ) = (sgnQ Q u : ℝ) * (aQ Q u : ℝ) := by
    have h := congrArg (Int.cast (R := ℝ)) (Int.toNat_sub_toNat_neg (sgnQ Q u * aQ Q u))
    push_cast at h; unfold apQ amQ; rw [← h]
  have hc := sgnQ_mul_cQ Q u
  set E : ℝ := 2 ^ (T * (lR Q u).length)
  set F : ℝ := 2 ^ (2 * q.length + 1)
  have hE : 0 < E := by positivity
  have hF : 0 < F := by positivity
  unfold gC
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  rw [← sub_nonneg, ← sub_nonneg (a := (sgnQ Q u : ℝ) * _)]
  have key : (evM (lR Q u) N T : ℝ) * F + E * (apQ Q u * F + cnQ Q u * yN q) -
      ((evP (lR Q u) N T : ℝ) * F + E * amQ Q u * F) =
      E * F * ((sgnQ Q u : ℝ) * ((aQ Q u : ℝ) + (cQ Q u : ℝ) * ((yN q : ℝ) / F)) -
        (sgnQ Q u : ℝ) * aeval ((N : ℝ) / 2 ^ T) Q) := by
    have hYF : (yN q : ℝ) / F * F = yN q := div_mul_cancel₀ _ hF.ne'
    linear_combination (-F) * hev + E * F * hapm - E * (yN q : ℝ) * hc
      - E * (sgnQ Q u : ℝ) * (cQ Q u : ℝ) * hYF
  rw [key]
  exact mul_nonneg_iff_of_pos_left (by positivity)

theorem cQ_real : (cQ Q u : ℝ) = 2 * (aeval ((u : ℝ) + 2) Q - aeval ((u : ℝ) + 1) Q) := by
  simp only [cQ]; push_cast
  rw [aeval_intCast_eq, aeval_intCast_eq]; push_cast; ring

variable {Q u}

/-- `σ Q` is expanding on `[u, ∞)` with `σ = sgnQ`. -/
theorem sgn_expand (hu : IsBranch Q u) : ∀ s t : ℝ, (u : ℝ) ≤ s → s ≤ t →
    t - s ≤ (sgnQ Q u : ℝ) * aeval t Q - (sgnQ Q u : ℝ) * aeval s Q := by
  obtain ⟨σ, hσ, hexp⟩ := branch_expand hu
  have h1 := hexp ((u : ℝ) + 1) ((u : ℝ) + 2) (by linarith) (by linarith)
  have hc := cQ_real Q u
  suffices (sgnQ Q u : ℝ) = σ by rw [this]; exact hexp
  unfold sgnQ
  rcases hσ with rfl | rfl
  · rw [if_pos]; · simp
    have : (0 : ℝ) ≤ cQ Q u := by rw [hc]; linarith
    exact_mod_cast this
  · rw [if_neg]; · simp
    have : (cQ Q u : ℝ) < 0 := by rw [hc]; linarith
    intro h; have : (0 : ℝ) ≤ cQ Q u := by exact_mod_cast h
    linarith

theorem sgn_le_iff (hu : IsBranch Q u) {s t : ℝ} (hs : (u : ℝ) ≤ s) (ht : (u : ℝ) ≤ t) :
    (sgnQ Q u : ℝ) * aeval s Q ≤ (sgnQ Q u : ℝ) * aeval t Q ↔ s ≤ t := by
  constructor
  · intro h; by_contra h'; push Not at h'
    have := sgn_expand hu t s ht h'.le; linarith
  · intro h; have := sgn_expand hu s t hs h; linarith

/-- The grid point count. -/
noncomputable def gN (T : ℕ) (q : List Bool) : ℕ := (u + 1) * 2 ^ T + gcount (gC Q u T q) (2 ^ T)

/-- **Grid bracket**: `gN/2^T ≤ Q⁻¹(a + c y_lo) < gN/2^T + 2^{-T}`. -/
theorem grid_bracket (hu : IsBranch Q u) (T : ℕ) (q : List Bool)
    (hq : (yN q : ℝ) / 2 ^ (2 * q.length + 1) ∈ Set.Icc (1 / 2 : ℝ) 1) :
    ((gN (Q := Q) (u := u) T q : ℕ) : ℝ) / 2 ^ T ≤ Xf Q u ((yN q : ℝ) / 2 ^ (2 * q.length + 1)) ∧
      Xf Q u ((yN q : ℝ) / 2 ^ (2 * q.length + 1)) <
        ((gN (Q := Q) (u := u) T q : ℕ) : ℝ) / 2 ^ T + (1 / 2) ^ T := by
  set ylo := (yN q : ℝ) / 2 ^ (2 * q.length + 1)
  set xlo := Xf Q u ylo
  have hm := Xf_mem_Icc hu hq
  have hsp := (Xf_spec (window_sub_Vset hu hq)).2
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  set z : ℝ := (xlo - u - 1) * 2 ^ T
  have hz0 : 0 ≤ z := mul_nonneg (by linarith [hm.1]) hT.le
  have hz1 : z ≤ 2 ^ T := by
    have : xlo - u - 1 ≤ 1 := by linarith [hm.2]
    nlinarith
  have hC : ∀ j, gC Q u T q j ↔ (j : ℝ) ≤ z := by
    intro j
    rw [gC_iff, ← hsp]
    have hp : (((u + 1) * 2 ^ T + j : ℕ) : ℝ) / 2 ^ T = (u : ℝ) + 1 + j / 2 ^ T := by
      push_cast; field_simp
    have hj0 : (0 : ℝ) ≤ j / 2 ^ T := by positivity
    rw [hp, sgn_le_iff hu (by linarith) (by linarith [hm.1]), ← sub_nonneg]
    have e : xlo - ((u : ℝ) + 1 + j / 2 ^ T) = ((xlo - u - 1) * 2 ^ T - j) / 2 ^ T := by
      field_simp; ring
    rw [e]
    exact ⟨fun h => by
      have := mul_nonneg h hT.le; rw [div_mul_cancel₀ _ hT.ne'] at this; linarith,
      fun h => div_nonneg (by linarith) hT.le⟩
  have hg := gcount_eq (gC Q u T q) hz0 hC (2 ^ T)
  have hfl : ⌊z⌋₊ ≤ 2 ^ T := Nat.floor_le_of_le (by exact_mod_cast hz1)
  rw [min_eq_right hfl] at hg
  have hN : ((gN (Q := Q) (u := u) T q : ℕ) : ℝ) / 2 ^ T = (u : ℝ) + 1 + (⌊z⌋₊ : ℝ) / 2 ^ T := by
    simp only [gN, hg]; push_cast; field_simp
  have f1 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz0
  have f2 : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  rw [hN]
  have e2 : xlo = (u : ℝ) + 1 + z / 2 ^ T := by simp only [z]; field_simp; ring
  constructor
  · rw [e2]; gcongr
  · rw [e2, one_div_pow]
    have : z / 2 ^ T < ((⌊z⌋₊ : ℝ) + 1) / 2 ^ T := by gcongr
    rw [add_div] at this
    linarith

theorem primrec_gN : Primrec fun x : ℕ × List Bool => gN (Q := Q) (u := u) x.1 x.2 := by
  have hpow2 : ∀ {f : (ℕ × List Bool) × ℕ → ℕ}, Primrec f → Primrec fun x => 2 ^ f x :=
    fun hf => ComputableNormal.primrec_pow.comp (Primrec.const 2) hf
  have hT : Primrec fun x : (ℕ × List Bool) × ℕ => x.1.1 := Primrec.fst.comp Primrec.fst
  have hq : Primrec fun x : (ℕ × List Bool) × ℕ => x.1.2 := Primrec.snd.comp Primrec.fst
  have hN : Primrec fun x : (ℕ × List Bool) × ℕ => (u + 1) * 2 ^ x.1.1 + x.2 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const _) (hpow2 hT)) Primrec.snd
  have hF : Primrec fun x : (ℕ × List Bool) × ℕ => 2 ^ (2 * x.1.2.length + 1) :=
    hpow2 (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.list_length.comp hq)) (Primrec.const 1))
  have hE : Primrec fun x : (ℕ × List Bool) × ℕ => 2 ^ (x.1.1 * (lR Q u).length) :=
    hpow2 (Primrec.nat_mul.comp hT (Primrec.const _))
  have hev : ∀ {g : List ℤ × ℕ × ℕ → ℕ}, Primrec g →
      Primrec fun x : (ℕ × List Bool) × ℕ => g (lR Q u, (u + 1) * 2 ^ x.1.1 + x.2, x.1.1) :=
    fun hg => hg.comp (Primrec.pair (Primrec.const _) (Primrec.pair hN hT))
  have hrel : PrimrecRel fun (x : ℕ × List Bool) (j : ℕ) => gC Q u x.1 x.2 j := by
    unfold gC
    exact Primrec.nat_le.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (hev primrec_evP) hF)
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp hE (Primrec.const _)) hF))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (hev primrec_evM) hF)
        (Primrec.nat_mul.comp hE (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const _) hF)
          (Primrec.nat_mul.comp (Primrec.const _) (primrec_yN.comp hq)))))
  have hc := primrec_gcount (fun (x : ℕ × List Bool) (j : ℕ) => gC Q u x.1 x.2 j) hrel
    (f := fun x : ℕ × List Bool => 2 ^ x.1)
    (ComputableNormal.primrec_pow.comp (Primrec.const 2) Primrec.fst)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const _)
    (ComputableNormal.primrec_pow.comp (Primrec.const 2) Primrec.fst)) hc

end Grid

/-! ### The affine-dependence test -/

section Aff

/-- Coefficient list of `Q`. -/
noncomputable def lQ (Q : ℤ[X]) : List ℤ := (List.range (Q.natDegree + 1)).map Q.coeff

theorem affTest_iff (Q : ℤ[X]) (k₀ k₁ : ℕ) (l : List ℤ) (m : ℕ) :
    affTest (lQ Q) k₀ k₁ l m ↔
      (aeval (m : ℝ) (polyOfList l) - aeval (k₀ : ℝ) (polyOfList l)) *
          (aeval (k₁ : ℝ) Q - aeval (k₀ : ℝ) Q) =
        (aeval (k₁ : ℝ) (polyOfList l) - aeval (k₀ : ℝ) (polyOfList l)) *
          (aeval (m : ℝ) Q - aeval (k₀ : ℝ) Q) := by
  rw [affTest, pmulEq_iff]
  simp only [pval_psub, pval_evN, lQ, polyOfList_coeffs]

theorem aeval_natCast_eq (Q : ℤ[X]) (m : ℕ) : aeval (m : ℝ) Q = ((Q.eval (m : ℤ) : ℤ) : ℝ) := by
  rw [aeval_intCast_eq]; rfl

theorem affFail_iff {Q : ℤ[X]} {k₀ k₁ : ℕ} (hk : Q.eval (k₁ : ℤ) ≠ Q.eval (k₀ : ℤ))
    (l : List ℤ) :
    affFail (lQ Q) k₀ k₁ l (l.length + Q.natDegree + 1) = 0 ↔ AffineIn (polyOfList l) Q := by
  rw [affFail_eq_zero_iff]
  set P := polyOfList l
  constructor
  · intro h
    set dQ : ℤ := Q.eval (k₁ : ℤ) - Q.eval (k₀ : ℤ)
    set dP : ℤ := P.eval (k₁ : ℤ) - P.eval (k₀ : ℤ)
    set D : ℤ[X] := (P - C (P.eval (k₀ : ℤ))) * C dQ - C dP * (Q - C (Q.eval (k₀ : ℤ)))
    have hev : ∀ m < l.length + Q.natDegree + 1, D.eval (m : ℤ) = 0 := by
      intro m hm
      have := (affTest_iff Q k₀ k₁ l m).1 (h m hm)
      simp only [aeval_natCast_eq] at this
      have h' : (P.eval (m : ℤ) - P.eval (k₀ : ℤ)) * dQ = dP * (Q.eval (m : ℤ) - Q.eval (k₀ : ℤ)) := by
        exact_mod_cast this
      simp only [D, eval_sub, eval_mul, eval_C]
      linear_combination h'
    have hdeg : D.natDegree < l.length + Q.natDegree + 1 := by
      have hP := natDegree_polyOfList_le l
      have h1 : ((P - C (P.eval (k₀ : ℤ))) * C dQ).natDegree ≤ l.length :=
        (natDegree_mul_C_le _ _).trans ((natDegree_sub_C).le.trans hP)
      have h2 : (C dP * (Q - C (Q.eval (k₀ : ℤ)))).natDegree ≤ Q.natDegree :=
        (natDegree_C_mul_le _ _).trans (natDegree_sub_C).le
      exact Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans
        (max_le (h1.trans (Nat.le_add_right _ _)) (h2.trans (Nat.le_add_left _ _))))
    have hD : D = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero D
        (f := fun i : Fin (l.length + Q.natDegree + 1) => ((i : ℕ) : ℤ))
        (fun a b hab => Fin.ext (by simpa using hab)) (fun i => hev i i.2) (by simpa using hdeg)
    have hdQ : (dQ : ℚ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hk
    set γ : ℤ := P.eval (k₀ : ℤ) * dQ - dP * Q.eval (k₀ : ℤ)
    refine ⟨(dP : ℚ) / dQ, (γ : ℚ) / dQ, ?_⟩
    have hm := congrArg (Polynomial.map (Int.castRingHom ℚ)) hD
    simp only [D, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_zero,
      Int.coe_castRingHom] at hm
    have key : P.map (Int.castRingHom ℚ) * C (dQ : ℚ) =
        C (dP : ℚ) * Q.map (Int.castRingHom ℚ) + C (γ : ℚ) := by
      simp only [γ]; push_cast
      simp only [C_sub, C_mul]
      linear_combination hm
    calc P.map (Int.castRingHom ℚ) = (P.map (Int.castRingHom ℚ) * C (dQ : ℚ)) * C ((dQ : ℚ)⁻¹) := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hdQ, C_1, mul_one]
      _ = _ := by rw [key, div_eq_mul_inv, div_eq_mul_inv, C_mul, C_mul]; ring
  · rintro ⟨α, β, hab⟩ m _
    rw [affTest_iff]
    have e := aeval_eq_of_affineIn hab
    rw [e, e, e]
    ring

end Aff

/-! ### Lipschitz estimates on the window -/

section Lip

theorem abs_aeval_sub_le_window (P : ℤ[X]) (u : ℕ) {x x' : ℝ}
    (hx : x ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2)) (hx' : x' ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2)) :
    |aeval x P - aeval x' P| ≤
      ((P.natDegree : ℝ) + 1) * hgt P * ((u : ℝ) + 2) ^ P.natDegree * |x - x'| := by
  have hB : (1 : ℝ) ≤ (u : ℝ) + 2 := by linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
  have := (convex_Icc ((u : ℝ) + 1) ((u : ℝ) + 2)).norm_image_sub_le_of_norm_deriv_le
    (f := fun x : ℝ => aeval x P)
    (C := ((P.natDegree : ℝ) + 1) * hgt P * ((u : ℝ) + 2) ^ P.natDegree)
    (fun z _ => Polynomial.differentiableAt_aeval P) (fun z hz => by
      rw [Polynomial.deriv_aeval, Real.norm_eq_abs]
      refine (abs_aeval_deriv_le P hB ?_).2.1
      rw [abs_of_nonneg (by linarith [hz.1, (Nat.cast_nonneg u : (0 : ℝ) ≤ u)])]; exact hz.2)
    hx' hx
  simpa [Real.norm_eq_abs] using this

theorem abs_sub_le_abs_aeval_sub {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {s t : ℝ}
    (hs : (u : ℝ) ≤ s) (ht : (u : ℝ) ≤ t) : |t - s| ≤ |aeval t Q - aeval s Q| := by
  have hσ : |(sgnQ Q u : ℝ)| = 1 := by unfold sgnQ; split_ifs <;> simp
  have key : |t - s| ≤ |(sgnQ Q u : ℝ) * aeval t Q - (sgnQ Q u : ℝ) * aeval s Q| := by
    rcases le_total s t with h | h
    · have := sgn_expand hu s t hs h
      rw [abs_of_nonneg (by linarith)]; exact this.trans (le_abs_self _)
    · have := sgn_expand hu t s ht h
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm]; exact this.trans (le_abs_self _)
  rwa [← mul_sub, abs_mul, hσ, one_mul] at key

theorem abs_Xf_sub_le {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {y y' : ℝ}
    (hy : y ∈ Set.Icc (1 / 2 : ℝ) 1) (hy' : y' ∈ Set.Icc (1 / 2 : ℝ) 1) :
    |Xf Q u y - Xf Q u y'| ≤ (cnQ Q u : ℝ) * |y - y'| := by
  have h1 := Xf_mem_Icc hu hy
  have h2 := Xf_mem_Icc hu hy'
  have u0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have := abs_sub_le_abs_aeval_sub hu (s := Xf Q u y') (t := Xf Q u y) (by linarith [h2.1])
    (by linarith [h1.1])
  rw [(Xf_spec (window_sub_Vset hu hy)).2, (Xf_spec (window_sub_Vset hu hy')).2] at this
  have hc : |(cQ Q u : ℝ)| = cnQ Q u := by
    rw [cnQ, Nat.cast_natAbs, Int.cast_abs]
  calc _ ≤ _ := this
    _ = _ := by rw [← hc, ← abs_mul]; congr 1; ring

end Lip

/-! ### The re-normalised family -/

section Fam

/-- Coefficient list of `X^{deg Q + 1}`. -/
noncomputable def lX (Q : ℤ[X]) : List ℤ :=
  (List.range ((X ^ (Q.natDegree + 1) : ℤ[X]).natDegree + 1)).map (X ^ (Q.natDegree + 1) : ℤ[X]).coeff

/-- Decoded list. -/
def dl (i : ℕ) : List ℤ := (Encodable.decode (α := List ℤ) i).getD []

theorem primrec_dl : Primrec dl := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- Index `i` → coefficient list: the decoded one when it is off `span(1, Q)`, else `X^{deg Q+1}`. -/
noncomputable def lst (Q : ℤ[X]) (u i : ℕ) : List ℤ :=
  if affFail (lQ Q) (u + 1) (u + 2) (dl i) ((dl i).length + Q.natDegree + 1) = 0 then lX Q
  else dl i

theorem primrec_lst (Q : ℤ[X]) (u : ℕ) : Primrec (lst Q u) := by
  have h := primrec_affFail (lQ Q) (u + 1) (u + 2) (n := fun l : List ℤ => l.length + Q.natDegree + 1)
    (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.list_length (Primrec.const _))
      (Primrec.const 1))
  exact Primrec.ite (Primrec.eq.comp (h.comp primrec_dl) (Primrec.const 0)) (Primrec.const _)
    primrec_dl

theorem eval_ne_of_isBranch {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) :
    Q.eval (((u + 2 : ℕ)) : ℤ) ≠ Q.eval (((u + 1 : ℕ)) : ℤ) := by
  intro h
  apply (branch_spec hu).1
  simp only [cQ]; push_cast at h; rw [h]; ring

theorem not_affineIn_lst {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) (i : ℕ) :
    ¬ AffineIn (polyOfList (lst Q u i)) Q := by
  unfold lst
  split_ifs with h
  · rw [lX, polyOfList_coeffs]; exact not_affineIn_X_pow_succ Q
  · rwa [← affFail_iff (eval_ne_of_isBranch hu)]

theorem exists_lst_eq {Q : ℤ[X]} {u : ℕ} (hu : IsBranch Q u) {P : ℤ[X]} (hP : ¬ AffineIn P Q) :
    ∃ i, polyOfList (lst Q u i) = P := by
  refine ⟨Encodable.encode ((List.range (P.natDegree + 1)).map P.coeff), ?_⟩
  have hd : dl (Encodable.encode ((List.range (P.natDegree + 1)).map P.coeff)) =
      (List.range (P.natDegree + 1)).map P.coeff := by simp [dl]
  unfold lst
  rw [hd, if_neg, polyOfList_coeffs]
  rw [affFail_iff (eval_ne_of_isBranch hu), polyOfList_coeffs]; exact hP

/-- `H_l = Σ|l_j| (u+2)^{|l|} + 1`. -/
def Hl (u : ℕ) (l : List ℤ) : ℕ := Hn l * (u + 2) ^ l.length + 1

/-- Normaliser `M_l = H_l (|c| + 1)(|l| + 1)`. -/
noncomputable def Ml (Q : ℤ[X]) (u : ℕ) (l : List ℤ) : ℕ :=
  Hl u l * ((cnQ Q u + 1) * (l.length + 1))

theorem primrec_Ml (Q : ℤ[X]) (u : ℕ) : Primrec (Ml Q u) := by
  unfold Ml Hl
  exact Primrec.nat_mul.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp primrec_Hn
    (ComputableNormal.primrec_pow.comp (Primrec.const _) Primrec.list_length)) (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const _) (Primrec.nat_add.comp Primrec.list_length
      (Primrec.const 1)))

theorem one_le_Ml (Q : ℤ[X]) (u : ℕ) (l : List ℤ) : 1 ≤ Ml Q u l :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

/-- The re-normalised family `(G_P(y) + M)/(2M)`, `P = polyOfList (lst i)`. -/
noncomputable def GPfam2 (Q : ℤ[X]) (u i : ℕ) (ω : ℕ → Bool) : ℝ :=
  (GP Q u (polyOfList (lst Q u i)) (cantorReal ω) + Ml Q u (lst Q u i)) /
    (2 * Ml Q u (lst Q u i))

end Fam

/-! ### Exact lower approximations of `GPfam2` -/

section Approx

/-- Truncated-subtraction rational `= max 0 (R − 4^{-D}/2)`, `R = ((p − m)/E + M)/(2M)`. -/
theorem natsub_div_eq (p m E M D : ℕ) (hE : 0 < E) (hM : 0 < M) :
    (((4 ^ D * (p + E * M) - (4 ^ D * m + E * M) : ℕ) : ℝ) / ((2 * M * E * 4 ^ D : ℕ) : ℝ)) =
      max 0 (((((p : ℝ) - m) / E + M) / (2 * M)) - (1 / 4 : ℝ) ^ D / 2) := by
  set v : ℝ := ((((p : ℝ) - m) / E + M) / (2 * M)) - (1 / 4 : ℝ) ^ D / 2
  have hD0 : (0 : ℝ) < ((2 * M * E * 4 ^ D : ℕ) : ℝ) := by positivity
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have key : ((4 ^ D * (p + E * M) : ℕ) : ℝ) - ((4 ^ D * m + E * M : ℕ) : ℝ) =
      v * ((2 * M * E * 4 ^ D : ℕ) : ℝ) := by
    simp only [v]; push_cast
    have e4 : (1 / 4 : ℝ) ^ D * 4 ^ D = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination ((E : ℝ) * M) * e4
  by_cases hle : 4 ^ D * m + E * M ≤ 4 ^ D * (p + E * M)
  · rw [Nat.cast_sub hle, key, mul_div_cancel_right₀ _ hD0.ne']
    have : 0 ≤ v := by
      have h0 : (0 : ℝ) ≤ v * ((2 * M * E * 4 ^ D : ℕ) : ℝ) := by
        rw [← key]; exact sub_nonneg.2 (by exact_mod_cast hle)
      exact nonneg_of_mul_nonneg_left h0 hD0
    rw [max_eq_right this]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle)]
    have hlt : ((4 ^ D * (p + E * M) : ℕ) : ℝ) < ((4 ^ D * m + E * M : ℕ) : ℝ) := by
      exact_mod_cast not_le.1 hle
    have : v * ((2 * M * E * 4 ^ D : ℕ) : ℝ) < 0 := by rw [← key]; linarith
    have : v < 0 := neg_of_mul_neg_left this hD0.le
    rw [max_eq_left this.le, Nat.cast_zero, zero_div]

variable (Q : ℤ[X]) (u : ℕ)

/-- Grid numerator / denominator at prefix `q` (`T = 2|q| + 1`). -/
noncomputable def Num2 (l : List ℤ) (q : List Bool) : ℕ :=
  4 ^ q.length * (evP l (gN (Q := Q) (u := u) (2 * q.length + 1) q) (2 * q.length + 1) +
      2 ^ ((2 * q.length + 1) * l.length) * Ml Q u l) -
    (4 ^ q.length * evM l (gN (Q := Q) (u := u) (2 * q.length + 1) q) (2 * q.length + 1) +
      2 ^ ((2 * q.length + 1) * l.length) * Ml Q u l)

noncomputable def Den2 (l : List ℤ) (q : List Bool) : ℕ :=
  2 * Ml Q u l * 2 ^ ((2 * q.length + 1) * l.length) * 4 ^ q.length

variable {Q u}

theorem approx2_core (hu : IsBranch Q u) (l : List ℤ) (ω : ℕ → Bool) (D : ℕ) :
    0 ≤ (Num2 Q u l (Derandomize.pre ω D) : ℝ) / Den2 Q u l (Derandomize.pre ω D) ∧
    (Num2 Q u l (Derandomize.pre ω D) : ℝ) / Den2 Q u l (Derandomize.pre ω D) ≤
      (GP Q u (polyOfList l) (cantorReal ω) + Ml Q u l) / (2 * Ml Q u l) ∧
    (GP Q u (polyOfList l) (cantorReal ω) + Ml Q u l) / (2 * Ml Q u l) ≤
      (Num2 Q u l (Derandomize.pre ω D) : ℝ) / Den2 Q u l (Derandomize.pre ω D) +
        (1 / 2 : ℝ) ^ D := by
  set q := Derandomize.pre ω D with hqdef
  have hq : q.length = D := Derandomize.length_pre ω D
  set T := 2 * q.length + 1 with hT
  set N := gN (Q := Q) (u := u) T q with hN
  set P := polyOfList l
  set M : ℝ := (Ml Q u l : ℝ) with hMdef
  set E : ℕ := 2 ^ (T * l.length) with hE
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast one_le_Ml Q u l
  -- the closed form of the approximant
  have hA : (Num2 Q u l q : ℝ) / Den2 Q u l q =
      max 0 ((aeval ((N : ℝ) / 2 ^ T) P + M) / (2 * M) - (1 / 4 : ℝ) ^ D / 2) := by
    have h := natsub_div_eq (evP l N T) (evM l N T) E (Ml Q u l) q.length (by positivity)
      (one_le_Ml Q u l)
    have hev := evP_sub_evM l N T
    have hE0 : (E : ℝ) ≠ 0 := by positivity
    have : ((evP l N T : ℝ) - evM l N T) / E = aeval ((N : ℝ) / 2 ^ T) P := by
      rw [hev, hE]; push_cast; field_simp; rfl
    rw [this] at h
    rw [Num2, Den2, h, hq]
  rw [hA]
  -- the prefix bracket
  obtain ⟨hy1, hy2⟩ := cantorReal_mem_prefix D ω
  rw [← hqdef] at hy1 hy2
  set y := cantorReal ω
  set ylo : ℝ := (yN q : ℝ) / 2 ^ (2 * D + 1)
  have hYge : (4 : ℝ) ^ D ≤ yN q := by rw [← hq]; exact_mod_cast yN_ge q
  have h2D : (2 : ℝ) ^ (2 * D + 1) = 2 * 4 ^ D := by rw [pow_succ, pow_mul]; norm_num; ring
  have hlo : 1 / 2 ≤ ylo := by rw [le_div_iff₀ (by positivity), h2D]; linarith
  have hy23 : y ≤ 2 / 3 := cantorReal_le_two_thirds ω
  have hloW : ylo ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨hlo, by linarith⟩
  have hyW : y ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hloW' : (yN q : ℝ) / 2 ^ (2 * q.length + 1) ∈ Set.Icc (1 / 2 : ℝ) 1 := by rw [hq]; exact hloW
  obtain ⟨hg1, hg2⟩ := grid_bracket hu T q hloW'
  rw [hq] at hg1 hg2
  rw [← hN] at hg1 hg2
  set xlo := Xf Q u ylo
  set xt : ℝ := (N : ℝ) / 2 ^ T
  have hxlo := Xf_mem_Icc hu hloW
  have hx := Xf_mem_Icc hu hyW
  have hxt : xt ∈ Set.Icc ((u : ℝ) + 1) ((u : ℝ) + 2) := by
    refine ⟨?_, by linarith [hxlo.2]⟩
    rw [le_div_iff₀ (by positivity)]
    have : (u + 1) * 2 ^ T ≤ N := by simp only [hN, gN]; omega
    exact_mod_cast this
  have hT2 : (1 / 2 : ℝ) ^ T = (1 / 4 : ℝ) ^ D / 2 := by
    rw [hT, hq, pow_succ, pow_mul, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]; ring
  -- distances
  have E1 : |Xf Q u y - xlo| ≤ (cnQ Q u : ℝ) * ((1 / 4 : ℝ) ^ D / 6) := by
    refine (abs_Xf_sub_le hu hyW hloW).trans ?_
    gcongr
    rw [abs_of_nonneg (by linarith)]; linarith
  have E2 : |xlo - xt| ≤ (1 / 4 : ℝ) ^ D / 2 := by
    rw [abs_of_nonneg (by linarith), ← hT2]; linarith
  -- Lipschitz constant
  set L : ℕ := l.length
  have hdeg : P.natDegree ≤ L := natDegree_polyOfList_le l
  have hB : (1 : ℝ) ≤ (u : ℝ) + 2 := by linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
  have hHn : (hgt P : ℝ) = Hn l := by rw [hgt_polyOfList, Hn_cast]
  have hBp : ((u : ℝ) + 2) ^ P.natDegree ≤ ((u : ℝ) + 2) ^ L := pow_le_pow_right₀ hB hdeg
  set H : ℝ := (Hl u l : ℝ) with hHdef
  have hHl : (Hn l : ℝ) * ((u : ℝ) + 2) ^ L + 1 = H := by rw [hHdef, Hl]; push_cast; ring
  have hMH : M = H * (((cnQ Q u : ℝ) + 1) * ((L : ℝ) + 1)) := by
    rw [hMdef, hHdef, Ml]; push_cast; ring
  have hLip : ((P.natDegree : ℝ) + 1) * hgt P * ((u : ℝ) + 2) ^ P.natDegree ≤ ((L : ℝ) + 1) * H := by
    rw [hHn, ← hHl]
    have : (P.natDegree : ℝ) ≤ L := by exact_mod_cast hdeg
    have hn : (0 : ℝ) ≤ Hn l := by positivity
    calc ((P.natDegree : ℝ) + 1) * Hn l * ((u : ℝ) + 2) ^ P.natDegree
        ≤ ((L : ℝ) + 1) * Hn l * ((u : ℝ) + 2) ^ L := by gcongr
      _ ≤ _ := by nlinarith
  have hPdiff : |aeval (Xf Q u y) P - aeval xt P| ≤
      ((L : ℝ) + 1) * H * ((cnQ Q u : ℝ) * ((1 / 4 : ℝ) ^ D / 6) + (1 / 4 : ℝ) ^ D / 2) := by
    refine (abs_aeval_sub_le_window P u hx hxt).trans ?_
    have : |Xf Q u y - xt| ≤ (cnQ Q u : ℝ) * ((1 / 4 : ℝ) ^ D / 6) + (1 / 4 : ℝ) ^ D / 2 :=
      (abs_sub_le _ xlo _).trans (add_le_add E1 E2)
    gcongr
  -- assemble
  have h4 : (0 : ℝ) ≤ (1 / 4) ^ D := by positivity
  have hc0 : (0 : ℝ) ≤ cnQ Q u := Nat.cast_nonneg _
  have hH0 : (0 : ℝ) < H := by rw [← hHl]; positivity
  have hGP : GP Q u P y = aeval (Xf Q u y) P := rfl
  set R := (aeval xt P + M) / (2 * M)
  have hFR : |(GP Q u P y + M) / (2 * M) - R| ≤ (1 / 4 : ℝ) ^ D / 2 := by
    rw [show (GP Q u P y + M) / (2 * M) - R = (aeval (Xf Q u y) P - aeval xt P) / (2 * M) by
      simp only [R, hGP]; ring, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * M),
      div_le_iff₀ (by linarith)]
    refine hPdiff.trans ?_
    rw [hMH]
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have : (cnQ Q u : ℝ) * ((1 / 4 : ℝ) ^ D / 6) + (1 / 4 : ℝ) ^ D / 2 ≤
        ((cnQ Q u : ℝ) + 1) * ((1 / 4 : ℝ) ^ D) := by nlinarith
    calc ((L : ℝ) + 1) * H * ((cnQ Q u : ℝ) * ((1 / 4 : ℝ) ^ D / 6) + (1 / 4 : ℝ) ^ D / 2)
        ≤ ((L : ℝ) + 1) * H * (((cnQ Q u : ℝ) + 1) * ((1 / 4 : ℝ) ^ D)) := by gcongr
      _ = _ := by ring
  have hF0 : 0 ≤ (GP Q u P y + M) / (2 * M) := by
    have hb : |aeval (Xf Q u y) P| ≤ M := by
      have hxa : |Xf Q u y| ≤ (u : ℝ) + 2 := by
        rw [abs_of_nonneg (by linarith [hx.1, (Nat.cast_nonneg u : (0 : ℝ) ≤ u)])]; exact hx.2
      refine (abs_aeval_deriv_le P hB hxa).1.trans ?_
      rw [hHn]
      have : H ≤ M := by
        rw [hMH]; have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
        exact le_mul_of_one_le_right hH0.le
          (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))
      have hn : (0 : ℝ) ≤ Hn l := by positivity
      calc (Hn l : ℝ) * ((u : ℝ) + 2) ^ P.natDegree ≤ Hn l * ((u : ℝ) + 2) ^ L := by gcongr
        _ ≤ H := by rw [← hHl]; exact le_add_of_nonneg_right zero_le_one
        _ ≤ M := this
    rw [hGP]
    exact div_nonneg (by linarith [neg_abs_le (aeval (Xf Q u y) P)]) (by linarith)
  have h41 : (1 / 4 : ℝ) ^ D ≤ (1 / 2) ^ D := by gcongr; norm_num
  rw [abs_le] at hFR
  refine ⟨le_max_left _ _, max_le hF0 (by linarith), ?_⟩
  linarith [le_max_right 0 (R - (1 / 4 : ℝ) ^ D / 2)]

end Approx

end NormalNumbers.ExplicitPQ
