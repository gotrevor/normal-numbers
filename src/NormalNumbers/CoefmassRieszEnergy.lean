/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelPhaseAlgebra
import Mathlib.Data.ZMod.QuotientRing

/-!
# Model energy above the Riesz cutoff

The coefmass route (`docs/notes/coefmass-bv-ledger-2026-10-11.md`) names `RieszEnergyTail` as one
of the inputs of `siteFactorizationScheduled_of'`.  It is elementary, and this file proves it.

**Objects.**  For a finite set `P` of primes, the local phase of `p` at `n` is
`ψ_p(n) = ∏_{j : p ≤ y_j, p ∣ n+j+1} z_j`.  It is unimodular and depends only on `n mod p`.
`μ_p` is its mean over one period, and `φ_p = ψ_p − μ_p`.  Since `∏ (μ_p + φ_p) = ∏ ψ_p`, the
frozen product expands over subsets: `Φ = Σ_{T ⊆ P} c_T` with
`c_T = ∏_{p∉T} μ_p ∏_{p∈T} φ_p`.  The Riesz truncation weights the `T`-term by
`w_T = (1 − log d_T / K)_+^k`, where `d_T = ∏_{p∈T} p`.

**Claim.**  Over one CRT period `M = ∏_{p∈P} p`,
`mean |Φ − P_k|² ≤ (k/K) Σ_{p∈P} V_p log p`, where `V_p = 1 − |μ_p|²`.

**Proof plan** (each step a lemma):
1. *CRT product average.*  For pairwise distinct primes, `(1/M) Σ_{n<M} ∏_{p∈P} g_p(n mod p)`
   equals `∏_{p∈P} (1/p) Σ_{r<p} g_p r`.  This is the only arithmetic input; use
   `Nat.chineseRemainder` or the `ZMod` product equivalence.
2. *Periodicity.*  `psiP J y h p n = psiP J y h p (n % p)`.
3. *Orthogonality.*  For `T ≠ T′` the mean of `c_T · conj c_{T′}` is 0, because a prime in the
   symmetric difference contributes a factor `mean φ_p = 0` (by step 1).  Also
   `mean |c_T|² = ∏_{p∉T} |μ_p|² ∏_{p∈T} V_p`, using `mean |φ_p|² = mean |ψ_p|² − |μ_p|² = V_p`
   (with `|ψ_p| = 1`, `‖zPhase‖ = 1`).
4. *Expansion.*  `Φ − P_k = Σ_T (1 − w_T) c_T`, by `Finset.prod_add`.  So
   `mean |Φ − P_k|² = Σ_T (1 − w_T)² mean |c_T|²`.
5. *Scalar inequality.*  For `k ≥ 1`, `K > 0` and `x = log d_T / K ≥ 0`,
   `(1 − (max 0 (1 − x))^k)² ≤ k x`.  If `x ≥ 1` the left side is 1.  Otherwise use
   Bernoulli (`one_add_mul_le_pow`) and `(1−w)² ≤ 1−w`.
6. *Summation.*  `Σ_T log d_T ∏_{p∉T}|μ_p|² ∏_{p∈T} V_p = Σ_p V_p log p`, since
   `|μ_p|² + V_p = 1`: split `log d_T = Σ_{p∈T} log p` and sum out the other primes.

Exact numerical control (Opus, 2026-10-11): J=3, P={7,11,13,17}, four `(K, k)` pairs.  The
period-mean energy equals the orthogonal sum to all printed digits and lies under the bound.
-/

namespace NormalNumbers.PrimeModel.SiteFactor

open NormalNumbers.PrimeModel.PhaseAlgebra

/-- Local phase of prime `p` at `n`: `ψ_p(n) = ∏_{j : p ≤ y_j, p ∣ n+j+1} z_j`. -/
noncomputable def psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p n : ℕ) : ℂ :=
  ∏ j : Fin J, if p ≤ y j ∧ p ∣ n + j.val + 1 then zPhase h J j else 1

/-- Exact average over one period: the model expectation, by CRT. -/
noncomputable def periodMean (F : ℕ → ℂ) (M : ℕ) : ℂ := (∑ n ∈ Finset.range M, F n) / M

/-- The period mean of the local phase. -/
noncomputable def muP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ) : ℂ :=
  periodMean (psiP J y h p) p

/-- The local phase only depends on the residue class modulo its prime. -/
lemma psiP_mod (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p n : ℕ) :
    psiP J y h p n = psiP J y h p (n % p) := by
  unfold psiP
  apply Finset.prod_congr rfl
  intro j _
  have hn : n ≡ n % p [MOD p] := by simp [Nat.ModEq]
  have ha : n + (j.val + 1) ≡ n % p + (j.val + 1) [MOD p] := hn.add_right _
  have hdvd : p ∣ n + j.val + 1 ↔ p ∣ n % p + j.val + 1 := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    change (n + j.val + 1) % p = (n % p + j.val + 1) % p at ha
    rw [ha]
  simp only [hdvd]

/-- Every local phase is unimodular. -/
@[simp] lemma norm_psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p n : ℕ) :
    ‖psiP J y h p n‖ = 1 := by
  rw [psiP, norm_prod]
  apply Finset.prod_eq_one
  intro j _
  split <;> simp

/-- Centering by the period mean gives mean zero. -/
lemma periodMean_psiP_sub_muP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ)
    (hp : p ≠ 0) :
    periodMean (fun n ↦ psiP J y h p n - muP J y h p) p = 0 := by
  unfold muP
  simp only [periodMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- Rewrite a sum over the standard representatives modulo a nonzero modulus as a `ZMod` sum. -/
lemma sum_range_eq_sum_zmod (M : ℕ) [NeZero M] (F : ℕ → ℂ) :
    (∑ n ∈ Finset.range M, F n) = ∑ x : ZMod M, F x.val := by
  rw [← Equiv.sum_comp (ZMod.finEquiv M).toEquiv (fun x : ZMod M ↦ F x.val)]
  obtain _ | M := M
  · exact (NeZero.ne 0 rfl).elim
  · change (∑ n ∈ Finset.range (M + 1), F n) = ∑ i : Fin (M + 1), F i
    exact (Fin.sum_univ_eq_sum_range F (M + 1)).symm

/-- The algebraic heart of CRT averaging: a product of coordinate functions factors after
summing over the product modulus. -/
lemma sum_zmod_prod_eq_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hcop : Pairwise (Function.onFun Nat.Coprime a)) (g : ∀ i, ZMod (a i) → ℂ) :
    (∑ x : ZMod (∏ i, a i), ∏ i, g i ((ZMod.prodEquivPi a hcop) x i)) =
      ∏ i, ∑ r : ZMod (a i), g i r := by
  rw [Fintype.prod_sum]
  exact Equiv.sum_comp (ZMod.prodEquivPi a hcop).toEquiv (fun x ↦ ∏ i, g i (x i))

/-- CRT factorization over a finite set of primes, indexed by the subtype of the set. -/
lemma sum_range_prod_mod_eq_prod_sum_subtype (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (f : (p : P) → ℕ → ℂ) :
    (∑ n ∈ Finset.range (∏ p ∈ P, p), ∏ p : P, f p (n % p)) =
      ∏ p : P, ∑ r ∈ Finset.range (p : ℕ), f p r := by
  classical
  let a : P → ℕ := fun p ↦ p
  letI : ∀ p : P, NeZero (a p) := fun p ↦
    ⟨(hP p p.property).ne_zero⟩
  have hcop : Pairwise (Function.onFun Nat.Coprime a) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).2
      (fun hpqv ↦ hpq (Subtype.ext hpqv))
  have hprod : (∏ p : P, a p) = ∏ p ∈ P, p := by
    exact Finset.prod_coe_sort P (fun p ↦ p)
  letI : NeZero (∏ p : P, a p) :=
    ⟨by rw [hprod]; exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hP p hp).ne_zero⟩
  have hcoord (x : ZMod (∏ p : P, a p)) (p : P) :
      ((ZMod.prodEquivPi a hcop) x p).val = x.val % (p : ℕ) := by
    rw [ZMod.prodEquivPi_apply]
    rw [ZMod.castHom_apply]
    rw [ZMod.cast_eq_val]
    simp [a, ZMod.val_natCast]
  rw [← hprod]
  rw [sum_range_eq_sum_zmod]
  simp_rw [← hcoord]
  rw [sum_zmod_prod_eq_prod_sum a hcop (fun p r ↦ f p r.val)]
  apply Fintype.prod_congr
  intro p
  exact (sum_range_eq_sum_zmod (p : ℕ) (f p)).symm

/-- Natural-number form of the finite CRT product-sum factorization. -/
lemma sum_range_prod_mod_eq_prod_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.range (∏ p ∈ P, p), ∏ p ∈ P, f p (n % p)) =
      ∏ p ∈ P, ∑ r ∈ Finset.range p, f p r := by
  have h := sum_range_prod_mod_eq_prod_sum_subtype P hP (fun p r ↦ f p r)
  rw [show (∏ p : P, ∑ r ∈ Finset.range (p : ℕ), f p r) =
      ∏ p ∈ P, ∑ r ∈ Finset.range p, f p r from
    Finset.prod_coe_sort P (fun p ↦ ∑ r ∈ Finset.range p, f p r)] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro n _
  exact (Finset.prod_coe_sort P (fun p ↦ f p (n % p))).symm

/-- Riesz-truncated centered expansion over a finite prime set `P`:
`Σ_{T ⊆ P} (1 − log d_T/K)_+^k ∏_{p∉T} μ_p ∏_{p∈T} (ψ_p − μ_p)`. -/
noncomputable def rieszCentered (P : Finset ℕ) (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (k : ℕ)
    (n : ℕ) : ℂ :=
  ∑ T ∈ P.powerset, ((max 0 (1 - Real.log (∏ p ∈ T, (p : ℝ)) / K)) ^ k : ℝ) *
    ((∏ p ∈ P \ T, muP J y h p) * ∏ p ∈ T, (psiP J y h p n - muP J y h p))

/-- **Model energy above the Riesz cutoff.** -/
def RieszEnergyTail : Prop :=
  ∀ (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
    ∀ K : ℝ, 0 < K → ∀ k : ℕ, 1 ≤ k →
      (∑ n ∈ Finset.range (∏ p ∈ P, p),
          ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2) / (∏ p ∈ P, p : ℕ)
        ≤ k / K * ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p

/-- The scalar cutoff loss used termwise in the Riesz-energy estimate. -/
lemma one_sub_rieszWeight_sq_le (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    (1 - (max 0 (1 - x)) ^ k) ^ 2 ≤ k * x := by
  by_cases hx1 : 1 ≤ x
  · rw [max_eq_left]
    · simp only [zero_pow (Nat.ne_zero_of_lt hk), sub_zero, one_pow]
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [mul_nonneg (Nat.cast_nonneg k) hx]
    · linarith
  · have hxlt : x < 1 := lt_of_not_ge hx1
    rw [max_eq_right (by linarith)]
    have hpow_nonneg : 0 ≤ (1 - x) ^ k := pow_nonneg (by linarith) k
    have hpow_le : (1 - x) ^ k ≤ 1 := by
      exact pow_le_one₀ (by linarith : 0 ≤ 1 - x) (by linarith : 1 - x ≤ 1)
    have hbern : 1 - (1 - x) ^ k ≤ k * x := by
      have h := one_add_mul_le_pow (a := -x) (by linarith : (-2 : ℝ) ≤ -x) k
      ring_nf at h
      linarith
    have hsquare : (1 - (1 - x) ^ k) ^ 2 ≤ 1 - (1 - x) ^ k := by
      nlinarith
    exact hsquare.trans hbern

/-- Finite bias-variance identity for a complex-valued family. -/
lemma sum_norm_sub_mean_sq (z : ℕ → ℂ) (M : ℕ) (hM : 0 < M) :
    (∑ d ∈ Finset.range M, ‖z d - (∑ e ∈ Finset.range M, z e) / (M : ℂ)‖ ^ 2) / M
      = (∑ d ∈ Finset.range M, ‖z d‖ ^ 2) / M -
        ‖(∑ e ∈ Finset.range M, z e) / (M : ℂ)‖ ^ 2 := by
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set m : ℂ := (∑ e ∈ Finset.range M, z e) / (M : ℂ) with hm
  have hsum : ∑ e ∈ Finset.range M, z e = (M : ℂ) * m := by rw [hm]; field_simp
  have hexp : ∑ d ∈ Finset.range M, ‖z d - m‖ ^ 2
      = (∑ d ∈ Finset.range M, ‖z d‖ ^ 2) + (M : ℝ) * ‖m‖ ^ 2
        - 2 * (((∑ d ∈ Finset.range M, z d) * (starRingEnd ℂ) m).re) := by
    have hstep : ∀ d ∈ Finset.range M, ‖z d - m‖ ^ 2
        = ‖z d‖ ^ 2 + ‖m‖ ^ 2 - 2 * ((z d * (starRingEnd ℂ) m).re) := by
      intro d _
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    rw [Finset.sum_congr rfl hstep]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, ← Complex.re_sum,
      ← Finset.sum_mul]
  have hre : (((∑ d ∈ Finset.range M, z d) * (starRingEnd ℂ) m).re) =
      (M : ℝ) * ‖m‖ ^ 2 := by
    rw [hsum, mul_assoc, Complex.mul_conj, Complex.sq_norm]
    simp
  rw [hexp, hre]
  field_simp
  ring

/-- The unnormalized sum of a centered local phase is zero. -/
lemma sum_centered_psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ)
    (hp : p ≠ 0) :
    ∑ r ∈ Finset.range p, (psiP J y h p r - muP J y h p) = 0 := by
  unfold muP periodMean
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp
  ring

/-- The mean-square centered local phase has variance `1 - ‖μ_p‖²`. -/
lemma mean_sq_centered_psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ)
    (hp : 0 < p) :
    (∑ r ∈ Finset.range p, ‖psiP J y h p r - muP J y h p‖ ^ 2) / p =
      1 - ‖muP J y h p‖ ^ 2 := by
  have hv := sum_norm_sub_mean_sq (psiP J y h p) p hp
  rw [show (∑ e ∈ Finset.range p, psiP J y h p e) / (p : ℂ) =
      muP J y h p by rfl] at hv
  rw [show (∑ d ∈ Finset.range p, ‖psiP J y h p d‖ ^ 2) = (p : ℝ) by simp] at hv
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [div_self hpR] at hv
  exact hv

/-- Unnormalized form of the local variance identity. -/
lemma sum_sq_centered_psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ)
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, ‖psiP J y h p r - muP J y h p‖ ^ 2 =
      p * (1 - ‖muP J y h p‖ ^ 2) := by
  have hv := mean_sq_centered_psiP J y h p hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    (∑ r ∈ Finset.range p, ‖psiP J y h p r - muP J y h p‖ ^ 2) =
        ((∑ r ∈ Finset.range p, ‖psiP J y h p r - muP J y h p‖ ^ 2) / p) * p := by
          rw [div_mul_cancel₀ _ hpR]
    _ = (1 - ‖muP J y h p‖ ^ 2) * p := by rw [hv]
    _ = p * (1 - ‖muP J y h p‖ ^ 2) := mul_comm _ _

/-- Complex correlation form of the local variance identity. -/
lemma sum_centered_mul_conj (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ)
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p,
        (psiP J y h p r - muP J y h p) *
          (starRingEnd ℂ) (psiP J y h p r - muP J y h p) =
      (p : ℂ) * (1 - ‖muP J y h p‖ ^ 2 : ℝ) := by
  rw [Finset.sum_congr rfl (fun r _ ↦ Complex.mul_conj'
    (psiP J y h p r - muP J y h p))]
  exact_mod_cast sum_sq_centered_psiP J y h p hp

/-- The centered product indexed by one subset of primes. -/
noncomputable def centeredTerm (P T : Finset ℕ) (J : ℕ) (y : Fin J → ℕ)
    (h : ℤ) (n : ℕ) : ℂ :=
  (∏ p ∈ P \ T, muP J y h p) *
    ∏ p ∈ T, (psiP J y h p n - muP J y h p)

/-- One local factor in a centered subset term. -/
noncomputable def localCenteredFactor (T : Finset ℕ) (J : ℕ) (y : Fin J → ℕ)
    (h : ℤ) (p n : ℕ) : ℂ :=
  if p ∈ T then psiP J y h p n - muP J y h p else muP J y h p

lemma centeredTerm_eq_prod_localCenteredFactor (P T : Finset ℕ) (hT : T ⊆ P)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (n : ℕ) :
    centeredTerm P T J y h n =
      ∏ p ∈ P, localCenteredFactor T J y h p n := by
  unfold centeredTerm localCenteredFactor
  rw [Finset.prod_ite]
  have hfilter : P.filter (fun p ↦ p ∈ T) = T := by
    ext p
    simp only [Finset.mem_filter]
    aesop
  have hfilterc : P.filter (fun p ↦ ¬p ∈ T) = P \ T := by
    ext p
    simp
  rw [hfilter, hfilterc, mul_comm]

/-- Expansion of the untruncated product into centered subset terms. -/
lemma prod_psiP_eq_sum_centeredTerm (P : Finset ℕ) (J : ℕ)
    (y : Fin J → ℕ) (h : ℤ) (n : ℕ) :
    (∏ p ∈ P, psiP J y h p n) =
      ∑ T ∈ P.powerset, centeredTerm P T J y h n := by
  have hsplit : ∀ p, psiP J y h p n =
      (psiP J y h p n - muP J y h p) + muP J y h p := by
    intro p
    ring
  calc
    (∏ p ∈ P, psiP J y h p n) =
        ∏ p ∈ P, ((psiP J y h p n - muP J y h p) + muP J y h p) := by
          apply Finset.prod_congr rfl
          intro p _
          exact hsplit p
    _ = ∑ T ∈ P.powerset,
        (∏ p ∈ T, (psiP J y h p n - muP J y h p)) *
          ∏ p ∈ P \ T, muP J y h p := Finset.prod_add _ _ P
    _ = ∑ T ∈ P.powerset, centeredTerm P T J y h n := by
      apply Finset.sum_congr rfl
      intro T _
      rw [centeredTerm, mul_comm]

/-- Difference between the full product and its Riesz truncation. -/
lemma prod_psiP_sub_rieszCentered_eq (P : Finset ℕ) (J : ℕ)
    (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (k n : ℕ) :
    (∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n =
      ∑ T ∈ P.powerset,
        ((1 - (max 0 (1 - Real.log (∏ p ∈ T, (p : ℝ)) / K)) ^ k : ℝ) : ℂ) *
          centeredTerm P T J y h n := by
  rw [prod_psiP_eq_sum_centeredTerm, rieszCentered,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [centeredTerm]
  push_cast
  ring

/-- The local correlation between two centered subset terms. -/
noncomputable def localCenteredCorr (T U : Finset ℕ) (J : ℕ) (y : Fin J → ℕ)
    (h : ℤ) (p r : ℕ) : ℂ :=
  localCenteredFactor T J y h p r *
    (starRingEnd ℂ) (localCenteredFactor U J y h p r)

lemma localCenteredFactor_mod (T : Finset ℕ) (J : ℕ) (y : Fin J → ℕ)
    (h : ℤ) (p n : ℕ) :
    localCenteredFactor T J y h p n = localCenteredFactor T J y h p (n % p) := by
  unfold localCenteredFactor
  split
  · rw [psiP_mod]
  · rfl

lemma centeredTerm_mul_conj_eq_prod_localCenteredCorr (P T U : Finset ℕ)
    (hT : T ⊆ P) (hU : U ⊆ P) (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (n : ℕ) :
    centeredTerm P T J y h n * (starRingEnd ℂ) (centeredTerm P U J y h n) =
      ∏ p ∈ P, localCenteredCorr T U J y h p n := by
  rw [centeredTerm_eq_prod_localCenteredFactor P T hT,
    centeredTerm_eq_prod_localCenteredFactor P U hU]
  simp only [map_prod, Finset.prod_mul_distrib, localCenteredCorr]

/-- A local cross-correlation vanishes when exactly one subset contains its prime. -/
lemma sum_localCenteredCorr_eq_zero_of_mem_ne (T U : Finset ℕ) (J : ℕ)
    (y : Fin J → ℕ) (h : ℤ) (p : ℕ) (hp : p ≠ 0)
    (hne : (p ∈ T) ≠ (p ∈ U)) :
    ∑ r ∈ Finset.range p, localCenteredCorr T U J y h p r = 0 := by
  classical
  by_cases hpT : p ∈ T <;> by_cases hpU : p ∈ U
  · exact (hne (propext ⟨fun _ ↦ hpU, fun _ ↦ hpT⟩)).elim
  · simp only [localCenteredCorr, localCenteredFactor, if_pos hpT, if_neg hpU]
    rw [← Finset.sum_mul, sum_centered_psiP J y h p hp]
    simp
  · simp only [localCenteredCorr, localCenteredFactor, if_neg hpT, if_pos hpU]
    rw [← Finset.mul_sum, ← map_sum, sum_centered_psiP J y h p hp]
    simp
  · exact (hne (propext ⟨fun hmem ↦ (hpT hmem).elim,
      fun hmem ↦ (hpU hmem).elim⟩)).elim

/-- The diagonal local correlation is its exact variance factor. -/
lemma sum_localCenteredCorr_self (T : Finset ℕ) (J : ℕ) (y : Fin J → ℕ)
    (h : ℤ) (p : ℕ) (hp : 0 < p) :
    ∑ r ∈ Finset.range p, localCenteredCorr T T J y h p r =
      (p : ℂ) *
        ((if p ∈ T then 1 - ‖muP J y h p‖ ^ 2 else ‖muP J y h p‖ ^ 2 : ℝ) : ℂ) := by
  classical
  by_cases hpT : p ∈ T
  · simp only [localCenteredCorr, localCenteredFactor, if_pos hpT]
    exact sum_centered_mul_conj J y h p hp
  · simp only [localCenteredCorr, localCenteredFactor, if_neg hpT]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Complex.mul_conj']
    push_cast
    ring

/-- CRT factors the global correlation of two subset terms into local correlations. -/
lemma sum_centeredTerm_mul_conj_eq_prod_local (P T U : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hT : T ⊆ P) (hU : U ⊆ P)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    (∑ n ∈ Finset.range (∏ p ∈ P, p),
        centeredTerm P T J y h n *
          (starRingEnd ℂ) (centeredTerm P U J y h n)) =
      ∏ p ∈ P, ∑ r ∈ Finset.range p, localCenteredCorr T U J y h p r := by
  classical
  calc
    (∑ n ∈ Finset.range (∏ p ∈ P, p),
        centeredTerm P T J y h n *
          (starRingEnd ℂ) (centeredTerm P U J y h n)) =
        ∑ n ∈ Finset.range (∏ p ∈ P, p),
          ∏ p ∈ P, localCenteredCorr T U J y h p (n % p) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [centeredTerm_mul_conj_eq_prod_localCenteredCorr P T U hT hU]
            apply Finset.prod_congr rfl
            intro p _
            unfold localCenteredCorr
            rw [localCenteredFactor_mod T, localCenteredFactor_mod U]
    _ = ∏ p ∈ P, ∑ r ∈ Finset.range p, localCenteredCorr T U J y h p r :=
      sum_range_prod_mod_eq_prod_sum P hP (localCenteredCorr T U J y h)

/-- Distinct centered subset terms are orthogonal over one CRT period. -/
lemma sum_centeredTerm_mul_conj_eq_zero (P T U : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hT : T ⊆ P) (hU : U ⊆ P) (hTU : T ≠ U)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    ∑ n ∈ Finset.range (∏ p ∈ P, p),
        centeredTerm P T J y h n *
          (starRingEnd ℂ) (centeredTerm P U J y h n) = 0 := by
  classical
  rw [sum_centeredTerm_mul_conj_eq_prod_local P T U hP hT hU]
  have hex : ∃ p, (p ∈ T) ≠ (p ∈ U) := by
    by_contra hn
    push Not at hn
    apply hTU
    ext p
    exact iff_of_eq (hn p)
  obtain ⟨p, hpne⟩ := hex
  have hpP : p ∈ P := by
    by_cases hpT : p ∈ T
    · exact hT hpT
    · exact hU (by
        by_contra hpU
        exact hpne (propext ⟨fun hmem ↦ (hpT hmem).elim,
          fun hmem ↦ (hpU hmem).elim⟩))
  apply Finset.prod_eq_zero hpP
  exact sum_localCenteredCorr_eq_zero_of_mem_ne T U J y h p
    (hP p hpP).ne_zero hpne

/-- Probability mass of one centered subset term. -/
noncomputable def subsetMass (P T : Finset ℕ) (J : ℕ)
    (y : Fin J → ℕ) (h : ℤ) : ℝ :=
  ∏ p ∈ P,
    if p ∈ T then 1 - ‖muP J y h p‖ ^ 2 else ‖muP J y h p‖ ^ 2

/-- Exact diagonal mass of a centered subset term. -/
lemma sum_centeredTerm_mul_conj_self (P T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hT : T ⊆ P)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    (∑ n ∈ Finset.range (∏ p ∈ P, p),
        centeredTerm P T J y h n *
          (starRingEnd ℂ) (centeredTerm P T J y h n)) =
      ((∏ p ∈ P, p : ℕ) : ℂ) * (subsetMass P T J y h : ℂ) := by
  classical
  rw [sum_centeredTerm_mul_conj_eq_prod_local P T T hP hT hT]
  rw [Finset.prod_congr rfl (fun p hp ↦
    sum_localCenteredCorr_self T J y h p (hP p hp).pos)]
  rw [Finset.prod_mul_distrib]
  rw [subsetMass]
  push_cast
  rfl

/-- Finite Parseval identity for arbitrary coefficients of the centered subset basis. -/
lemma sum_weighted_centered_mul_conj (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (J : ℕ) (y : Fin J → ℕ) (h : ℤ)
    (a : Finset ℕ → ℂ) :
    (∑ n ∈ Finset.range (∏ p ∈ P, p),
        (∑ T ∈ P.powerset, a T * centeredTerm P T J y h n) *
          (starRingEnd ℂ) (∑ U ∈ P.powerset,
            a U * centeredTerm P U J y h n)) =
      ((∏ p ∈ P, p : ℕ) : ℂ) *
        ∑ T ∈ P.powerset,
          (a T * (starRingEnd ℂ) (a T)) * (subsetMass P T J y h : ℂ) := by
  classical
  let M := ∏ p ∈ P, p
  let S := P.powerset
  have hexpand :
      (∑ n ∈ Finset.range M,
          (∑ T ∈ S, a T * centeredTerm P T J y h n) *
            (starRingEnd ℂ) (∑ U ∈ S,
              a U * centeredTerm P U J y h n)) =
        ∑ n ∈ Finset.range M, ∑ T ∈ S, ∑ U ∈ S,
          (a T * (starRingEnd ℂ) (a U)) *
            (centeredTerm P T J y h n *
              (starRingEnd ℂ) (centeredTerm P U J y h n)) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.sum_congr rfl
    intro U _
    rw [map_mul]
    ring
  have hreorder :
      (∑ n ∈ Finset.range M, ∑ T ∈ S, ∑ U ∈ S,
          (a T * (starRingEnd ℂ) (a U)) *
            (centeredTerm P T J y h n *
              (starRingEnd ℂ) (centeredTerm P U J y h n))) =
        ∑ T ∈ S, ∑ U ∈ S,
          (a T * (starRingEnd ℂ) (a U)) *
            ∑ n ∈ Finset.range M,
              centeredTerm P T J y h n *
                (starRingEnd ℂ) (centeredTerm P U J y h n) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.mul_sum]
  rw [hexpand, hreorder]
  change (∑ T ∈ S, ∑ U ∈ S,
      (a T * (starRingEnd ℂ) (a U)) *
        ∑ n ∈ Finset.range M,
          centeredTerm P T J y h n *
            (starRingEnd ℂ) (centeredTerm P U J y h n)) =
    (M : ℂ) * ∑ T ∈ S,
      (a T * (starRingEnd ℂ) (a T)) * (subsetMass P T J y h : ℂ)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hTP : T ⊆ P := Finset.mem_powerset.mp hT
  rw [Finset.sum_eq_single T]
  · rw [sum_centeredTerm_mul_conj_self P T hP hTP]
    ring
  · intro U hU hUT
    have hUP : U ⊆ P := Finset.mem_powerset.mp hU
    rw [sum_centeredTerm_mul_conj_eq_zero P T U hP hTP hUP hUT.symm]
    ring
  · exact fun hnot ↦ (hnot hT).elim

/-- Scalar loss attached to one subset by the Riesz cutoff. -/
noncomputable def rieszLoss (T : Finset ℕ) (K : ℝ) (k : ℕ) : ℝ :=
  1 - (max 0 (1 - Real.log (∏ p ∈ T, (p : ℝ)) / K)) ^ k

lemma prod_psiP_sub_rieszCentered_eq_loss (P : Finset ℕ) (J : ℕ)
    (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (k n : ℕ) :
    (∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n =
      ∑ T ∈ P.powerset, (rieszLoss T K k : ℂ) *
        centeredTerm P T J y h n := by
  exact prod_psiP_sub_rieszCentered_eq P J y h K k n

/-- Exact orthogonal-sum formula for the Riesz truncation error. -/
lemma riesz_energy_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (k : ℕ) :
    (∑ n ∈ Finset.range (∏ p ∈ P, p),
        ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2) /
        (∏ p ∈ P, p : ℕ) =
      ∑ T ∈ P.powerset, (rieszLoss T K k) ^ 2 * subsetMass P T J y h := by
  classical
  let M := ∏ p ∈ P, p
  let S := P.powerset
  let a : Finset ℕ → ℂ := fun T ↦ (rieszLoss T K k : ℂ)
  have horth := sum_weighted_centered_mul_conj P hP J y h a
  have hleft :
      (∑ n ∈ Finset.range M,
          (∑ T ∈ S, a T * centeredTerm P T J y h n) *
            (starRingEnd ℂ) (∑ U ∈ S,
              a U * centeredTerm P U J y h n)) =
        ((∑ n ∈ Finset.range M,
          ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← prod_psiP_sub_rieszCentered_eq_loss P J y h K k n]
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hright :
      ((M : ℂ) * ∑ T ∈ S,
          (a T * (starRingEnd ℂ) (a T)) * (subsetMass P T J y h : ℂ)) =
        (((M : ℝ) * ∑ T ∈ S,
          (rieszLoss T K k) ^ 2 * subsetMass P T J y h : ℝ) : ℂ) := by
    push_cast
    apply congrArg₂ (· * ·) rfl
    apply Finset.sum_congr rfl
    intro T _
    simp only [a, Complex.conj_ofReal]
    ring
  have hreal :
      (∑ n ∈ Finset.range M,
          ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2 : ℝ) =
        (M : ℝ) * ∑ T ∈ S,
          (rieszLoss T K k) ^ 2 * subsetMass P T J y h := by
    apply Complex.ofReal_injective
    rw [← hleft, ← hright]
    exact horth
  have hM : (0 : ℝ) < M := by
    exact_mod_cast Finset.prod_pos fun p hp ↦ (hP p hp).pos
  change (∑ n ∈ Finset.range M,
      ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2) / M =
    ∑ T ∈ S, (rieszLoss T K k) ^ 2 * subsetMass P T J y h
  rw [hreal]
  field_simp

/-- A local phase mean lies in the closed unit disk. -/
lemma norm_muP_le_one (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ)
    (hp : 0 < p) : ‖muP J y h p‖ ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [muP, periodMean, norm_div, Complex.norm_natCast]
  rw [div_le_one hpR]
  calc
    ‖∑ n ∈ Finset.range p, psiP J y h p n‖
        ≤ ∑ n ∈ Finset.range p, ‖psiP J y h p n‖ := norm_sum_le _ _
    _ = (p : ℝ) := by simp

lemma subsetMass_nonneg (P T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    0 ≤ subsetMass P T J y h := by
  unfold subsetMass
  apply Finset.prod_nonneg
  intro p hp
  split
  · nlinarith [norm_nonneg (muP J y h p), norm_muP_le_one J y h p (hP p hp).pos]
  · positivity

lemma subsetMass_eq_split (P T : Finset ℕ) (hT : T ⊆ P)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    subsetMass P T J y h =
      (∏ p ∈ T, (1 - ‖muP J y h p‖ ^ 2)) *
        ∏ p ∈ P \ T, ‖muP J y h p‖ ^ 2 := by
  unfold subsetMass
  rw [Finset.prod_ite]
  have hfilter : P.filter (fun p ↦ p ∈ T) = T := by
    ext p
    simp only [Finset.mem_filter]
    aesop
  have hfilterc : P.filter (fun p ↦ ¬p ∈ T) = P \ T := by
    ext p
    simp
  rw [hfilter, hfilterc]

/-- The centered subset masses form a probability distribution. -/
lemma sum_subsetMass_eq_one (P : Finset ℕ) (J : ℕ)
    (y : Fin J → ℕ) (h : ℤ) :
    ∑ T ∈ P.powerset, subsetMass P T J y h = 1 := by
  calc
    (∑ T ∈ P.powerset, subsetMass P T J y h) =
        ∑ T ∈ P.powerset,
          (∏ p ∈ T, (1 - ‖muP J y h p‖ ^ 2)) *
            ∏ p ∈ P \ T, ‖muP J y h p‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro T hT
              exact subsetMass_eq_split P T (Finset.mem_powerset.mp hT) J y h
    _ = ∏ p ∈ P, ((1 - ‖muP J y h p‖ ^ 2) + ‖muP J y h p‖ ^ 2) := by
      rw [Finset.prod_add]
    _ = 1 := by simp

lemma subsetMass_insert_not_mem {q : ℕ} {P T : Finset ℕ}
    (hq : q ∉ P) (hT : T ⊆ P) (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    subsetMass (insert q P) T J y h =
      ‖muP J y h q‖ ^ 2 * subsetMass P T J y h := by
  have hqT : q ∉ T := fun hmem ↦ hq (hT hmem)
  simp [subsetMass, hq, hqT]

lemma subsetMass_insert_insert {q : ℕ} {P T : Finset ℕ}
    (hq : q ∉ P) (hT : T ⊆ P) (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    subsetMass (insert q P) (insert q T) J y h =
      (1 - ‖muP J y h q‖ ^ 2) * subsetMass P T J y h := by
  have hqT : q ∉ T := fun hmem ↦ hq (hT hmem)
  unfold subsetMass
  rw [Finset.prod_insert hq]
  simp only [Finset.mem_insert, true_or, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
  simp [hpq]

/-- First-moment identity for the Bernoulli subset mass. -/
lemma sum_powerset_sum_mul_subsetMass (P : Finset ℕ) (L : ℕ → ℝ)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    ∑ T ∈ P.powerset, (∑ p ∈ T, L p) * subsetMass P T J y h =
      ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * L p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [subsetMass]
  | @insert q P hq ih =>
      rw [Finset.sum_powerset_insert hq]
      have hfirst :
          (∑ T ∈ P.powerset,
              (∑ p ∈ T, L p) * subsetMass (insert q P) T J y h) =
            ‖muP J y h q‖ ^ 2 *
              ∑ T ∈ P.powerset, (∑ p ∈ T, L p) * subsetMass P T J y h := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        rw [subsetMass_insert_not_mem hq (Finset.mem_powerset.mp hT)]
        ring
      have hsecond :
          (∑ T ∈ P.powerset,
              (∑ p ∈ insert q T, L p) *
                subsetMass (insert q P) (insert q T) J y h) =
            (1 - ‖muP J y h q‖ ^ 2) *
              (L q * ∑ T ∈ P.powerset, subsetMass P T J y h +
                ∑ T ∈ P.powerset,
                  (∑ p ∈ T, L p) * subsetMass P T J y h) := by
        calc
          (∑ T ∈ P.powerset,
              (∑ p ∈ insert q T, L p) *
                subsetMass (insert q P) (insert q T) J y h) =
              ∑ T ∈ P.powerset, (1 - ‖muP J y h q‖ ^ 2) *
                (L q * subsetMass P T J y h +
                  (∑ p ∈ T, L p) * subsetMass P T J y h) := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    have hTP := Finset.mem_powerset.mp hT
                    have hqT : q ∉ T := fun hmem ↦ hq (hTP hmem)
                    rw [subsetMass_insert_insert hq hTP]
                    simp only [Finset.sum_insert hqT]
                    ring
          _ = (1 - ‖muP J y h q‖ ^ 2) *
              (L q * ∑ T ∈ P.powerset, subsetMass P T J y h +
                ∑ T ∈ P.powerset,
                  (∑ p ∈ T, L p) * subsetMass P T J y h) := by
                    simp_rw [mul_add]
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                    congr 2
                    rw [← Finset.mul_sum]
      rw [hfirst, hsecond, ih, sum_subsetMass_eq_one]
      simp only [Finset.sum_insert hq]
      ring

lemma log_prod_subset (P T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hT : T ⊆ P) :
    Real.log (∏ p ∈ T, (p : ℝ)) = ∑ p ∈ T, Real.log p := by
  rw [Real.log_prod]
  intro p hp
  exact_mod_cast (hP p (hT hp)).ne_zero

/-- Logarithmic first moment of the centered subset mass. -/
lemma sum_log_mul_subsetMass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) :
    ∑ T ∈ P.powerset,
        Real.log (∏ p ∈ T, (p : ℝ)) * subsetMass P T J y h =
      ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p := by
  calc
    (∑ T ∈ P.powerset,
        Real.log (∏ p ∈ T, (p : ℝ)) * subsetMass P T J y h) =
      ∑ T ∈ P.powerset,
        (∑ p ∈ T, Real.log p) * subsetMass P T J y h := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [log_prod_subset P T hP (Finset.mem_powerset.mp hT)]
    _ = ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p :=
      sum_powerset_sum_mul_subsetMass P (fun p : ℕ ↦ Real.log p) J y h

/-- Termwise scalar control followed by the logarithmic subset-mass identity. -/
lemma riesz_tail_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (hK : 0 < K)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ T ∈ P.powerset, (rieszLoss T K k) ^ 2 * subsetMass P T J y h) ≤
      k / K * ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p := by
  calc
    (∑ T ∈ P.powerset, (rieszLoss T K k) ^ 2 * subsetMass P T J y h) ≤
        ∑ T ∈ P.powerset,
          (k * (Real.log (∏ p ∈ T, (p : ℝ)) / K)) *
            subsetMass P T J y h := by
              apply Finset.sum_le_sum
              intro T hT
              have hTP := Finset.mem_powerset.mp hT
              have hprod : (1 : ℝ) ≤ ∏ p ∈ T, (p : ℝ) := by
                apply Finset.one_le_prod
                intro p hp
                exact_mod_cast (hP p (hTP hp)).one_lt.le
              have hx : 0 ≤ Real.log (∏ p ∈ T, (p : ℝ)) / K :=
                div_nonneg (Real.log_nonneg hprod) hK.le
              have hscalar := one_sub_rieszWeight_sq_le k hk
                (Real.log (∏ p ∈ T, (p : ℝ)) / K) hx
              rw [← rieszLoss] at hscalar
              exact mul_le_mul_of_nonneg_right hscalar
                (subsetMass_nonneg P T hP J y h)
    _ = k / K * ∑ T ∈ P.powerset,
        Real.log (∏ p ∈ T, (p : ℝ)) * subsetMass P T J y h := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          push_cast
          ring
    _ = k / K * ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p := by
      rw [sum_log_mul_subsetMass P hP J y h]

theorem rieszEnergyTail : RieszEnergyTail := by
  intro J y h P hP K hK k hk
  rw [riesz_energy_eq P hP J y h K k]
  exact riesz_tail_sum_le P hP J y h K hK k hk

end NormalNumbers.PrimeModel.SiteFactor
