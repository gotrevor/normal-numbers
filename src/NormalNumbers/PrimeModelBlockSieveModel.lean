import NormalNumbers.PrimeModelBlockSieve

/-!
# Lemma B, part 2: the relative defect under the product model

Lap 2 of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §3
"Relative defect" and `papers/ROUND2-multicutoff-astra.md` §4.  Still no arithmetic: this file is
about a finite family of blocks with independent block statistics.

* `model_defect` — if `V i ≤ E[U i] ≤ V i (1 + D̄ i)` with `V i > 0`, `D̄ i ≥ 0`, then
  `E[L] = ∏ E[U] − ∑ V_i D̄_i ∏_{j≠i} E[U_j] ≥ (∏ V)(1 − (∑ D̄) e^{∑ D̄})`.
  This is the packaged form of `E[L] ≥ (1 − η) ∏ V`.
* `exp_neg_two_mul_le_one_sub` — `e^{−2t} ≤ 1 − t` on `[0, 1/2]`, the inequality behind
  `V ≥ e^{−2λ}` (and the only place `2 d_p ≤ p` is used).
* `esymm_le_pow_div_factorial` — `∑_{E ⊆ B, |E| = k} ∏_E g ≤ (∑_B g)^k / k!` for `g ≥ 0`,
  the bound on `E[D] = e_{r+1}(g)`.
-/

open Finset

namespace NormalNumbers.PrimeModel.BlockSieve

variable {ι : Type*} [DecidableEq ι]

/-! ### The abstract model defect -/

/-- **Fable §3, relative defect** in abstract form: the model expectation of the graded block
minorant is at least `(∏ V)(1 − (∑ D̄) e^{∑ D̄})`. -/
theorem model_defect (s : Finset ι) (V Ub Db : ι → ℝ)
    (hV : ∀ i ∈ s, 0 < V i) (hDb : ∀ i ∈ s, 0 ≤ Db i)
    (hlow : ∀ i ∈ s, V i ≤ Ub i) (hhigh : ∀ i ∈ s, Ub i ≤ V i * (1 + Db i)) :
    (∏ i ∈ s, V i) * (1 - (∑ i ∈ s, Db i) * Real.exp (∑ i ∈ s, Db i))
      ≤ (∏ i ∈ s, Ub i) - ∑ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j := by
  classical
  have hUbnn : ∀ i ∈ s, 0 ≤ Ub i := fun i hi => (hV i hi).le.trans (hlow i hi)
  have hVprod : 0 < ∏ i ∈ s, V i := Finset.prod_pos hV
  -- (1) `∏ V ≤ ∏ Ub`
  have h1 : (∏ i ∈ s, V i) ≤ ∏ i ∈ s, Ub i :=
    Finset.prod_le_prod (fun i hi => (hV i hi).le) hlow
  -- (2) `∏_{j ∈ s} (1 + D̄ j) ≤ exp (∑ D̄)`
  have hexp : (∏ i ∈ s, (1 + Db i)) ≤ Real.exp (∑ i ∈ s, Db i) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun i hi => by linarith [hDb i hi]) (fun i _ => ?_)
    rw [add_comm]
    exact Real.add_one_le_exp _
  have hexpnn : 0 ≤ Real.exp (∑ i ∈ s, Db i) := (Real.exp_pos _).le
  -- (3) each defect term is at most `D̄ i (∏ V) exp (∑ D̄)`
  have h2 : ∀ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j
      ≤ Db i * ((∏ j ∈ s, V j) * Real.exp (∑ j ∈ s, Db j)) := by
    intro i hi
    have hsub : ∀ j ∈ s.erase i, j ∈ s := fun j hj => Finset.mem_of_mem_erase hj
    have hstep : (∏ j ∈ s.erase i, Ub j) ≤ ∏ j ∈ s.erase i, (V j * (1 + Db j)) :=
      Finset.prod_le_prod (fun j hj => hUbnn j (hsub j hj)) (fun j hj => hhigh j (hsub j hj))
    have hsplit : (∏ j ∈ s.erase i, (V j * (1 + Db j)))
        = (∏ j ∈ s.erase i, V j) * ∏ j ∈ s.erase i, (1 + Db j) := Finset.prod_mul_distrib
    have hVi : V i * ∏ j ∈ s.erase i, V j = ∏ j ∈ s, V j := Finset.mul_prod_erase s V hi
    have honenn' : 0 ≤ ∏ j ∈ s.erase i, (1 + Db j) :=
      Finset.prod_nonneg fun j hj => by linarith [hDb j (Finset.mem_of_mem_erase hj)]
    have hone : (∏ j ∈ s.erase i, (1 + Db j)) ≤ ∏ j ∈ s, (1 + Db j) := by
      have hfac : (1 + Db i) * ∏ j ∈ s.erase i, (1 + Db j) = ∏ j ∈ s, (1 + Db j) :=
        Finset.mul_prod_erase s (fun j => 1 + Db j) hi
      nlinarith [hDb i hi, honenn']
    have hprodnn : 0 ≤ ∏ j ∈ s.erase i, V j :=
      Finset.prod_nonneg fun j hj => (hV j (hsub j hj)).le
    have honenn : 0 ≤ ∏ j ∈ s.erase i, (1 + Db j) :=
      Finset.prod_nonneg fun j hj => by linarith [hDb j (hsub j hj)]
    have hDbi : 0 ≤ Db i := hDb i hi
    have hVipos : 0 < V i := hV i hi
    calc (V i * Db i) * ∏ j ∈ s.erase i, Ub j
        ≤ (V i * Db i) * ((∏ j ∈ s.erase i, V j) * ∏ j ∈ s.erase i, (1 + Db j)) := by
          refine mul_le_mul_of_nonneg_left (hstep.trans_eq hsplit) ?_
          positivity
      _ = Db i * ((V i * ∏ j ∈ s.erase i, V j) * ∏ j ∈ s.erase i, (1 + Db j)) := by ring
      _ = Db i * ((∏ j ∈ s, V j) * ∏ j ∈ s.erase i, (1 + Db j)) := by rw [hVi]
      _ ≤ Db i * ((∏ j ∈ s, V j) * Real.exp (∑ j ∈ s, Db j)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hone.trans hexp) hVprod.le)
            hDbi
  have h3 : (∑ i ∈ s, (V i * Db i) * ∏ j ∈ s.erase i, Ub j)
      ≤ (∑ i ∈ s, Db i) * ((∏ j ∈ s, V j) * Real.exp (∑ j ∈ s, Db j)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum h2
  nlinarith [hVprod, hexpnn]

/-! ### `1 − t ≥ e^{−2t}` on `[0, 1/2]` -/

/-- On `[0, 1/2]`, `e^{−2t} ≤ 1 − t`.  Proof: `1/(1−t) ≤ 1 + 2t ≤ e^{2t}`, the first step
being `t(1 − 2t) ≥ 0`. -/
theorem exp_neg_two_mul_le_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Real.exp (-(2 * t)) ≤ 1 - t := by
  have hlt : 0 < 1 - t := by linarith
  have hexp : 1 + 2 * t ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t)
    linarith
  have hinv : 1 ≤ (1 + 2 * t) * (1 - t) := by nlinarith
  have hkey : 1 ≤ Real.exp (2 * t) * (1 - t) := by nlinarith [Real.exp_pos (2 * t)]
  have hexppos : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hexppos]
  linarith

/-! ### `e_k(g) ≤ (∑ g)^k / k!` -/

variable {α : Type*} [DecidableEq α]

/-- The `k`-th elementary symmetric sum of `g` over `B`. -/
noncomputable def esymmOn (g : α → ℝ) (B : Finset α) (k : ℕ) : ℝ :=
  ∑ E ∈ B.powersetCard k, ∏ p ∈ E, g p

/-- **The factorial bound**: `k! · e_k(g) ≤ (∑_B g)^k` for a nonnegative weight. -/
theorem factorial_mul_esymmOn_le (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) :
    ∀ (B : Finset α) (k : ℕ), (k.factorial : ℝ) * esymmOn g B k ≤ (∑ p ∈ B, g p) ^ k := by
  sorry

end NormalNumbers.PrimeModel.BlockSieve
