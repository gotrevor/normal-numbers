/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Transfer

/-!
# G4 §4C, C3 without the sample exponential moment

`G4Transfer.norm_sampleAvg_prod_sub_prod_le` reduced C3 to two inputs, the second of which
(C3core, a Shiu-type exponential moment of the active-prime count **over the sample**) is a
project-scale sieve theorem.  This file shows it is **not needed**.

The point is *where* to expand.  Expanding `∏_p g_p` around the independent-model means `μ_p`
makes every subset term a genuine fluctuation, and the tail beyond size `M` can only be paid by
an exponential moment of `∑_p ‖g_p − μ_p‖` on the sample.  Expanding around `1` instead,

    ∏_{p∈s} g_p(n) = ∑_{T ⊆ s} ∏_{p∈T} (g_p(n) − 1),

the term of `T` vanishes unless every `p ∈ T` is *active* at `n` (`g_p(n) ≠ 1`).  So the tail
beyond size `M` is supported on `{n : V(n) > M}`, `V(n)` the number of active primes, and on
that set the truncated sum is at most `∑_{m ≤ M} C(V,m) 2^m ≤ (2eV/M)^M` — a **polynomial of
degree `M` in `V(n)`**.  A degree-`M` polynomial in `V` is a sum over `M`-tuples of primes of
indicator products with modulus `≤ R^M`, hence CRT-transferable to the independent model, where
the exponential moment `∏_p (1 + e^λ π_p)` is an exact product.

* `norm_truncation_le` — the pointwise bound `‖∏_s g − ∑_{|T|≤M} ∏_T (g−1)‖ ≤ 2 (2eV/M)^M`.
* `sampleAvg_card_pow_le` — the moment transfer
  `avg_n V(n)^M ≤ ∑_{D⊆s} |D|^M ∏_D π_p + |s|^M ε'`, given the CRT input on each `D`.
* `sum_card_pow_mul_prod_le` — `∑_{D⊆s} |D|^M ∏_D π_p ≤ (M/λ)^M ∏_p (1 + e^λ π_p)`.
* **`norm_sampleAvg_prod_sub_prod_le'`** — the assembled skeleton with *only* CRT inputs:

      ‖avg ∏_s g − ∏_s μ‖ ≤ N_M ε + λ'^{−M} ∏(1+λ' c_p)
                              + 2(2e/λ)^M ∏(1+e^λ π_p) + 2(2e/M)^M |s|^M ε'.

  With `π_p = k/p`, `c_p = 2π_p`, `∑_p π_p = μ ≍ kL` and `M = Cμ`, the two middle terms are
  `exp(−Θ(M))` once `λ' = e^{λ}`-ish constants are fixed with `C` large; both CRT errors are
  `X^{−1+o(1)}`.  Every remaining input is elementary counting.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.G4

section Truncation

variable {ι : Type*} [DecidableEq ι]

/-- Expansion of a product around `1`. -/
lemma prod_eq_sum_powerset_prod_sub_one (s : Finset ι) (g : ι → ℂ) :
    ∏ p ∈ s, g p = ∑ T ∈ s.powerset, ∏ p ∈ T, (g p - 1) := by
  rw [prod_sub_expansion s g (fun _ => 1)]
  simp

omit [DecidableEq ι] in
/-- A subset term vanishes unless the subset is inside the active set. -/
lemma prod_sub_one_eq_zero_of_not_subset {s A T : Finset ι} (g : ι → ℂ)
    (hg : ∀ p ∈ s, p ∉ A → g p = 1) (hT : T ⊆ s) (hTA : ¬ T ⊆ A) :
    ∏ p ∈ T, (g p - 1) = 0 := by
  obtain ⟨p, hpT, hpA⟩ := Finset.not_subset.1 hTA
  exact Finset.prod_eq_zero hpT (by rw [hg p (hT hpT) hpA, sub_self])

/-- `∑_{T ⊆ A, |T| ≤ M} 2^{|T|} ≤ (2eV/M)^M` when `M ≤ V = |A|`, `1 ≤ M`. -/
lemma sum_two_pow_card_le {A : Finset ι} {M : ℕ} (hM : 1 ≤ M) (hMA : M ≤ A.card) :
    ∑ T ∈ A.powerset.filter (fun T => T.card ≤ M), (2 : ℝ) ^ T.card
      ≤ (2 * Real.exp 1 * A.card / M) ^ M := by
  set V : ℝ := (A.card : ℝ) with hV
  have hVpos : (0 : ℝ) < V := by
    have : (1 : ℝ) ≤ V := by rw [hV]; exact_mod_cast hM.trans hMA
    linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMV : (M : ℝ) ≤ V := by rw [hV]; exact_mod_cast hMA
  set θ : ℝ := M / (2 * V) with hθ
  have hθpos : 0 < θ := by positivity
  have hθle : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]; linarith
  -- each term: 2^{|T|} ≤ θ^{-M} (2θ)^{|T|}
  have hterm : ∀ T ∈ A.powerset.filter (fun T => T.card ≤ M),
      (2 : ℝ) ^ T.card ≤ θ⁻¹ ^ M * (2 * θ) ^ T.card := by
    intro T hT
    have hTM : T.card ≤ M := (Finset.mem_filter.1 hT).2
    rw [mul_pow, ← mul_assoc]
    have h1 : (1 : ℝ) ≤ θ⁻¹ ^ M * θ ^ T.card := by
      have : θ⁻¹ ^ M * θ ^ T.card = θ⁻¹ ^ (M - T.card) := by
        rw [inv_pow, inv_pow, ← Nat.sub_add_cancel hTM, pow_add, Nat.add_sub_cancel]
        field_simp
      rw [this]
      exact one_le_pow₀ (one_le_inv₀ hθpos |>.2 hθle)
    calc (2 : ℝ) ^ T.card = 1 * 2 ^ T.card := (one_mul _).symm
      _ ≤ (θ⁻¹ ^ M * θ ^ T.card) * 2 ^ T.card :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = θ⁻¹ ^ M * 2 ^ T.card * θ ^ T.card := by ring
  calc ∑ T ∈ A.powerset.filter (fun T => T.card ≤ M), (2 : ℝ) ^ T.card
      ≤ ∑ T ∈ A.powerset.filter (fun T => T.card ≤ M), θ⁻¹ ^ M * (2 * θ) ^ T.card :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ T ∈ A.powerset, θ⁻¹ ^ M * (2 * θ) ^ T.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun T _ _ => by positivity)
    _ = θ⁻¹ ^ M * (1 + 2 * θ) ^ A.card := by
        rw [← Finset.mul_sum, ← Finset.prod_const, Finset.prod_one_add]
        congr 1
        exact Finset.sum_congr rfl fun T _ => by rw [Finset.prod_const]
    _ ≤ θ⁻¹ ^ M * Real.exp M := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2θ : 2 * θ = M / V := by rw [hθ]; field_simp
        calc (1 + 2 * θ) ^ A.card ≤ (Real.exp (2 * θ)) ^ A.card := by
              refine pow_le_pow_left₀ (by positivity) ?_ _
              have := Real.add_one_le_exp (2 * θ); linarith
          _ = Real.exp (2 * θ * A.card) := by rw [← Real.exp_nat_mul]; ring_nf
          _ = Real.exp M := by rw [h2θ, ← hV]; congr 1; field_simp
    _ = (2 * Real.exp 1 * V / M) ^ M := by
        rw [hθ, inv_div, ← Real.exp_one_pow, ← mul_pow]
        congr 1
        field_simp

/-- **Pointwise truncation bound.**  If `‖g p‖ ≤ 1` and `g p = 1` off the active set `A ⊆ s`,
the remainder of the expansion around `1` truncated at size `M ≥ 1` satisfies
`‖∏_s g − ∑_{|T| ≤ M} ∏_T (g − 1)‖ ≤ 2 (2e|A|/M)^M`. -/
theorem norm_truncation_le {s A : Finset ι} (g : ι → ℂ) (hg1 : ∀ p ∈ s, ‖g p‖ ≤ 1)
    (hg : ∀ p ∈ s, p ∉ A → g p = 1) (hA : A ⊆ s) {M : ℕ} (hM : 1 ≤ M) :
    ‖∏ p ∈ s, g p - ∑ T ∈ s.powerset.filter (fun T => T.card ≤ M), ∏ p ∈ T, (g p - 1)‖
      ≤ 2 * (2 * Real.exp 1 * A.card / M) ^ M := by
  rw [prod_eq_sum_powerset_prod_sub_one]
  by_cases hVM : A.card ≤ M
  · -- no active subset exceeds size `M`: the truncation is exact
    have : ∑ T ∈ s.powerset, ∏ p ∈ T, (g p - 1)
        = ∑ T ∈ s.powerset.filter (fun T => T.card ≤ M), ∏ p ∈ T, (g p - 1) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun T hT => ?_
      split_ifs with h
      · rfl
      · refine (prod_sub_one_eq_zero_of_not_subset g hg (Finset.mem_powerset.1 hT) ?_)
        intro hTA
        exact h ((Finset.card_le_card hTA).trans hVM)
    rw [this, sub_self, norm_zero]
    positivity
  · push Not at hVM
    have hbig : (1 : ℝ) ≤ (2 * Real.exp 1 * A.card / M) ^ M := by
      refine one_le_pow₀ ?_
      rw [le_div_iff₀ (by positivity)]
      have he : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hMc : (M : ℝ) ≤ A.card := by exact_mod_cast hVM.le
      have : (1 : ℝ) * (M : ℝ) ≤ (2 * Real.exp 1) * A.card := by
        apply mul_le_mul _ hMc (by positivity) (by positivity); linarith
      linarith
    rw [← prod_eq_sum_powerset_prod_sub_one]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖∏ p ∈ s, g p‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun p _ => norm_nonneg _) hg1
    have h2 : ‖∑ T ∈ s.powerset.filter (fun T => T.card ≤ M), ∏ p ∈ T, (g p - 1)‖
        ≤ (2 * Real.exp 1 * A.card / M) ^ M := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ T ∈ s.powerset.filter (fun T => T.card ≤ M), ‖∏ p ∈ T, (g p - 1)‖
          ≤ ∑ T ∈ s.powerset.filter (fun T => T.card ≤ M),
              (if T ⊆ A then (2 : ℝ) ^ T.card else 0) := by
            refine Finset.sum_le_sum fun T hT => ?_
            have hTs : T ⊆ s := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
            split_ifs with hTA
            · rw [norm_prod, ← Finset.prod_const]
              refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
              calc ‖g p - 1‖ ≤ ‖g p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                _ ≤ 1 + 1 := by rw [norm_one]; linarith [hg1 p (hTs hp)]
                _ = 2 := by norm_num
            · rw [prod_sub_one_eq_zero_of_not_subset g hg hTs hTA, norm_zero]
        _ = ∑ T ∈ (s.powerset.filter (fun T => T.card ≤ M)).filter (fun T => T ⊆ A),
              (2 : ℝ) ^ T.card := by rw [Finset.sum_filter (fun T => T ⊆ A)]
        _ = ∑ T ∈ A.powerset.filter (fun T => T.card ≤ M), (2 : ℝ) ^ T.card := by
            congr 1
            ext T
            simp only [Finset.mem_filter, Finset.mem_powerset]
            constructor
            · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1.trans hA, h2⟩, h1⟩
        _ ≤ _ := sum_two_pow_card_le hM hVM.le
    linarith

end Truncation

section Moment

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- `k^M ≤ (M/λ)^M e^{λk}` for `k ≥ 0`, `λ > 0` (from `(λk)^M/M! ≤ e^{λk}` and `M! ≤ M^M`). -/
lemma pow_le_div_pow_mul_exp {k : ℝ} (hk : 0 ≤ k) {lam : ℝ} (hlam : 0 < lam) (M : ℕ) :
    k ^ M ≤ ((M : ℝ) / lam) ^ M * Real.exp (lam * k) := by
  have h1 := Real.pow_div_factorial_le_exp (lam * k) (mul_nonneg hlam.le hk) M
  have h2 : ((M.factorial : ℕ) : ℝ) ≤ (M : ℝ) ^ M := by exact_mod_cast Nat.factorial_le_pow M
  have hf : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  rw [div_le_iff₀ hf] at h1
  have h3 : (lam * k) ^ M ≤ (M : ℝ) ^ M * Real.exp (lam * k) := by
    refine h1.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  rw [mul_pow] at h3
  rw [div_pow]
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hlam M)]
  linarith [h3]

/-- **The independent-model moment.**  `∑_{D ⊆ s} |D|^M ∏_{p∈D} π_p ≤ (M/λ)^M ∏_p (1 + e^λ π_p)`.
This is `𝔼 V^M ≤ (M/λ)^M 𝔼 e^{λV}` for independent Bernoulli(`π_p`) summands, written as an
exact identity of finite sums so that no probability space is needed. -/
lemma sum_card_pow_mul_prod_le (s : Finset ι) (π : ι → ℝ) (hπ : ∀ p ∈ s, 0 ≤ π p)
    {lam : ℝ} (hlam : 0 < lam) (M : ℕ) :
    ∑ D ∈ s.powerset, (D.card : ℝ) ^ M * ∏ p ∈ D, π p
      ≤ ((M : ℝ) / lam) ^ M * ∏ p ∈ s, (1 + Real.exp lam * π p) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_le_sum fun D hD => ?_
  have hDs : D ⊆ s := Finset.mem_powerset.1 hD
  have hprod : 0 ≤ ∏ p ∈ D, π p := Finset.prod_nonneg fun p hp => hπ p (hDs hp)
  have hk := pow_le_div_pow_mul_exp (Nat.cast_nonneg D.card) hlam M
  calc (D.card : ℝ) ^ M * ∏ p ∈ D, π p
      ≤ (((M : ℝ) / lam) ^ M * Real.exp (lam * D.card)) * ∏ p ∈ D, π p :=
        mul_le_mul_of_nonneg_right hk hprod
    _ = ((M : ℝ) / lam) ^ M * ∏ p ∈ D, (Real.exp lam * π p) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul, mul_comm (D.card : ℝ)]
        ring

/-- `|A|^M` as a sum over `M`-tuples from `s ⊇ A` of the indicator that the tuple's range lies
in `A`. -/
lemma card_pow_eq_sum_piFinset {s A : Finset ι} (hA : A ⊆ s) (M : ℕ) :
    ((A.card : ℝ)) ^ M
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin M => s),
          (if Finset.image x Finset.univ ⊆ A then (1 : ℝ) else 0) := by
  have hcard : (A.card : ℝ) = ∑ p ∈ s, (if p ∈ A then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    congr 2
    exact (Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.2 hA)).symm
  rw [hcard, ← Fin.prod_const M, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.image_subset_iff, Finset.mem_univ, true_implies]

/-- **The moment transfer.**  If every CRT-reachable indicator (`D ⊆ s` nonempty, `|D| ≤ M`)
has sample average at most its independent-model value plus `ε'`, then the sample `M`-th moment
of the active count is at most the independent-model moment plus `|s|^M ε'`. -/
theorem sampleAvg_card_pow_le (P : Finset ℕ) (s : Finset ι) (Act : ℕ → Finset ι)
    (hAct : ∀ n, Act n ⊆ s) (π : ι → ℝ) (hπ : ∀ p ∈ s, 0 ≤ π p) {ε' : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hcrt : ∀ D ∈ s.powerset, D.Nonempty → D.card ≤ M →
        sampleAvg P id (fun n => if D ⊆ Act n then (1 : ℝ) else 0) ≤ ∏ p ∈ D, π p + ε') :
    sampleAvg P id (fun n => ((Act n).card : ℝ) ^ M)
      ≤ ∑ D ∈ s.powerset, (D.card : ℝ) ^ M * ∏ p ∈ D, π p + (s.card : ℝ) ^ M * ε' := by
  have hfun : (fun n => ((Act n).card : ℝ) ^ M)
      = fun n => ∑ x ∈ Fintype.piFinset (fun _ : Fin M => s),
          (if Finset.image x Finset.univ ⊆ Act n then (1 : ℝ) else 0) := by
    funext n; exact card_pow_eq_sum_piFinset (hAct n) M
  rw [hfun, sampleAvg_id_sum]
  have hne : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  calc ∑ x ∈ Fintype.piFinset (fun _ : Fin M => s),
        sampleAvg P id (fun n => if Finset.image x Finset.univ ⊆ Act n then (1 : ℝ) else 0)
      ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin M => s),
          (∏ p ∈ Finset.image x Finset.univ, π p + ε') := by
        refine Finset.sum_le_sum fun x hx => ?_
        refine hcrt _ ?_ ?_ ?_
        · rw [Finset.mem_powerset, Finset.image_subset_iff]
          intro i _
          exact (Fintype.mem_piFinset.1 hx) i
        · exact (Finset.univ_nonempty).image x
        · exact (Finset.card_image_le).trans (by simp)
    _ = ∑ x ∈ Fintype.piFinset (fun _ : Fin M => s), ∏ p ∈ Finset.image x Finset.univ, π p
          + (s.card : ℝ) ^ M * ε' := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset_const]
        push_cast; ring
    _ ≤ _ := by
        gcongr
        -- group the tuples by their range
        rw [← Finset.sum_fiberwise_of_maps_to (t := s.powerset)
          (g := fun x : Fin M → ι => Finset.image x Finset.univ)
          (fun x hx => by
            rw [Finset.mem_powerset, Finset.image_subset_iff]
            intro i _
            exact (Fintype.mem_piFinset.1 hx) i)]
        refine Finset.sum_le_sum fun D hD => ?_
        have hDs : D ⊆ s := Finset.mem_powerset.1 hD
        have hprod : 0 ≤ ∏ p ∈ D, π p := Finset.prod_nonneg fun p hp => hπ p (hDs hp)
        calc ∑ x ∈ (Fintype.piFinset (fun _ : Fin M => s)).filter
                (fun x => Finset.image x Finset.univ = D), ∏ p ∈ Finset.image x Finset.univ, π p
            = ∑ x ∈ (Fintype.piFinset (fun _ : Fin M => s)).filter
                (fun x => Finset.image x Finset.univ = D), ∏ p ∈ D, π p := by
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [(Finset.mem_filter.1 hx).2]
          _ = (((Fintype.piFinset (fun _ : Fin M => s)).filter
                (fun x => Finset.image x Finset.univ = D)).card : ℝ) * ∏ p ∈ D, π p := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (D.card : ℝ) ^ M * ∏ p ∈ D, π p := by
              refine mul_le_mul_of_nonneg_right ?_ hprod
              have : ((Fintype.piFinset (fun _ : Fin M => s)).filter
                  (fun x => Finset.image x Finset.univ = D))
                  ⊆ Fintype.piFinset (fun _ : Fin M => D) := by
                intro x hx
                rw [Fintype.mem_piFinset]
                intro i
                rw [← (Finset.mem_filter.1 hx).2]
                exact Finset.mem_image_of_mem x (Finset.mem_univ i)
              have h := Finset.card_le_card this
              rw [Fintype.card_piFinset_const] at h
              exact_mod_cast h

end Moment

section Assembly

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma sampleAvg_id_add {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Finset ℕ) (u v : ℕ → E) :
    sampleAvg P id (fun n => u n + v n) = sampleAvg P id u + sampleAvg P id v := by
  unfold sampleAvg
  simp only [id_eq, Finset.sum_add_distrib, smul_add]

/-- **The C3 skeleton with CRT-only inputs.**  Compare `norm_sampleAvg_prod_sub_prod_le`: the
sample exponential moment `B` is gone.  Its place is taken by the independent-model product
`∏_p (1 + e^λ π_p)`, an exact finite product, reached through the degree-`M` moment of the
active count, which is CRT-transferable (`hcrt`).

Inputs: `‖g p n‖ ≤ 1`; `g p n = 1` when `p` is not active at `n`; `‖μ p − 1‖ ≤ c p`;
`hsmall` (C3a, around `1`) and `hcrt` (the indicator version of C3a).  Both are the same
elementary CRT/equidistribution count on a modulus `∏_{p∈T} p ≤ R^M`. -/
theorem norm_sampleAvg_prod_sub_prod_le' (P : Finset ℕ) (hP : P.Nonempty) (s : Finset ι)
    (g : ι → ℕ → ℂ) (Act : ℕ → Finset ι) (hAct : ∀ n, Act n ⊆ s)
    (hg1 : ∀ p ∈ s, ∀ n, ‖g p n‖ ≤ 1) (hg : ∀ p ∈ s, ∀ n, p ∉ Act n → g p n = 1)
    (μ : ι → ℂ) (c : ι → ℝ) (hc : ∀ p ∈ s, 0 ≤ c p) (hμc : ∀ p ∈ s, ‖μ p - 1‖ ≤ c p)
    (π : ι → ℝ) (hπ : ∀ p ∈ s, 0 ≤ π p)
    {M : ℕ} (hM : 1 ≤ M) {lam' lam ε ε' : ℝ} (hlam' : 1 ≤ lam') (hlam : 0 < lam)
    (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hsmall : ∀ T ∈ s.powerset, T.Nonempty → T.card ≤ M →
        ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) - ∏ p ∈ T, (μ p - 1)‖ ≤ ε)
    (hcrt : ∀ D ∈ s.powerset, D.Nonempty → D.card ≤ M →
        sampleAvg P id (fun n => if D ⊆ Act n then (1 : ℝ) else 0) ≤ ∏ p ∈ D, π p + ε') :
    ‖sampleAvg P id (fun n => ∏ p ∈ s, g p n) - ∏ p ∈ s, μ p‖
      ≤ (s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card * ε
        + (∏ p ∈ s, (1 + lam' * c p)) / lam' ^ M
        + 2 * (2 * Real.exp 1 / lam) ^ M * ∏ p ∈ s, (1 + Real.exp lam * π p)
        + 2 * (2 * Real.exp 1 / M) ^ M * (s.card : ℝ) ^ M * ε' := by
  classical
  have hcard : (P.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hP.choose_spec)
  set F := s.powerset.filter (fun T => T.card ≤ M) with hF
  set Rem : ℕ → ℂ := fun n => ∏ p ∈ s, g p n - ∑ T ∈ F, ∏ p ∈ T, (g p n - 1) with hRem
  -- the model value, split at size `M`
  have hμsplit : ∏ p ∈ s, μ p
      = ∑ T ∈ F, ∏ p ∈ T, (μ p - 1)
        + ∑ T ∈ s.powerset.filter (fun T => ¬ T.card ≤ M), ∏ p ∈ T, (μ p - 1) := by
    rw [prod_eq_sum_powerset_prod_sub_one, ← Finset.sum_filter_add_sum_filter_not s.powerset
      (fun T => T.card ≤ M)]
  -- the sample value, split the same way
  have hgsplit : sampleAvg P id (fun n => ∏ p ∈ s, g p n)
      = ∑ T ∈ F, sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) + sampleAvg P id Rem := by
    rw [← sampleAvg_id_sum]
    rw [← sampleAvg_id_add]
    congr 1
    funext n
    simp only [hRem, add_sub_cancel]
  rw [hgsplit, hμsplit]
  have hrearr : ∑ T ∈ F, sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) + sampleAvg P id Rem
      - (∑ T ∈ F, ∏ p ∈ T, (μ p - 1)
          + ∑ T ∈ s.powerset.filter (fun T => ¬ T.card ≤ M), ∏ p ∈ T, (μ p - 1))
      = ∑ T ∈ F, (sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) - ∏ p ∈ T, (μ p - 1))
        + sampleAvg P id Rem
        - ∑ T ∈ s.powerset.filter (fun T => ¬ T.card ≤ M), ∏ p ∈ T, (μ p - 1) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hrearr]
  have htri : ∀ a b c : ℂ, ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := fun a b c => by
    have := norm_sub_le (a + b) c
    have := norm_add_le a b
    linarith
  refine (htri _ _ _).trans ?_
  -- (1) the CRT-reachable subsets
  have h1 : ‖∑ T ∈ F, (sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) - ∏ p ∈ T, (μ p - 1))‖
      ≤ (s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M)).card * ε := by
    refine (norm_sum_le _ _).trans ?_
    have hFF : s.powerset.filter (fun T => T.Nonempty ∧ T.card ≤ M) = F.filter (fun T => T.Nonempty) := by
      rw [hF, Finset.filter_filter]
      congr 1
      ext T; simp only [and_comm]
    rw [hFF, ← Finset.sum_filter_add_sum_filter_not F (fun T => T.Nonempty)]
    have hempty : ∑ T ∈ F.filter (fun T => ¬ T.Nonempty),
        ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) - ∏ p ∈ T, (μ p - 1)‖ = 0 := by
      refine Finset.sum_eq_zero fun T hT => ?_
      have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hT).2
      subst hT0
      simp only [Finset.prod_empty]
      have : sampleAvg P id (fun _ : ℕ => (1 : ℂ)) = 1 := by
        unfold sampleAvg
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Complex.real_smul,
          Complex.ofReal_inv, Complex.ofReal_natCast]
        exact inv_mul_cancel₀ (by exact_mod_cast hcard)
      rw [this, sub_self, norm_zero]
    rw [hempty, add_zero]
    calc ∑ T ∈ F.filter (fun T => T.Nonempty),
          ‖sampleAvg P id (fun n => ∏ p ∈ T, (g p n - 1)) - ∏ p ∈ T, (μ p - 1)‖
        ≤ ∑ _T ∈ F.filter (fun T => T.Nonempty), ε := by
          refine Finset.sum_le_sum fun T hT => ?_
          obtain ⟨hTF, hTne⟩ := Finset.mem_filter.1 hT
          obtain ⟨hTs, hTM⟩ := Finset.mem_filter.1 hTF
          exact hsmall T hTs hTne hTM
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- (2) the sample truncation remainder, through the moment transfer
  have h2 : ‖sampleAvg P id Rem‖
      ≤ 2 * (2 * Real.exp 1 / lam) ^ M * ∏ p ∈ s, (1 + Real.exp lam * π p)
        + 2 * (2 * Real.exp 1 / M) ^ M * (s.card : ℝ) ^ M * ε' := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hpt : ∀ n, ‖Rem n‖ ≤ 2 * (2 * Real.exp 1 / M) ^ M * ((Act n).card : ℝ) ^ M := by
      intro n
      have := norm_truncation_le (s := s) (A := Act n) (fun p => g p n)
        (fun p hp => hg1 p hp n) (fun p hp hpA => hg p hp n hpA) (hAct n) hM
      calc ‖Rem n‖ ≤ 2 * (2 * Real.exp 1 * ((Act n).card : ℝ) / M) ^ M := this
        _ = 2 * (2 * Real.exp 1 / M) ^ M * ((Act n).card : ℝ) ^ M := by
          rw [mul_assoc (2 : ℝ) ((2 * Real.exp 1 / M) ^ M), ← mul_pow]; congr 2; ring
    calc ‖sampleAvg P id Rem‖ ≤ sampleAvg P id (fun n => ‖Rem n‖) := norm_sampleAvg_id_le_avg_norm P _
      _ ≤ sampleAvg P id (fun n => 2 * (2 * Real.exp 1 / M) ^ M * ((Act n).card : ℝ) ^ M) :=
          sampleAvg_id_mono P fun n _ => hpt n
      _ = 2 * (2 * Real.exp 1 / M) ^ M * sampleAvg P id (fun n => ((Act n).card : ℝ) ^ M) :=
          sampleAvg_id_const_smul P _ _
      _ ≤ 2 * (2 * Real.exp 1 / M) ^ M
            * (∑ D ∈ s.powerset, (D.card : ℝ) ^ M * ∏ p ∈ D, π p + (s.card : ℝ) ^ M * ε') := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sampleAvg_card_pow_le P s Act hAct π hπ hM hcrt
      _ ≤ 2 * (2 * Real.exp 1 / M) ^ M
            * (((M : ℝ) / lam) ^ M * ∏ p ∈ s, (1 + Real.exp lam * π p) + (s.card : ℝ) ^ M * ε') := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact add_le_add (sum_card_pow_mul_prod_le s π hπ hlam M) le_rfl
      _ = _ := by
          have : (2 * Real.exp 1 / M) ^ M * ((M : ℝ) / lam) ^ M = (2 * Real.exp 1 / lam) ^ M := by
            rw [← mul_pow]; congr 1; field_simp
          rw [mul_add, mul_assoc (2 * (2 * Real.exp 1 / M) ^ M), ← mul_assoc _ _ (∏ p ∈ s, _)]
          rw [mul_assoc (2 : ℝ), this]
  -- (3) the independent-model tail
  have h3 : ‖∑ T ∈ s.powerset.filter (fun T => ¬ T.card ≤ M), ∏ p ∈ T, (μ p - 1)‖
      ≤ (∏ p ∈ s, (1 + lam' * c p)) / lam' ^ M := by
    have hlamM : (0 : ℝ) < lam' ^ M := by positivity
    refine (norm_sum_le _ _).trans ?_
    rw [le_div_iff₀ hlamM]
    calc (∑ T ∈ s.powerset.filter (fun T => ¬ T.card ≤ M), ‖∏ p ∈ T, (μ p - 1)‖) * lam' ^ M
        ≤ (∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, c p) * lam' ^ M := by
          refine mul_le_mul_of_nonneg_right ?_ hlamM.le
          have hfe : s.powerset.filter (fun T => ¬ T.card ≤ M)
              = s.powerset.filter (fun T => M < T.card) := by
            congr 1; ext T; simp only [not_le]
          rw [hfe]
          refine Finset.sum_le_sum fun T hT => ?_
          have hTs : T ⊆ s := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
          rw [norm_prod]
          exact Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => hμc p (hTs hp)
      _ = lam' ^ M * ∑ T ∈ s.powerset.filter (fun T => M < T.card), ∏ p ∈ T, c p := mul_comm _ _
      _ ≤ _ := mul_pow_sum_powerset_card_gt_le c hc M hlam'
  linarith [h1, h2, h3]

end Assembly

end NormalNumbers.G4
