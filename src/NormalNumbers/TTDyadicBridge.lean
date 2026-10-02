/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureTTEquidistributedDefect

/-!
# `TTEquidistributedReal → TTEquidistributedDyadic`

Proof of the bridge stated in `LiteratureTTDyadicReferee.lean`.  Set `c' = min c 1 / 4`,
`η = L^{-2c'}`.  A scale `j` is declared exceptional if it is the top scale (`X < 2^{j+2}`) or some
natural `N` of its block has its whole window `[N, N(1+η)]` inside TT's `E`.

* `perturb_bound` — from a good real `N' ∈ [N, N(1+η)]` to the natural `N`: (3.1) at `q = 1`
  transfers `δ` (`|δ N − δ N'| ≤ 3/L + 6η`), boundary terms cost `4` each.
* `card_mul_le_integral` — windows of same-parity scales are disjoint, so
  `#bad · η/2 ≤ 2 ∫_E dt/t`.
* `log_le_card_dyadicScales` — `log X ≤ 6 · #scales` once a scale exists.
-/

open MeasureTheory

namespace NormalNumbers.CastingOut.TTBridge

/-- Moving the endpoints of an `Ioc` window costs at most `B` per added or dropped term. -/
theorem norm_sum_Ioc_sub_le {F : ℕ → ℂ} {B : ℝ} (hF : ∀ n, ‖F n‖ ≤ B)
    {N a M b : ℕ} (h1 : N ≤ a) (h2 : a ≤ M) (h3 : M ≤ b) :
    ‖(∑ n ∈ Finset.Ioc N M, F n) - ∑ n ∈ Finset.Ioc a b, F n‖
      ≤ B * (((a : ℝ) - N) + ((b : ℝ) - M)) := by
  rw [← Finset.sum_Ioc_consecutive F h1 h2, ← Finset.sum_Ioc_consecutive F h2 h3]
  have e : (∑ n ∈ Finset.Ioc N a, F n) + (∑ n ∈ Finset.Ioc a M, F n)
      - ((∑ n ∈ Finset.Ioc a M, F n) + ∑ n ∈ Finset.Ioc M b, F n)
      = (∑ n ∈ Finset.Ioc N a, F n) - ∑ n ∈ Finset.Ioc M b, F n := by ring
  rw [e]
  have hA := norm_sum_le_of_le (Finset.Ioc N a) (fun n _ => hF n)
  have hB := norm_sum_le_of_le (Finset.Ioc M b) (fun n _ => hF n)
  simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul] at hA hB
  rw [Nat.cast_sub h1] at hA
  rw [Nat.cast_sub h3] at hB
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

/-- `∫_{[N, N(1+η)]} dt/t ≥ η/2`. -/
theorem half_le_integral_inv {N η : ℝ} (hN : 0 < N) (hη : 0 < η) (hη1 : η ≤ 1) :
    η / 2 ≤ ∫ t in Set.Icc N (N * (1 + η)), t⁻¹ := by
  have hle : N ≤ N * (1 + η) := by nlinarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    integral_inv_of_pos hN (by positivity)]
  rw [show N * (1 + η) / N = 1 + η by field_simp]
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + η)⁻¹ by positivity)
  rw [Real.log_inv] at h
  have h3 : η / 2 ≤ η / (1 + η) := div_le_div_of_nonneg_left hη.le (by linarith) (by linarith)
  have h4 : (1 + η)⁻¹ - 1 = -(η / (1 + η)) := by field_simp; ring
  linarith

/-- **Perturbation from a real point `N'` to a natural `N ≤ N' ≤ N(1+η)`.**  Uses (3.1) at
`q = 1` at both points to transfer `δ` (`|δ N − δ N'| ≤ 3/L + 6η`), then pays `4` per boundary
term.  Crude counts suffice: the cost `W(18η + 3/L)` is absorbed later by `W ≤ L^{c'}`,
`η = L^{-2c'}`. -/
theorem perturb_bound {g₁ g₂ : ℕ → ℂ} (hb₁ : ∀ n, ‖g₁ n‖ ≤ 1) (hb₂ : ∀ n, ‖g₂ n‖ ≤ 1)
    {δ : ℝ → ℝ} {L η K : ℝ} (hL : 1 ≤ L) (hη : 0 < η) (hη1 : η ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {N' : ℝ} (hN1 : (N : ℝ) ≤ N') (hN2 : N' ≤ N * (1 + η))
    (h31N : ‖(∑ n ∈ Finset.Ioc N (2 * N), g₁ n) - (((N : ℝ) * δ N : ℝ) : ℂ)‖ ≤ N / L)
    (h31N' : ‖(∑ n ∈ Finset.Ioc ⌊N'⌋₊ ⌊2 * N'⌋₊, g₁ n) - ((N' * δ N' : ℝ) : ℂ)‖ ≤ N' / L)
    {W b h₁ h₂ : ℕ} (hW : 0 < W)
    (hTT : ‖((W : ℝ) / N' : ℝ) •
        ∑ n ∈ (Finset.Ioc ⌊N'⌋₊ ⌊2 * N'⌋₊).filter (fun n => n % W = b % W),
          (g₁ (n + h₁) - ((δ N' : ℝ) : ℂ)) * g₂ (n + h₂)‖ ≤ K) :
    ‖((W : ℝ) / (N : ℝ) : ℝ) •
        ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => n % W = b % W),
          (g₁ (n + h₁) - ((δ N : ℝ) : ℂ)) * g₂ (n + h₂)‖
      ≤ 2 * K + W * (18 * η + 3 / L) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN'pos : 0 < N' := by linarith
  have hL0 : 0 < L := by linarith
  set a := ⌊N'⌋₊ with ha
  set c := ⌊2 * N'⌋₊ with hc
  have haN : N ≤ a := Nat.le_floor hN1
  have ha_le : (a : ℝ) ≤ N' := Nat.floor_le hN'pos.le
  have ha_gt : N' < a + 1 := Nat.lt_floor_add_one N'
  have hc_le : (c : ℝ) ≤ 2 * N' := Nat.floor_le (by linarith)
  have hNc : 2 * N ≤ c := Nat.le_floor (by push_cast; linarith)
  have ha2N : a ≤ 2 * N := by
    have : (a : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this
  have hac : a ≤ c := le_trans ha2N hNc
  have hdA : (a : ℝ) - N ≤ η * N := by nlinarith
  have hdC : (c : ℝ) - ((2 * N : ℕ) : ℝ) ≤ 2 * η * N := by push_cast; nlinarith
  -- `|δ N'| ≤ 3`
  have hS' : ‖∑ n ∈ Finset.Ioc a c, g₁ n‖ ≤ N' + 1 := by
    have h := norm_sum_le_of_le (Finset.Ioc a c) (fun n _ => hb₁ n)
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one] at h
    rw [Nat.cast_sub hac] at h
    linarith
  have hδ' : |δ N'| ≤ 3 := by
    have h1 : ‖((N' * δ N' : ℝ) : ℂ)‖ ≤ ‖∑ n ∈ Finset.Ioc a c, g₁ n‖ + N' / L := by
      have := norm_sub_le (∑ n ∈ Finset.Ioc a c, g₁ n)
        ((∑ n ∈ Finset.Ioc a c, g₁ n) - ((N' * δ N' : ℝ) : ℂ))
      rw [sub_sub_cancel] at this
      linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hN'pos] at h1
    have hNL : N' / L ≤ N' := div_le_self hN'pos.le hL
    have : N' * |δ N'| ≤ N' * 3 := by linarith
    exact le_of_mul_le_mul_left this hN'pos
  -- δ transfer
  have hSS : ‖(∑ n ∈ Finset.Ioc N (2 * N), g₁ n) - ∑ n ∈ Finset.Ioc a c, g₁ n‖ ≤ 3 * η * N := by
    have h := norm_sum_Ioc_sub_le hb₁ haN ha2N hNc
    linarith
  have hdiff : |(N : ℝ) * δ N - N' * δ N'| ≤ 3 * N / L + 3 * η * N := by
    have e : (((N : ℝ) * δ N - N' * δ N' : ℝ) : ℂ)
        = ((∑ n ∈ Finset.Ioc a c, g₁ n) - ((N' * δ N' : ℝ) : ℂ))
          - ((∑ n ∈ Finset.Ioc N (2 * N), g₁ n) - (((N : ℝ) * δ N : ℝ) : ℂ))
          + ((∑ n ∈ Finset.Ioc N (2 * N), g₁ n) - ∑ n ∈ Finset.Ioc a c, g₁ n) := by
      push_cast; ring
    have h := congrArg norm e
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    rw [h]
    have hN'L : N' / L ≤ 2 * N / L := by
      apply div_le_div_of_nonneg_right _ hL0.le; nlinarith
    calc _ ≤ ‖((∑ n ∈ Finset.Ioc a c, g₁ n) - ((N' * δ N' : ℝ) : ℂ))
          - ((∑ n ∈ Finset.Ioc N (2 * N), g₁ n) - (((N : ℝ) * δ N : ℝ) : ℂ))‖
          + ‖(∑ n ∈ Finset.Ioc N (2 * N), g₁ n) - ∑ n ∈ Finset.Ioc a c, g₁ n‖ := norm_add_le _ _
      _ ≤ (N' / L + N / L) + 3 * η * N := add_le_add (norm_sub_le_of_le h31N' h31N) hSS
      _ ≤ _ := by
        have : (N : ℝ) / L + 2 * N / L = 3 * N / L := by ring
        linarith
  have hΔ : |δ N - δ N'| ≤ 3 / L + 6 * η := by
    have e : (N : ℝ) * (δ N - δ N') = (N * δ N - N' * δ N') + (N' - N) * δ N' := by ring
    have h2 : |(N' - N) * δ N'| ≤ η * N * 3 := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ N' - N)]
      exact mul_le_mul (by nlinarith) hδ' (abs_nonneg _) (by positivity)
    have h3 : (N : ℝ) * |δ N - δ N'| ≤ N * (3 / L + 6 * η) := by
      have h0 : (N : ℝ) * |δ N - δ N'| = |(N : ℝ) * (δ N - δ N')| := by
        rw [abs_mul, abs_of_pos hNpos]
      rw [h0, e]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ 3 * N / L + 3 * η * N + η * N * 3 := add_le_add hdiff h2
        _ = _ := by ring
    exact le_of_mul_le_mul_left h3 hNpos
  -- main sum
  set F : ℝ → ℕ → ℂ := fun d n =>
    if n % W = b % W then (g₁ (n + h₁) - ((d : ℝ) : ℂ)) * g₂ (n + h₂) else 0 with hF
  have hsum : ∀ (d : ℝ) (A B : ℕ),
      ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % W = b % W),
        (g₁ (n + h₁) - ((d : ℝ) : ℂ)) * g₂ (n + h₂) = ∑ n ∈ Finset.Ioc A B, F d n := by
    intro d A B; rw [Finset.sum_filter]
  rw [hsum] at hTT ⊢
  have hFb : ∀ n, ‖F (δ N') n‖ ≤ 4 := by
    intro n; simp only [hF]; split_ifs
    · rw [norm_mul]
      have h1 : ‖g₁ (n + h₁) - ((δ N' : ℝ) : ℂ)‖ ≤ 4 := by
        calc _ ≤ ‖g₁ (n + h₁)‖ + ‖((δ N' : ℝ) : ℂ)‖ := norm_sub_le _ _
          _ ≤ 1 + 3 := by
            rw [Complex.norm_real, Real.norm_eq_abs]; linarith [hb₁ (n + h₁)]
          _ = 4 := by norm_num
      calc _ ≤ 4 * 1 := mul_le_mul h1 (hb₂ _) (norm_nonneg _) (by norm_num)
        _ = 4 := by ring
    · simp
  have hbd := norm_sum_Ioc_sub_le hFb haN ha2N hNc
  have hsplit : ∑ n ∈ Finset.Ioc N (2 * N), F (δ N) n
      = ∑ n ∈ Finset.Ioc N (2 * N), F (δ N') n
        + ∑ n ∈ Finset.Ioc N (2 * N),
            (if n % W = b % W then ((δ N' - δ N : ℝ) : ℂ) * g₂ (n + h₂) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hF]; split_ifs
    · push_cast; ring
    · simp
  have hG : ‖∑ n ∈ Finset.Ioc N (2 * N),
      (if n % W = b % W then ((δ N' - δ N : ℝ) : ℂ) * g₂ (n + h₂) else 0)‖
        ≤ N * (3 / L + 6 * η) := by
    have hGb : ∀ n, ‖(if n % W = b % W then ((δ N' - δ N : ℝ) : ℂ) * g₂ (n + h₂) else 0)‖
        ≤ 3 / L + 6 * η := by
      intro n; split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        calc _ ≤ (3 / L + 6 * η) * 1 :=
              mul_le_mul hΔ (hb₂ _) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · simp; positivity
    have h := norm_sum_le_of_le (Finset.Ioc N (2 * N)) (fun n _ => hGb n)
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul] at h
    have : ((2 * N - N : ℕ) : ℝ) = N := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this] at h; exact h
  have hT : ‖∑ n ∈ Finset.Ioc N (2 * N), F (δ N) n‖
      ≤ ‖∑ n ∈ Finset.Ioc a c, F (δ N') n‖ + 12 * η * N + N * (3 / L + 6 * η) := by
    rw [hsplit]
    have h1 := norm_add_le (∑ n ∈ Finset.Ioc N (2 * N), F (δ N') n) (∑ n ∈ Finset.Ioc N (2 * N),
            (if n % W = b % W then ((δ N' - δ N : ℝ) : ℂ) * g₂ (n + h₂) else 0))
    have h2 : ‖∑ n ∈ Finset.Ioc N (2 * N), F (δ N') n‖
        ≤ ‖∑ n ∈ Finset.Ioc a c, F (δ N') n‖ + 12 * η * N := by
      have := norm_le_norm_add_norm_sub' (∑ n ∈ Finset.Ioc N (2 * N), F (δ N') n)
        (∑ n ∈ Finset.Ioc a c, F (δ N') n)
      have h4 : 4 * (((a : ℝ) - N) + ((c : ℝ) - ((2 * N : ℕ) : ℝ))) ≤ 12 * η * N := by linarith
      linarith
    linarith
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hTT ⊢
  have hK : (W / N : ℝ) * ‖∑ n ∈ Finset.Ioc a c, F (δ N') n‖ ≤ 2 * K := by
    have hratio : (W / N : ℝ) = (N' / N) * (W / N') := by field_simp
    rw [hratio, mul_assoc]
    have hK0 : 0 ≤ K := le_trans (by positivity) hTT
    have hr : N' / N ≤ 2 := by rw [div_le_iff₀ hNpos]; nlinarith
    calc _ ≤ 2 * ((W / N') * ‖∑ n ∈ Finset.Ioc a c, F (δ N') n‖) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ ≤ 2 * K := by linarith
  calc (W / N : ℝ) * ‖∑ n ∈ Finset.Ioc N (2 * N), F (δ N) n‖
      ≤ (W / N : ℝ) * (‖∑ n ∈ Finset.Ioc a c, F (δ N') n‖ + 12 * η * N + N * (3 / L + 6 * η)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (W / N : ℝ) * ‖∑ n ∈ Finset.Ioc a c, F (δ N') n‖ + W * (18 * η + 3 / L) := by
        field_simp; ring
    _ ≤ _ := by linarith

/-- **Counting.**  Disjoint-by-parity log-intervals `[N_j, N_j(1+η)] ⊆ E ∩ [2^j, 2^{j+2})`, one
per bad scale, force `#bad · η/2 ≤ 2 ∫_E dt/t`. -/
theorem card_mul_le_integral {E : Set ℝ} (hEm : MeasurableSet E) {s X : ℝ} (hs : 0 < s)
    (hE : E ⊆ Set.Icc s X) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (Bad : Finset ℕ) (Nf : ℕ → ℝ)
    (h1 : ∀ j ∈ Bad, (2 : ℝ) ^ j ≤ Nf j) (h2 : ∀ j ∈ Bad, Nf j * (1 + η) < 2 ^ (j + 2))
    (h3 : ∀ j ∈ Bad, Set.Icc (Nf j) (Nf j * (1 + η)) ⊆ E) :
    (Bad.card : ℝ) * (η / 2) ≤ 2 * ∫ t in E, t⁻¹ := by
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) E := by
    refine IntegrableOn.mono_set ?_ hE
    exact (continuousOn_inv₀.mono fun t ht => (by
      have := ht.1; exact ne_of_gt (by linarith))).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict E] (fun t : ℝ => t⁻¹) := by
    refine ae_restrict_of_forall_mem hEm fun t ht => ?_
    have := (hE ht).1; exact inv_nonneg.mpr (by linarith)
  have key : ∀ r : ℕ, ((Bad.filter (fun j => j % 2 = r)).card : ℝ) * (η / 2)
      ≤ ∫ t in E, t⁻¹ := by
    intro r
    set B := Bad.filter (fun j => j % 2 = r)
    have hsub : ∀ j ∈ B, j ∈ Bad := fun j hj => (Finset.mem_filter.mp hj).1
    have hpos : ∀ j ∈ B, 0 < Nf j := fun j hj =>
      lt_of_lt_of_le (by positivity) (h1 j (hsub j hj))
    calc ((B.card : ℝ) * (η / 2)) = ∑ j ∈ B, η / 2 := by simp
      _ ≤ ∑ j ∈ B, ∫ t in Set.Icc (Nf j) (Nf j * (1 + η)), t⁻¹ :=
          Finset.sum_le_sum fun j hj => half_le_integral_inv (hpos j hj) hη hη1
      _ = ∫ t in ⋃ j ∈ B, Set.Icc (Nf j) (Nf j * (1 + η)), t⁻¹ := by
          rw [integral_biUnion_finset]
          · exact fun j _ => measurableSet_Icc
          · intro j hj k hk hjk
            simp only [Function.onFun]
            rw [Set.disjoint_left]
            intro t htj htk
            have hjr := (Finset.mem_filter.mp hj).2
            have hkr := (Finset.mem_filter.mp hk).2
            have a1 := h1 j (hsub j hj); have a2 := h2 j (hsub j hj)
            have b1 := h1 k (hsub k hk); have b2 := h2 k (hsub k hk)
            have hj2 : (2 : ℝ) ^ j ≤ t := le_trans a1 htj.1
            have hj3 : t < 2 ^ (j + 2) := lt_of_le_of_lt htj.2 a2
            have hk2 : (2 : ℝ) ^ k ≤ t := le_trans b1 htk.1
            have hk3 : t < 2 ^ (k + 2) := lt_of_le_of_lt htk.2 b2
            rcases lt_or_gt_of_ne hjk with h | h
            · have : j + 2 ≤ k := by omega
              have : (2 : ℝ) ^ (j + 2) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) this
              linarith
            · have : k + 2 ≤ j := by omega
              have : (2 : ℝ) ^ (k + 2) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) this
              linarith
          · exact fun j hj => hint.mono_set (h3 j (hsub j hj))
      _ ≤ ∫ t in E, t⁻¹ := by
          refine setIntegral_mono_set hint hnn (Filter.Eventually.of_forall ?_)
          intro t ht
          have ht' : t ∈ ⋃ j ∈ B, Set.Icc (Nf j) (Nf j * (1 + η)) := ht
          simp only [Set.mem_iUnion] at ht'
          obtain ⟨j, hj, ht'⟩ := ht'
          exact h3 j (hsub j hj) ht'
  have hsplit : (Bad.card : ℝ) = (Bad.filter (fun j => j % 2 = 0)).card
      + (Bad.filter (fun j => j % 2 = 1)).card := by
    have h := Finset.card_filter_add_card_filter_not (s := Bad) (fun j => j % 2 = 0)
    have e : Bad.filter (fun j => ¬ j % 2 = 0) = Bad.filter (fun j => j % 2 = 1) :=
      Finset.filter_congr fun j _ => by omega
    rw [e] at h; exact_mod_cast h.symm
  rw [hsplit, add_mul]
  linarith [key 0, key 1]

/-- If there is a dyadic scale, `log X ≤ 6 · #scales`. -/
theorem log_le_card_dyadicScales {X : ℝ} (hX : 2 ≤ X) (hne : (dyadicScales X).Nonempty) :
    Real.log X ≤ 6 * ((dyadicScales X).card : ℝ) := by
  set ℓ := Real.logb 2 X with hℓ
  have hX0 : 0 < X := by linarith
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) hX0]; simpa using hX
  set A := ⌈ℓ / 2⌉₊
  set B := ⌊ℓ⌋₊ - 1
  have hfl1 : 1 ≤ ⌊ℓ⌋₊ := Nat.le_floor (by simpa using hℓ1)
  have hsub : Finset.Icc A B ⊆ dyadicScales X := by
    intro j hj
    obtain ⟨hAj, hjB⟩ := Finset.mem_Icc.mp hj
    unfold dyadicScales
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have : ⌊ℓ⌋₊ ≤ ⌈Real.logb 2 X⌉₊ := Nat.floor_le_ceil _
      omega
    · rw [Real.sqrt_le_left (by positivity)]
      have h1 : ℓ / 2 ≤ j := le_trans (Nat.le_ceil _) (by exact_mod_cast hAj)
      have h2 : X = (2 : ℝ) ^ ℓ := (Real.rpow_logb (by norm_num) (by norm_num) hX0).symm
      rw [h2, ← pow_mul, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    · have h1 : ((j + 1 : ℕ) : ℝ) ≤ ℓ := by
        have : j + 1 ≤ ⌊ℓ⌋₊ := by omega
        exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
      have h2 : X = (2 : ℝ) ^ ℓ := (Real.rpow_logb (by norm_num) (by norm_num) hX0).symm
      conv_rhs => rw [h2]
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast h1)
  have hcard : ((B : ℝ) + 1 - A) ≤ ((dyadicScales X).card : ℝ) := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    have : B + 1 ≤ (B + 1 - A) + A := by omega
    have : (B : ℝ) + 1 ≤ ((B + 1 - A : ℕ) : ℝ) + A := by exact_mod_cast this
    have : ((B + 1 - A : ℕ) : ℝ) ≤ ((dyadicScales X).card : ℝ) := by exact_mod_cast h
    linarith
  have hA : (A : ℝ) ≤ ℓ / 2 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hB : ℓ - 2 ≤ (B : ℝ) := by
    have : (B : ℝ) = (⌊ℓ⌋₊ : ℝ) - 1 := by rw [Nat.cast_sub hfl1]; simp
    rw [this]; linarith [Nat.lt_floor_add_one ℓ]
  have h1 : (1 : ℝ) ≤ ((dyadicScales X).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hlog : Real.log X = ℓ * Real.log 2 := by
    rw [hℓ, Real.logb, div_mul_cancel₀]; exact (Real.log_pos (by norm_num)).ne'
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlog]
  nlinarith

theorem filter_mod_one (A B : ℕ) (a : ℕ) :
    (Finset.Ioc A B).filter (fun n => n % 1 = a % 1) = Finset.Ioc A B :=
  Finset.filter_true_of_mem fun n _ => by simp [Nat.mod_one]

/-- **The bridge**, with an explicit real-form hypothesis: `(c, C)` of the literal Theorem 3.1(i)
give the counted dyadic form with `c' = min c 1 / 4` and `Cst' = 6(1 + 4C) + 2C + 21`. -/
theorem dyadic_of_real_core {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hreal : ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → ∀ δ : ℝ → ℝ,
        (∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖(∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), g₁ n)
              - (((N / q) * δ N : ℝ) : ℂ)‖ ≤ N / L) →
        (∀ p : ℕ, p.Prime → Real.exp (Real.log X ^ ((1 : ℝ) / 11)) ≤ p →
          (p : ℝ) ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 10)) → g₁ p = 1) →
        ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Icc (Real.sqrt X) X ∧
          (∫ t in E, t⁻¹) ≤ C * L ^ (-c) * Real.log X ∧
          ∀ N : ℝ, Real.sqrt X ≤ N → N ≤ X → N ∉ E →
            ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
              (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
              ‖((W : ℝ) / N : ℝ) •
                  ∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % W = b % W),
                    (g₁ (n + h₁) - ((δ N : ℝ) : ℂ)) * g₂ (n + h₂)‖
                ≤ C * L ^ (-c)) :
    TTEquidistributedDyadic := by
  classical
  set c' := min c 1 / 4 with hc'
  have hc'0 : 0 < c' := by positivity
  have hc'c : 4 * c' ≤ c := by rw [hc']; linarith [min_le_left c 1]
  have hc'1 : 4 * c' ≤ 1 := by rw [hc']; linarith [min_le_right c 1]
  refine ⟨c', 6 * (1 + 4 * C) + 2 * C + 21, hc'0, by positivity,
    fun g₁ g₂ hg₁ hg₂ hb₁ hb₂ him X L hX hL1 hLX δ h31 h32 => ?_⟩
  obtain ⟨E, hEm, hEsub, hEint, hgood⟩ := hreal g₁ g₂ hg₁ hg₂ hb₁ hb₂ him X L hX hL1 hLX δ h31 h32
  have hL0 : 0 < L := by linarith
  have hX0 : 0 < X := by linarith
  set η := L ^ (-(2 * c')) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have h04 : X ^ (0.4 : ℝ) ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  set S := dyadicScales X
  set Edy := S.filter (fun j => X < 2 ^ (j + 2) ∨ ∃ N : ℕ, (2 : ℝ) ^ j ≤ N ∧
    (N : ℝ) < 2 ^ (j + 1) ∧ Set.Icc (N : ℝ) (N * (1 + η)) ⊆ E)
  have hmemS : ∀ j ∈ S, Real.sqrt X ≤ 2 ^ j ∧ (2 : ℝ) ^ (j + 1) ≤ X := fun j hj => by
    have := hj; unfold S dyadicScales at this
    exact (Finset.mem_filter.mp this).2
  refine ⟨Edy, Finset.filter_subset _ _, ?_, ?_⟩
  · -- counting
    rcases S.eq_empty_or_nonempty with hS | hS
    · have : Edy = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj; have := (Finset.mem_filter.mp hj).1; rw [hS] at this; simp at this
      rw [this, hS]; simp
    set Top := S.filter (fun j => X < 2 ^ (j + 2))
    set Bad := S.filter (fun j => ∃ N : ℕ, (2 : ℝ) ^ j ≤ N ∧
      (N : ℝ) < 2 ^ (j + 1) ∧ Set.Icc (N : ℝ) (N * (1 + η)) ⊆ E)
    have hEdy : Edy ⊆ Top ∪ Bad := by
      intro j hj
      obtain ⟨hjS, hj'⟩ := Finset.mem_filter.mp hj
      rcases hj' with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjS, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjS, h⟩)
    have hTop : Top.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro j hj k hk
      obtain ⟨hjS, hjX⟩ := Finset.mem_filter.mp hj
      obtain ⟨hkS, hkX⟩ := Finset.mem_filter.mp hk
      have hj1 := (hmemS j hjS).2; have hk1 := (hmemS k hkS).2
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have : (2 : ℝ) ^ (j + 2) ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      · have : (2 : ℝ) ^ (k + 2) ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
    have hBadex : ∀ j ∈ Bad, ∃ N : ℕ, (2 : ℝ) ^ j ≤ N ∧
        (N : ℝ) < 2 ^ (j + 1) ∧ Set.Icc (N : ℝ) (N * (1 + η)) ⊆ E :=
      fun j hj => (Finset.mem_filter.mp hj).2
    choose! Nf hNf1 hNf2 hNf3 using hBadex
    have hBad := card_mul_le_integral hEm hsqrt hEsub hη0 hη1 Bad (fun j => (Nf j : ℝ))
      hNf1 (fun j hj => by
        have h2 := hNf2 j hj
        have h0 : (0 : ℝ) ≤ Nf j := Nat.cast_nonneg _
        calc (Nf j : ℝ) * (1 + η) ≤ Nf j * 2 := by nlinarith
          _ < 2 ^ (j + 1) * 2 := by nlinarith
          _ = 2 ^ (j + 2) := by ring) hNf3
    have hlog := log_le_card_dyadicScales hX hS
    have hlogpos : 0 < Real.log X := lt_of_lt_of_le hL0 hLX
    -- `#Bad ≤ 4 C L^{-c'} log X`
    have hBad2 : (Bad.card : ℝ) ≤ 4 * C * L ^ (-c') * Real.log X := by
      have h1 : (Bad.card : ℝ) * η ≤ 4 * (C * L ^ (-c) * Real.log X) := by linarith
      have h2 : L ^ (-c) ≤ L ^ (-c') * η := by
        rw [hη, ← Real.rpow_add hL0]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have h3 : (Bad.card : ℝ) * η ≤ (4 * C * L ^ (-c') * Real.log X) * η := by
        have : C * L ^ (-c) * Real.log X ≤ C * (L ^ (-c') * η) * Real.log X := by gcongr
        nlinarith
      exact le_of_mul_le_mul_right h3 hη0
    have h1L : (1 : ℝ) ≤ L ^ (-c') * Real.log X := by
      have : L ^ c' ≤ Real.log X := le_trans
        (Real.rpow_le_self_of_one_le hL1 (by linarith)) hLX
      rw [Real.rpow_neg hL0.le]
      rw [le_inv_mul_iff₀ (by positivity)]; linarith
    have hcardE : (Edy.card : ℝ) ≤ 1 + Bad.card := by
      have h := (Finset.card_le_card hEdy).trans (Finset.card_union_le _ _)
      have : (Edy.card : ℝ) ≤ Top.card + Bad.card := by exact_mod_cast h
      have : (Top.card : ℝ) ≤ 1 := by exact_mod_cast hTop
      linarith
    have hLc : 0 < L ^ (-c') := by positivity
    calc (Edy.card : ℝ) ≤ (1 + 4 * C) * (L ^ (-c') * Real.log X) := by nlinarith
      _ ≤ (1 + 4 * C) * (L ^ (-c') * (6 * (S.card : ℝ))) := by gcongr
      _ ≤ _ := by
        have : (0 : ℝ) ≤ L ^ (-c') * S.card := by positivity
        nlinarith
  · -- the bound at good scales
    intro j hjS hjE N hN1 hN2 W b h₁ h₂ hW hWL hh₁ hh₂ hne
    have hnot : ¬ (X < 2 ^ (j + 2) ∨ ∃ N : ℕ, (2 : ℝ) ^ j ≤ N ∧
        (N : ℝ) < 2 ^ (j + 1) ∧ Set.Icc (N : ℝ) (N * (1 + η)) ⊆ E) :=
      fun h => hjE (Finset.mem_filter.mpr ⟨hjS, h⟩)
    push Not at hnot
    obtain ⟨hXj, hnE⟩ := hnot
    obtain ⟨N', hN'I, hN'E⟩ := Set.not_subset.mp (hnE N hN1 hN2)
    have hpj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hNge1 : 1 ≤ N := by exact_mod_cast hpj.trans hN1
    have hNX : (N : ℝ) ≤ X := by
      have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hN'X : N' ≤ X := by
      have h1 := hN'I.2
      have : (N : ℝ) * (1 + η) ≤ N * 2 := by nlinarith
      have : (2 : ℝ) ^ (j + 1) * 2 = 2 ^ (j + 2) := by ring
      linarith
    have hsqN : Real.sqrt X ≤ N := (hmemS j hjS).1.trans hN1
    have hsqN' : Real.sqrt X ≤ N' := hsqN.trans hN'I.1
    have hLcc : L ^ c' ≤ L ^ c := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hTT := hgood N' hsqN' hN'X hN'E W b h₁ h₂ hW (hWL.trans hLcc) (hh₁.trans hLcc)
      (hh₂.trans hLcc) hne
    have h31N := h31 (N : ℝ) (h04.trans hsqN) hNX 0 1 le_rfl
    have h31N' := h31 N' (h04.trans hsqN') hN'X 0 1 le_rfl
    rw [filter_mod_one] at h31N h31N'
    have e2 : (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
    rw [Nat.floor_natCast, e2, Nat.floor_natCast, Nat.cast_one, div_one] at h31N
    rw [Nat.cast_one, div_one] at h31N'
    have hmain := perturb_bound hb₁ hb₂ hL1 hη0 hη1 hNge1 hN'I.1 hN'I.2 h31N h31N' hW hTT
    refine hmain.trans ?_
    have hWpos : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have hA : (W : ℝ) * η ≤ L ^ (-c') := by
      calc (W : ℝ) * η ≤ L ^ c' * η := mul_le_mul_of_nonneg_right hWL hη0.le
        _ = L ^ (-c') := by rw [hη, ← Real.rpow_add hL0]; ring_nf
    have hB : (W : ℝ) / L ≤ L ^ (-c') := by
      calc (W : ℝ) / L ≤ L ^ c' / L := div_le_div_of_nonneg_right hWL hL0.le
        _ = L ^ (c' - 1) := by rw [Real.rpow_sub hL0, Real.rpow_one]
        _ ≤ L ^ (-c') := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hC2 : L ^ (-c) ≤ L ^ (-c') := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hLc : 0 < L ^ (-c') := by positivity
    have e3 : (W : ℝ) * (18 * η + 3 / L) = 18 * (W * η) + 3 * (W / L) := by ring
    rw [e3]
    nlinarith

end NormalNumbers.CastingOut.TTBridge
