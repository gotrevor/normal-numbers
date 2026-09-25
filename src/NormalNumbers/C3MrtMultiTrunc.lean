/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultiMass

/-!
# The `K`-fold truncation telescope

`two_shift_truncation_bound` (`C3MrtTwoShift`) cuts BOTH moduli of the two-shift bridge
expansion at `Y`, at a cost `(1+log N)·bridgeTail z₀ Y + (2·sqfWPartial z₀ Y +
(1+log N)·sqfWMass z₀)·bridgeTail z₁ Y`.  This file is its `K`-fold analogue: it truncates all
`K` moduli of `sum_pow_omega_multi_eq` at `Y`, by induction on `K` peeling the **last** shift.

**The invariant that makes the induction go through.**  A naive iteration would, at each peel,
bound the remaining mass by ONE congruence and so accumulate `∏_{j>m} sqfWPartial z_j Y ≍
Y^{(K-m-1)/2}` against a `bridgeTail ≍ Y^{-1/2}` — divergent for `K - m ≥ 3`.  The fix is to
carry, as an inductive hypothesis on the weight `F` and the index set `S`, the *two-term* mass
bound that `joint_multi_harmonic_mass` supplies for a consecutive block of congruences:

    ∑_{n ∈ S, ∀ s<r, g_s ∣ n + (J-r) + s + 1} ‖F n‖  ≤  α / g_0  +  β / ∏_{s<r} g_s .

The head term `α/g_0` is what pairs with `sqfWPartial` (an `N`-independent constant, harmless);
the `β`-term carries the full product weight and therefore pairs with the CONVERGENT
`sqfWMass`.  Peeling one shift with modulus `e` sends `(α, β) ↦ (α, β/e)`, which is exactly the
transformation that keeps the second factor convergent.

Consequently the accumulated error is `α·truncA + β·truncB`, with the two constants defined by
the transparent recursions

    truncA (J+1) = bridgeTail z_J Y + sqfWPartial z_J Y · truncA J ,
    truncB (J+1) = bridgeTail z_J Y + sqfWMass z_J · truncB J .

`truncB` is the term of the right order: every factor is `N`-independent and `sqfWMass` is
finite, so the whole `β`-part is `(1 + log N)·K^{K²}·(a constant that tends to `0` with `Y`).
`truncA` grows with `Y`, but `α` is `N`-independent, so the `α`-part is an `N`-independent
constant, killed by the `1/log N` normalisation — exactly as at `K = 2`.

The top-level instantiation (`multi_truncation_bound`) takes `α = K`, `β = (1+log N)·K^{K²}`
from `joint_multi_harmonic_mass`.
-/

open Finset

namespace NormalNumbers

namespace CastingOut

/-- The accumulated `sqfWPartial`-weighted tail constant: the coefficient of the head mass `α`.
`N`-independent; it grows with `Y`. -/
noncomputable def truncA (z : ℕ → ℂ) (Y : ℕ) : ℕ → ℝ
  | 0 => 0
  | J + 1 => bridgeTail (z J) Y + sqfWPartial (z J) Y * truncA z Y J

/-- The accumulated `sqfWMass`-weighted tail constant: the coefficient of the `log`-carrying
mass `β`.  Every factor is `N`-independent and `sqfWMass` is finite, so this tends to `0` as
`Y → ∞` for each fixed depth. -/
noncomputable def truncB (z : ℕ → ℂ) (Y : ℕ) : ℕ → ℝ
  | 0 => 0
  | J + 1 => bridgeTail (z J) Y + sqfWMass (z J) * truncB z Y J

lemma truncA_nonneg (z : ℕ → ℂ) (Y : ℕ) : ∀ J, 0 ≤ truncA z Y J
  | 0 => le_refl 0
  | J + 1 => by
      have := truncA_nonneg z Y J
      have h1 := bridgeTail_nonneg (z J) Y
      have h2 := sqfWPartial_nonneg (z J) Y
      rw [truncA]
      positivity

lemma truncB_nonneg (z : ℕ → ℂ) (Y : ℕ) : ∀ J, 0 ≤ truncB z Y J
  | 0 => le_refl 0
  | J + 1 => by
      have := truncB_nonneg z Y J
      have h1 := bridgeTail_nonneg (z J) Y
      have h2 := sqfWMass_nonneg (z J)
      rw [truncB]
      positivity

/-- **The `β`-side constant vanishes as `Y → ∞`, at every fixed depth.**  Each `bridgeTail`
tends to `0` (`bridgeTail_tendsto`) and each `sqfWMass` is a finite `Y`-independent constant, so
the whole `truncB` recursion does — uniformly in `N`, since no factor sees `N`.  This is what
makes the ε-chase of step 4 possible: choose `Y` from `ε` first, then let `N → ∞`. -/
theorem truncB_tendsto (z : ℕ → ℂ) : ∀ J,
    Filter.Tendsto (fun Y => truncB z Y J) Filter.atTop (nhds 0)
  | 0 => by simpa [truncB] using tendsto_const_nhds (α := ℝ) (x := (0 : ℝ))
  | J + 1 => by
      have ih := truncB_tendsto z J
      have hfun : (fun Y => truncB z Y (J + 1))
          = fun Y => bridgeTail (z J) Y + sqfWMass (z J) * truncB z Y J := rfl
      rw [hfun]
      simpa using (bridgeTail_tendsto (z J)).add (ih.const_mul (sqfWMass (z J)))

open scoped Classical in
/-- **The `K`-fold truncation telescope.**  All `J` moduli of the bridge expansion cut at `Y`,
the error controlled by the two-term block-mass invariant described in the module docstring.
`F`, `S`, `α`, `β` are quantified INSIDE the induction: each peel changes all four. -/
theorem multi_truncation_telescope (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (N Y : ℕ) :
    ∀ (J : ℕ) (F : ℕ → ℂ) (S : Finset ℕ) (α β : ℝ), 0 ≤ α → 0 ≤ β →
      (∀ n ∈ S, n < N) →
      (∀ r : ℕ, 1 ≤ r → r ≤ J → ∀ g : ℕ → ℕ, (∀ s, s < r → 0 < g s) →
        ∑ n ∈ S.filter (fun n => ∀ s, s < r → g s ∣ n + (J - r) + s + 1), ‖F n‖
          ≤ α / (g 0 : ℝ) + β / ∏ s ∈ range r, (g s : ℝ)) →
      ‖(∑ n ∈ S, F n * ∏ i : Fin J, (z i) ^ omegaNat (n + i + 1))
          - ∑ d ∈ Fintype.piFinset (fun _ : Fin J => range (Y + 1)),
              (∏ i : Fin J, sqfW (z i) (d i)) *
                ∑ n ∈ S.filter (fun n => ∀ i : Fin J, d i ∣ n + i + 1),
                  F n * ∏ i : Fin J,
                    (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d i)‖
        ≤ α * truncA z Y J + β * truncB z Y J := by
  classical
  intro J
  induction J with
  | zero =>
      intro F S α β hα hβ _ _
      simp [truncA, truncB]
  | succ K ih =>
      intro F S α β hα hβ hS hmass
      set F₁ : ℕ → ℂ := fun n => F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1) with hF₁
      have hF₁norm : ∀ n, ‖F₁ n‖ = ‖F n‖ := by
        intro n
        rw [hF₁, norm_mul, norm_prod]
        simp [hz]
      -- Step 1: peel the last shift, truncating its modulus at `Y`.
      set Mid := ∑ dK ∈ range (Y + 1), sqfW (z K) dK *
        ∑ n ∈ S.filter (fun n => dK ∣ n + (K + 1)),
          F₁ n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK) with hMid
      have hstep1 : ‖(∑ n ∈ S, F n * ∏ i : Fin (K + 1), (z i) ^ omegaNat (n + i + 1)) - Mid‖
          ≤ (α + β) * bridgeTail (z K) Y := by
        have hrw : (∑ n ∈ S, F n * ∏ i : Fin (K + 1), (z i) ^ omegaNat (n + i + 1))
            = ∑ n ∈ S, F₁ n * (z K) ^ omegaNat (n + (K + 1)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hF₁, Fin.prod_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          ring_nf
        rw [hrw, hMid]
        refine offset_truncation_bound_of_mass (z K) (hz K) F₁ S (K + 1) (by omega) (N + K + 1)
          (fun n hn => by have := hS n hn; omega) Y (α + β) (by linarith) ?_
        intro d hd
        have h := hmass 1 le_rfl (by omega) (fun _ => d) (fun s _ => hd)
        have hlast : α / (d : ℝ) + β / ∏ s ∈ range 1, ((d : ℕ) : ℝ) = (α + β) / (d : ℝ) := by
          simp only [Finset.prod_range_one]
          ring
        refine le_trans (le_of_eq ?_) (h.trans (le_of_eq hlast))
        refine Finset.sum_congr ?_ (fun n _ => hF₁norm n)
        ext n
        simp only [Finset.mem_filter]
        refine and_congr_right fun _ => ?_
        constructor
        · intro hh s hs
          obtain rfl : s = 0 := by omega
          have he : n + (K + 1 - 1) + 0 + 1 = n + (K + 1) := by omega
          rw [he]; exact hh
        · intro hh
          have h0 := hh 0 (by omega)
          have he : n + (K + 1 - 1) + 0 + 1 = n + (K + 1) := by omega
          rwa [he] at h0
      -- Step 2: for each `dK ≤ Y`, the remaining `K` shifts, by the induction hypothesis.
      set Full := ∑ d ∈ Fintype.piFinset (fun _ : Fin (K + 1) => range (Y + 1)),
        (∏ i : Fin (K + 1), sqfW (z i) (d i)) *
          ∑ n ∈ S.filter (fun n => ∀ i : Fin (K + 1), d i ∣ n + i + 1),
            F n * ∏ i : Fin (K + 1),
              (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d i) with hFull
      set Δ : ℕ → ℂ := fun dK => (∑ n ∈ S.filter (fun n => dK ∣ n + (K + 1)),
              F₁ n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
            - ∑ d' ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
                (∏ i : Fin K, sqfW (z i) (d' i)) *
                  ∑ n ∈ (S.filter (fun n => dK ∣ n + (K + 1))).filter
                      (fun n => ∀ i : Fin K, d' i ∣ n + i + 1),
                    (F n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK)) *
                      ∏ i : Fin K,
                        (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d' i) with hΔ
      have hstep2 : ∀ dK ∈ range (Y + 1),
          ‖Δ dK‖ ≤ α * truncA z Y K + (β / (dK : ℝ)) * truncB z Y K := by
        intro dK _
        simp only [hΔ]
        set S' := S.filter (fun n => dK ∣ n + (K + 1)) with hS'
        set G : ℕ → ℂ := fun n => F n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK)
          with hG
        have hGnorm : ∀ n, ‖G n‖ = ‖F n‖ := by
          intro n; rw [hG, norm_mul, norm_pow, hz K, one_pow, mul_one]
        have hrw : (∑ n ∈ S', F₁ n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK))
            = ∑ n ∈ S', G n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1) :=
          Finset.sum_congr rfl fun n _ => by rw [hF₁, hG]; ring
        rw [hrw]
        have hβ' : 0 ≤ β / (dK : ℝ) := by positivity
        refine ih G S' α (β / (dK : ℝ)) hα hβ' (fun n hn => hS n (Finset.mem_filter.1 hn).1) ?_
        intro r hr1 hrK g hg
        rcases Nat.eq_zero_or_pos dK with rfl | hdK
        · -- the progression is empty
          have hempty : S'.filter (fun n => ∀ s, s < r → g s ∣ n + (K - r) + s + 1) = ∅ := by
            refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
            have := (Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).2
            simp only [Nat.zero_dvd] at this
            omega
          rw [hempty, Finset.sum_empty]
          have h1 : (0 : ℝ) ≤ α / (g 0 : ℝ) := by positivity
          have h2 : (0 : ℝ) ≤ β / (0 : ℕ) / ∏ s ∈ range r, (g s : ℝ) := by
            simp
          linarith
        · set g' : ℕ → ℕ := fun s => if s < r then g s else dK with hg'
          have hg'pos : ∀ s, s < r + 1 → 0 < g' s := by
            intro s hs
            rw [hg']
            by_cases h : s < r
            · simp only [h, if_true]; exact hg s h
            · simp only [h, if_false]; exact hdK
          have h := hmass (r + 1) (by omega) (by omega) g' hg'pos
          have hbase : K + 1 - (r + 1) = K - r := by omega
          have hg0 : g' 0 = g 0 := by
            rw [hg']; simp only [if_pos (show 0 < r by omega)]
          have hprod : ∏ s ∈ range (r + 1), ((g' s : ℕ) : ℝ)
              = (∏ s ∈ range r, ((g s : ℕ) : ℝ)) * (dK : ℝ) := by
            rw [Finset.prod_range_succ]
            congr 1
            · refine Finset.prod_congr rfl fun s hs => ?_
              rw [hg']
              simp [Finset.mem_range.1 hs]
            · rw [hg']; simp
          have hdKR : (0 : ℝ) < (dK : ℝ) := by exact_mod_cast hdK
          have hprodpos : (0 : ℝ) < ∏ s ∈ range r, ((g s : ℕ) : ℝ) :=
            Finset.prod_pos fun s hs => by
              have := hg s (Finset.mem_range.1 hs); exact_mod_cast this
          have hlast : α / ((g' 0 : ℕ) : ℝ) + β / ∏ s ∈ range (r + 1), ((g' s : ℕ) : ℝ)
              = α / ((g 0 : ℕ) : ℝ) + (β / (dK : ℝ)) / ∏ s ∈ range r, ((g s : ℕ) : ℝ) := by
            rw [hg0, hprod]
            field_simp
          refine le_trans (le_of_eq ?_) (h.trans (le_of_eq hlast))
          refine Finset.sum_congr ?_ (fun n _ => hGnorm n)
          rw [hS', Finset.filter_filter]
          ext n
          simp only [Finset.mem_filter, hbase]
          refine and_congr_right fun _ => ?_
          constructor
          · rintro ⟨hdvd, hh⟩ s hs
            rw [hg']
            by_cases hlt : s < r
            · simp only [hlt, if_true]; exact hh s hlt
            · simp only [hlt, if_false]
              have hsr : s = r := by omega
              have harith : n + (K - r) + s + 1 = n + (K + 1) := by omega
              rw [harith]; exact hdvd
          · intro hh
            refine ⟨?_, fun s hs => ?_⟩
            · have hr := hh r (by omega)
              rw [hg'] at hr
              simp only [lt_irrefl, if_false] at hr
              have harith : n + (K - r) + r + 1 = n + (K + 1) := by omega
              rwa [harith] at hr
            · have hs' := hh s (by omega)
              rw [hg'] at hs'
              simpa [hs] using hs'
      -- assemble
      have hdiff : Mid - Full = ∑ dK ∈ range (Y + 1), sqfW (z K) dK * Δ dK := by
        simp only [hΔ]
        rw [hMid, hFull, sum_piFinset_snoc, Finset.sum_product, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun dK _ => ?_
        rw [mul_sub]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d' _ => ?_
        have hprod : (∏ i : Fin (K + 1), sqfW (z i) ((Fin.snoc d' dK : Fin (K + 1) → ℕ) i))
            = (∏ i : Fin K, sqfW (z i) (d' i)) * sqfW (z K) dK := by
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last]
        have hfilter : (S.filter (fun n => dK ∣ n + (K + 1))).filter
              (fun n => ∀ i : Fin K, d' i ∣ n + i + 1)
            = S.filter (fun n => ∀ i : Fin (K + 1),
                (Fin.snoc d' dK : Fin (K + 1) → ℕ) i ∣ n + i + 1) := by
          rw [Finset.filter_filter]
          refine Finset.filter_congr fun n _ => ?_
          constructor
          · intro hh i
            rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
            · rw [Fin.snoc_castSucc, Fin.val_castSucc]
              exact hh.2 i'
            · rw [Fin.snoc_last, Fin.val_last]
              have := hh.1
              simpa [Nat.add_assoc] using this
          · intro hh
            refine ⟨?_, fun i => ?_⟩
            · have h := hh (Fin.last K)
              rw [Fin.snoc_last, Fin.val_last] at h
              simpa [Nat.add_assoc] using h
            · have h := hh i.castSucc
              rw [Fin.snoc_castSucc, Fin.val_castSucc] at h
              exact h
        have hsum : ∑ n ∈ S.filter (fun n => ∀ i : Fin (K + 1),
              (Fin.snoc d' dK : Fin (K + 1) → ℕ) i ∣ n + i + 1),
            F n * ∏ i : Fin (K + 1), (z i) ^ ArithmeticFunction.cardFactors
              ((n + i + 1) / (Fin.snoc d' dK : Fin (K + 1) → ℕ) i)
            = ∑ n ∈ S.filter (fun n => ∀ i : Fin (K + 1),
                (Fin.snoc d' dK : Fin (K + 1) → ℕ) i ∣ n + i + 1),
              (F n * (z K) ^ ArithmeticFunction.cardFactors ((n + (K + 1)) / dK)) *
                ∏ i : Fin K, (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d' i) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last]
          ring_nf
        rw [hprod, hfilter, hsum]
        ring
      have hAnn : 0 ≤ α * truncA z Y K := mul_nonneg hα (truncA_nonneg z Y K)
      have hBnn : 0 ≤ β * truncB z Y K := mul_nonneg hβ (truncB_nonneg z Y K)
      have hMidFull : ‖Mid - Full‖
          ≤ sqfWPartial (z K) Y * (α * truncA z Y K)
            + sqfWMass (z K) * (β * truncB z Y K) := by
        rw [hdiff]
        have hterm : ∀ dK ∈ range (Y + 1), ‖sqfW (z K) dK * Δ dK‖
            ≤ ‖sqfW (z K) dK‖ * (α * truncA z Y K)
              + ‖sqfW (z K) dK‖ / (dK : ℝ) * (β * truncB z Y K) := by
          intro dK hdK
          rw [norm_mul]
          refine le_trans (mul_le_mul_of_nonneg_left (hstep2 dK hdK) (norm_nonneg _))
            (le_of_eq ?_)
          ring
        refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
        · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          have h1 : (∑ dK ∈ range (Y + 1), ‖sqfW (z K) dK‖) = sqfWPartial (z K) Y := rfl
          have h2 := sum_norm_sqfW_div_le_mass (hz K) (z := z K) Y
          rw [h1]
          have := mul_le_mul_of_nonneg_right h2 hBnn
          linarith
      have hfinal : ‖(∑ n ∈ S, F n * ∏ i : Fin (K + 1), (z i) ^ omegaNat (n + i + 1)) - Full‖
          ≤ (α + β) * bridgeTail (z K) Y
            + (sqfWPartial (z K) Y * (α * truncA z Y K)
              + sqfWMass (z K) * (β * truncB z Y K)) := by
        calc ‖(∑ n ∈ S, F n * ∏ i : Fin (K + 1), (z i) ^ omegaNat (n + i + 1)) - Full‖
            = ‖((∑ n ∈ S, F n * ∏ i : Fin (K + 1), (z i) ^ omegaNat (n + i + 1)) - Mid)
                + (Mid - Full)‖ := by congr 1; ring
          _ ≤ _ := le_trans (norm_add_le _ _) (add_le_add hstep1 hMidFull)
      refine hfinal.trans (le_of_eq ?_)
      rw [truncA, truncB]
      ring

#print axioms multi_truncation_telescope


open scoped Classical in
/-- **The `K`-fold truncation bound.**  All `K` moduli of `sum_pow_omega_multi_eq` cut at `Y`,
for the harmonic weight the rung supplies.  This is the `K`-point `two_shift_truncation_bound`:
the `α`-part `K·truncA` is `N`-independent (killed by the `1/log N` normalisation), and the
`β`-part carries the single factor `1 + log N` against `truncB`, every factor of which is
`N`-independent and tends to `0` with `Y`.  The constant `K^{K²}` is lap 37's
`prod_le_lcm_mul_pow`; `C3MrtBudget.kfold_budget_le_exp_cube` is what pays for it. -/
theorem multi_truncation_bound (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) {F : ℕ → ℂ}
    (hF : ∀ n : ℕ, ‖F n‖ ≤ ((n : ℝ) + 1)⁻¹) (K N Y : ℕ) (hK : 0 < K) :
    ‖(∑ n ∈ range N, F n * ∏ i : Fin K, (z i) ^ omegaNat (n + i + 1))
        - ∑ d ∈ Fintype.piFinset (fun _ : Fin K => range (Y + 1)),
            (∏ i : Fin K, sqfW (z i) (d i)) *
              ∑ n ∈ (range N).filter (fun n => ∀ i : Fin K, d i ∣ n + i + 1),
                F n * ∏ i : Fin K,
                  (z i) ^ ArithmeticFunction.cardFactors ((n + i + 1) / d i)‖
      ≤ (K : ℝ) * truncA z Y K
        + ((1 + Real.log N) * (K : ℝ) ^ (K * K)) * truncB z Y K := by
  classical
  have hKR : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  refine multi_truncation_telescope z hz N Y K F (range N) (K : ℝ)
    ((1 + Real.log N) * (K : ℝ) ^ (K * K)) hKR (by positivity)
    (fun n hn => Finset.mem_range.1 hn) ?_
  intro r hr1 hrK g hg
  have hmass := joint_multi_harmonic_mass (F := F) hF
    (S := (range N).filter (fun n => ∀ s, s < r → g s ∣ n + (K - r) + s + 1))
    (M := N) (m := K - r) (K := r)
    (fun n hn => Finset.mem_range.1 (Finset.mem_filter.1 hn).1) (by omega) g hg
    (fun n hn s hs => (Finset.mem_filter.1 hn).2 s hs)
  refine hmass.trans (add_le_add ?_ ?_)
  · refine div_le_div_of_nonneg_right ?_ ?_
    · have : (K - r : ℕ) + 1 ≤ K := by omega
      exact_mod_cast (by exact_mod_cast this : ((K - r : ℕ) : ℝ) + 1 ≤ (K : ℝ))
    · exact Nat.cast_nonneg _
  · refine div_le_div_of_nonneg_right ?_ ?_
    · have hpow : (r : ℝ) ^ (r * r) ≤ (K : ℝ) ^ (K * K) := by
        have h1 : (r : ℕ) ^ (r * r) ≤ K ^ (K * K) := by
          calc r ^ (r * r) ≤ K ^ (r * r) := Nat.pow_le_pow_left hrK _
            _ ≤ K ^ (K * K) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hrK hrK)
        exact_mod_cast h1
      have h1 : (0 : ℝ) ≤ 1 + Real.log N := by linarith
      exact mul_le_mul_of_nonneg_left hpow h1
    · exact Finset.prod_nonneg fun s _ => Nat.cast_nonneg _

#print axioms multi_truncation_bound
#print axioms truncB_tendsto

end CastingOut

end NormalNumbers
