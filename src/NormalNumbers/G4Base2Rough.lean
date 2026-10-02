/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2Mertens
import NormalNumbers.PrimeModelRadicalMoment

/-!
# Rough-number count for `I`-products

`card_prodLe_le'`: the squarefree `I`-products `≤ x` (all primes of `I` above `Y`, `x ≤ Y^{102}`)
number at most `1 + e⁵ log 4 · x / log Y`; `sum_prodLe_inv_le`: their reciprocal mass is `≤ e⁵`.
Proof: peel one prime `P ∈ (Y, x/∏T']` and count it by Chebyshev (`theta_le`).
-/

open Finset
namespace NormalNumbers.G4.Base2

/-- `I`-products `≤ x`. -/
noncomputable def prodLe (I : Finset ℕ) (x : ℝ) : Finset (Finset ℕ) :=
  I.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) ≤ x)

/-- Chebyshev on a window: `#{Y < P ≤ z prime} · log Y ≤ z log 4`. -/
lemma card_primes_window_mul_log_le (Y z : ℕ) (hY : 1 ≤ Y) :
    (((Iic z).filter (fun P => P.Prime ∧ Y < P)).card : ℝ) * Real.log Y ≤ z * Real.log 4 := by
  refine le_trans ?_ (PrimeModel.Radical.theta_le z)
  unfold PrimeModel.Radical.theta
  rw [← nsmul_eq_mul, ← sum_const]
  calc ∑ _P ∈ (Iic z).filter (fun P => P.Prime ∧ Y < P), Real.log Y
      ≤ ∑ P ∈ (Iic z).filter (fun P => P.Prime ∧ Y < P), Real.log P :=
        sum_le_sum fun P hP => Real.log_le_log (by exact_mod_cast hY)
          (by exact_mod_cast (mem_filter.1 hP).2.2.le)
    _ ≤ ∑ P ∈ (Iic z).filter Nat.Prime, Real.log P :=
        sum_le_sum_of_subset_of_nonneg (fun P hP => by
          simp only [mem_filter] at hP ⊢; exact ⟨hP.1, hP.2.1⟩)
          (fun P hP _ => Real.log_nonneg (by exact_mod_cast (mem_filter.1 hP).2.one_lt.le))

lemma one_le_prod_cast {I T : Finset ℕ} (hI : ∀ p ∈ I, p.Prime) (hT : T ⊆ I) :
    (1 : ℝ) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by
  have : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hI p (hT hp)).pos
  exact_mod_cast this

/-- **Rough count.**  `#prodLe I x ≤ 1 + (x log 4 / log Y) · Σ_{T ∈ prodLe I (x/Y)} 1/∏T`. -/
theorem card_prodLe_le {I : Finset ℕ} {Y : ℕ} (hY : 2 ≤ Y) (hI : ∀ p ∈ I, p.Prime ∧ Y < p)
    {x : ℝ} (hx : 0 ≤ x) :
    ((prodLe I x).card : ℝ) ≤ 1 + x * Real.log 4 / Real.log Y *
      ∑ T ∈ prodLe I (x / Y), ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ := by
  have hYr : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hIp : ∀ p ∈ I, p.Prime := fun p hp => (hI p hp).1
  set W : Finset ℕ → Finset ℕ := fun T' =>
    (Iic ⌊x / ((∏ p ∈ T', p : ℕ) : ℝ)⌋₊).filter (fun P => P.Prime ∧ Y < P) with hW
  have hsub : prodLe I x ⊆ insert ∅ ((prodLe I (x / Y)).biUnion
      (fun T' => ((W T').filter (· ∈ I)).image (fun P => insert P T'))) := by
    intro T hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨P, hP⟩
    · exact mem_insert_self _ _
    refine mem_insert_of_mem (mem_biUnion.2 ⟨T.erase P, ?_, mem_image.2 ⟨P, ?_, insert_erase hP⟩⟩)
    all_goals
      simp only [prodLe, mem_filter, mem_powerset] at hT
      have hPI : P ∈ I := hT.1 hP
      have hprod : ((∏ p ∈ T, p : ℕ) : ℝ) = P * ((∏ p ∈ T.erase P, p : ℕ) : ℝ) := by
        rw [← mul_prod_erase T (fun p => p) hP]; push_cast; ring
      have h1 := one_le_prod_cast hIp ((erase_subset P T).trans hT.1)
      have hPY : (Y : ℝ) < P := by exact_mod_cast (hI P hPI).2
      have hx2 := hT.2
      rw [hprod] at hx2
    · simp only [prodLe, mem_filter, mem_powerset]
      refine ⟨(erase_subset P T).trans hT.1, ?_⟩
      rw [le_div_iff₀ (by linarith)]; nlinarith
    · simp only [hW, mem_filter, mem_Iic]
      refine ⟨⟨Nat.le_floor ?_, (hI P hPI).1, (hI P hPI).2⟩, hPI⟩
      rw [le_div_iff₀ (by linarith)]; linarith
  have hcard := (Nat.cast_le (α := ℝ)).2 (card_le_card hsub)
  refine hcard.trans ?_
  refine (Nat.cast_le.2 (card_insert_le _ _)).trans ?_
  push_cast
  rw [add_comm]; gcongr
  refine (Nat.cast_le.2 card_biUnion_le).trans ?_
  push_cast
  rw [mul_sum]
  refine sum_le_sum fun T' hT' => ?_
  refine (Nat.cast_le.2 (card_image_le.trans (card_filter_le _ _))).trans ?_
  simp only [prodLe, mem_filter, mem_powerset] at hT'
  have h1 := one_le_prod_cast hIp hT'.1
  have hc := card_primes_window_mul_log_le Y ⌊x / ((∏ p ∈ T', p : ℕ) : ℝ)⌋₊ (by omega)
  have hfl := Nat.floor_le (div_nonneg hx (by linarith : (0:ℝ) ≤ ((∏ p ∈ T', p : ℕ) : ℝ)))
  rw [← le_div_iff₀ hlogY] at hc
  refine hc.trans ?_
  rw [div_le_iff₀ hlogY]
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e : x * Real.log 4 / Real.log Y * ((∏ p ∈ T', p : ℕ) : ℝ)⁻¹ * Real.log Y
      = x / ((∏ p ∈ T', p : ℕ) : ℝ) * Real.log 4 := by field_simp
  rw [← Nat.cast_prod, e]; gcongr

/-- `Σ_{T ∈ prodLe I x} 1/∏T ≤ exp(Σ_{p ∈ I, p ≤ x} 1/p)`. -/
theorem sum_prodLe_inv_le_exp {I : Finset ℕ} (hI : ∀ p ∈ I, p.Prime) (x : ℝ) :
    ∑ T ∈ prodLe I x, ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹
      ≤ Real.exp (∑ p ∈ I.filter (fun p : ℕ => (p : ℝ) ≤ x), (p : ℝ)⁻¹) := by
  set J := I.filter (fun p : ℕ => (p : ℝ) ≤ x)
  have hsub : prodLe I x ⊆ J.powerset := by
    intro T hT
    simp only [prodLe, mem_filter, mem_powerset] at hT ⊢
    intro p hp
    refine mem_filter.2 ⟨hT.1 hp, ?_⟩
    have hle : p ≤ ∏ q ∈ T, q :=
      Nat.le_of_dvd (prod_pos fun q hq => (hI q (hT.1 hq)).pos) (dvd_prod_of_mem _ hp)
    have : (p : ℝ) ≤ ((∏ q ∈ T, q : ℕ) : ℝ) := by exact_mod_cast hle
    linarith [hT.2]
  calc ∑ T ∈ prodLe I x, ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹
      ≤ ∑ T ∈ J.powerset, ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∏ p ∈ J, (1 + (p : ℝ)⁻¹) := by
        rw [prod_one_add]; refine sum_congr rfl fun T _ => ?_
        rw [Nat.cast_prod, prod_inv_distrib]
    _ ≤ _ := Real.prod_one_add_le_exp_sum _ fun p => by positivity

/-- For `log Y ≥ 13860` and `x ≤ Y^{102}`: `Σ_{T ∈ prodLe I x} 1/∏T ≤ e⁵`. -/
theorem sum_prodLe_inv_le {I : Finset ℕ} {Y : ℕ} (hY : 13860 ≤ Real.log Y)
    (hI : ∀ p ∈ I, p.Prime ∧ Y < p) {x : ℝ} (hx : x ≤ (Y : ℝ) ^ 102) :
    ∑ T ∈ prodLe I x, ((∏ p ∈ T, p : ℕ) : ℝ)⁻¹ ≤ Real.exp 5 := by
  refine (sum_prodLe_inv_le_exp (fun p hp => (hI p hp).1) x).trans (Real.exp_le_exp.2 ?_)
  refine le_trans ?_ (sum_inv_primes_Y102_le hY)
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
  obtain ⟨hpI, hpx⟩ := mem_filter.1 hp
  have hle : p ≤ Y ^ 102 := by exact_mod_cast (show (p : ℝ) ≤ ((Y ^ 102 : ℕ) : ℝ) by push_cast; linarith)
  simp only [mem_filter, mem_range]
  exact ⟨by omega, (hI p hpI).1, (hI p hpI).2⟩

/-- **Rough count, explicit.**  `#prodLe I x ≤ 1 + e⁵ log 4 · x / log Y`. -/
theorem card_prodLe_le' {I : Finset ℕ} {Y : ℕ} (hY : 13860 ≤ Real.log Y)
    (hI : ∀ p ∈ I, p.Prime ∧ Y < p) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (Y : ℝ) ^ 102) :
    ((prodLe I x).card : ℝ) ≤ 1 + Real.exp 5 * Real.log 4 * x / Real.log Y := by
  have hY1 : (1 : ℝ) < Y := (Real.log_pos_iff (Nat.cast_nonneg _)).1 (by linarith)
  have hY2 : 2 ≤ Y := by
    by_contra h
    have : Y ≤ 1 := by omega
    have : (Y : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  have h := card_prodLe_le hY2 hI hx0
  have hs := sum_prodLe_inv_le hY hI (x := x / Y) (by
    rw [div_le_iff₀ (by linarith)]
    calc x ≤ (Y : ℝ) ^ 102 := hx
      _ ≤ (Y : ℝ) ^ 102 * Y := le_mul_of_one_le_right (by positivity) hY1.le)
  have hlog : 0 < Real.log Y := by linarith
  have hk : 0 ≤ x * Real.log 4 / Real.log Y :=
    div_nonneg (mul_nonneg hx0 (Real.log_nonneg (by norm_num))) hlog.le
  calc ((prodLe I x).card : ℝ) ≤ 1 + x * Real.log 4 / Real.log Y * Real.exp 5 := by
        have := mul_le_mul_of_nonneg_left hs hk; linarith
    _ = _ := by ring
end NormalNumbers.G4.Base2
