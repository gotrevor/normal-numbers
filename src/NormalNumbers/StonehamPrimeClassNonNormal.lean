/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassSchedule
import NormalNumbers.Wall

/-!
# Positive-density obstruction for the dependent prime class

The arithmetic schedule makes a rational orbit state integral on geometrically dilated
intervals.  Lemma 1 for Stoneham sums puts the true orbit within `O(1/n)` of that integer.
This file supplies the missing analytic abstraction: such an orbit cannot be equidistributed,
because every dilated cell visits two arbitrarily thin intervals at the ends of `[0,1)` while
occupying a fixed positive proportion of its right endpoint.
-/

namespace NormalNumbers.StonehamPrimeClass

open Filter Finset

/-- A real within `ε` of an integer has fractional part in one of the two edge intervals. -/
lemma fract_mem_edge_of_abs_sub_int_lt
    {y ε : ℝ} {z : ℤ} (_hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h : |y - (z : ℝ)| < ε) :
    Int.fract y ∈ Set.Ico (0 : ℝ) ε ∨ Int.fract y ∈ Set.Ico (1 - ε) 1 := by
  have hd := (abs_lt.mp h)
  by_cases hnonneg : 0 ≤ y - (z : ℝ)
  · left
    have hlt : y - (z : ℝ) < 1 := hd.2.trans_le hε1
    have hfr : Int.fract y = y - (z : ℝ) := by
      rw [← Int.fract_sub_intCast]
      exact Int.fract_eq_self.mpr ⟨hnonneg, hlt⟩
    rw [hfr]
    exact ⟨hnonneg, hd.2⟩
  · right
    have hneg : y - (z : ℝ) < 0 := lt_of_not_ge hnonneg
    have hnonneg' : 0 ≤ y - (z : ℝ) + 1 := by linarith
    have hlt' : y - (z : ℝ) + 1 < 1 := by linarith
    have hfrSub : Int.fract (y - (z : ℝ)) = y - (z : ℝ) + 1 := by
      rw [← Int.fract_add_one]
      exact Int.fract_eq_self.mpr ⟨hnonneg', hlt'⟩
    have hfr : Int.fract y = y - (z : ℝ) + 1 := by
      rw [← Int.fract_sub_intCast]
      exact hfrSub
    rw [hfr]
    exact ⟨by linarith, hlt'⟩

/-- An equidistributed sequence cannot remain in two thin edge intervals throughout every
geometric cell `[A p^(Lt), (A+1) p^(Lt))`. -/
theorem not_equidistributed_of_geometric_edge_visits
    (v : ℕ → ℝ)
    (p L A t₀ : ℕ) (hp : 2 ≤ p) (hL : 1 ≤ L) (hA : 1 ≤ A)
    (hedge : ∀ t, t₀ ≤ t → ∀ n,
      A * p ^ (L * t) ≤ n → n < (A + 1) * p ^ (L * t) →
        v n ∈ Set.Ico (0 : ℝ) (1 / (8 * (A + 1 : ℝ))) ∨
          v n ∈ Set.Ico (1 - 1 / (8 * (A + 1 : ℝ))) 1) :
    ¬ Equidistributed v := by
  intro heq
  let δ : ℝ := 1 / (A + 1 : ℝ)
  let ε : ℝ := δ / 8
  have hApos : (0 : ℝ) < A + 1 := by positivity
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_one hApos]
    norm_num
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    nlinarith
  have hεform : ε = 1 / (8 * (A + 1 : ℝ)) := by
    dsimp [ε, δ]
    rw [div_div]
    congr 1
    ring
  have hleft := heq 0 ε (by norm_num) hε0.le hε1
  have hright := heq (1 - ε) 1 (by linarith) (by linarith) le_rfl
  have hright' : Tendsto
      (fun n => (visitCount v (1 - ε) 1 n : ℝ) / n) atTop (nhds ε) := by
    simpa only [sub_sub_cancel] using hright
  rw [Metric.tendsto_atTop] at hleft hright'
  obtain ⟨N₁, hN₁⟩ := hleft (δ / 8) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hright' (δ / 8) (by positivity)
  let t := max t₀ (max N₁ N₂)
  let R := p ^ (L * t)
  let lo := A * R
  let hi := (A + 1) * R
  have ht₀ : t₀ ≤ t := le_max_left _ _
  have hN₁t : N₁ ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₂t : N₂ ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have htExp : t ≤ L * t := by nlinarith
  have htR : t ≤ R := by
    dsimp only [R]
    exact (Nat.lt_pow_self hp).le.trans
      (Nat.pow_le_pow_right (by omega : 0 < p) htExp)
  have hRpos : 0 < R := by dsimp only [R]; positivity
  have hRhi : R ≤ hi := by
    dsimp only [hi]
    nlinarith
  have hN₁hi : N₁ ≤ hi := hN₁t.trans (htR.trans hRhi)
  have hN₂hi : N₂ ≤ hi := hN₂t.trans (htR.trans hRhi)
  have hleftClose := hN₁ hi hN₁hi
  have hrightClose := hN₂ hi hN₂hi
  rw [Real.dist_eq, abs_lt] at hleftClose hrightClose
  simp only [sub_zero] at hleftClose
  dsimp only [ε] at hleftClose hrightClose
  have hleftUpper : (visitCount v 0 ε hi : ℝ) / hi < δ / 4 := by
    linarith [hleftClose.2]
  have hrightUpper : (visitCount v (1 - ε) 1 hi : ℝ) / hi < δ / 4 := by
    linarith [hrightClose.2]
  have hsub : Ico lo hi ⊆
      ((range hi).filter fun n => v n ∈ Set.Ico (0 : ℝ) ε) ∪
        ((range hi).filter fun n => v n ∈ Set.Ico (1 - ε) 1) := by
    intro n hn
    have hn' := mem_Ico.mp hn
    have hedge' := hedge t ht₀ n (by simpa only [lo, R] using hn'.1)
      (by simpa only [hi, R] using hn'.2)
    simp only [mem_union, mem_filter, mem_range, hn'.2, true_and]
    rw [hεform]
    exact hedge'
  have hcard : (Ico lo hi).card ≤
      ((range hi).filter fun n => v n ∈ Set.Ico (0 : ℝ) ε).card +
        ((range hi).filter fun n => v n ∈ Set.Ico (1 - ε) 1).card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hhilo : hi = lo + R := by
    dsimp only [hi, lo]
    ring
  have hcell : (Ico lo hi).card = R := by
    rw [Nat.card_Ico, hhilo, Nat.add_sub_cancel_left]
  have hcount : R ≤ visitCount v 0 ε hi + visitCount v (1 - ε) 1 hi := by
    rw [hcell] at hcard
    simpa only [visitCount] using hcard
  have hhiPos : (0 : ℝ) < hi := by exact_mod_cast (lt_of_lt_of_le hRpos hRhi)
  have hcountR : (R : ℝ) / hi ≤
      (visitCount v 0 ε hi : ℝ) / hi +
        (visitCount v (1 - ε) 1 hi : ℝ) / hi := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) hhiPos.le
  have hratio : (R : ℝ) / hi = δ := by
    dsimp only [hi, δ]
    push_cast
    field_simp
  rw [hratio] at hcountR
  linarith

/-- If the multiply-by-`b` orbit is `O(1/n)` from an integer throughout fixed-proportion
geometric cells, then the underlying real is not `b`-normal. -/
theorem not_isNormal_of_geometric_integer_approx
    (b p L A : ℕ) (hb : 2 ≤ b) (hp : 2 ≤ p) (hL : 1 ≤ L) (hA : 1 ≤ A)
    (x C : ℝ)
    (happrox : ∀ t n,
      A * p ^ (L * t) ≤ n → n < (A + 1) * p ^ (L * t) → 1 ≤ n →
      ∃ z : ℤ, |(b : ℝ) ^ n * x - (z : ℝ)| ≤ C / n) :
    ¬ IsNormal b x := by
  intro hnormal
  have heq : Equidistributed (orbit b x) :=
    (isNormal_iff_equidistributed_orbit b hb x).mp hnormal
  let δ : ℝ := 1 / (A + 1 : ℝ)
  let ε : ℝ := δ / 8
  have hε0 : 0 < ε := by dsimp [ε, δ]; positivity
  have hApos : (0 : ℝ) < A + 1 := by positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_one hApos]
    norm_num
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    nlinarith
  have hεform : ε = 1 / (8 * (A + 1 : ℝ)) := by
    dsimp [ε, δ]
    rw [div_div]
    congr 1
    ring
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt (C / ε)
  apply not_equidistributed_of_geometric_edge_visits
    (orbit b x) p L A t₀ hp hL hA (fun t htt n hnlower hnupper => ?_) heq
  have htExp : t ≤ L * t := by nlinarith
  have htPow : t ≤ p ^ (L * t) :=
    (Nat.lt_pow_self hp).le.trans (Nat.pow_le_pow_right (by omega : 0 < p) htExp)
  have hnpos : 1 ≤ n := by
    have hpowpos : 0 < p ^ (L * t) := by positivity
    nlinarith
  obtain ⟨z, hz⟩ := happrox t n hnlower hnupper hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hCdiv : C / n < ε := by
    apply (div_lt_iff₀ hnR).2
    have httR : (t₀ : ℝ) ≤ n := by
      exact_mod_cast htt.trans (htPow.trans (by nlinarith [hnlower]))
    have hratio : C / ε < n := lt_of_lt_of_le ht₀ httR
    simpa only [mul_comm] using (div_lt_iff₀ hε0).1 hratio
  have hclose : |(b : ℝ) ^ n * x - (z : ℝ)| < ε := hz.trans_lt hCdiv
  have hedge := fract_mem_edge_of_abs_sub_int_lt hε0 hε1 hclose
  simpa only [orbit, mul_comm, hεform] using hedge

end NormalNumbers.StonehamPrimeClass
