/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import NormalNumbers.CoefmassErdosBorweinNegative

/-!
# Marginal criterion for sub-power Erdős--Borwein weights

This file isolates the probabilistic/Fatou part of the sub-power argument.  Its hypotheses involve
only the one-coordinate marginals.  The remaining arithmetic task is to verify that the capped
deterministic residual tends to zero for `subpowerWeight`.
-/

namespace NormalNumbers.ErdosBorweinSubpower

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinRandom

/-- Expected number of selected divisors above `M`, expressed using only the marginal masses. -/
noncomputable def marginalDivisorMass (delta : ℕ → ℝ) (M n : ℕ) : ℝ :=
  ∑ m ∈ n.divisors.filter (fun m => M < m), delta m

lemma marginalDivisorMass_nonneg (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m) (M n : ℕ) :
    0 ≤ marginalDivisorMass delta M n := by
  unfold marginalDivisorMass
  exact Finset.sum_nonneg fun m _ => hdelta m

lemma marginalDivisorMass_le_card_divisors (delta : ℕ → ℝ)
    (hdelta : ∀ m, delta m ≤ 1) (M n : ℕ) :
    marginalDivisorMass delta M n ≤ n.divisors.card := by
  unfold marginalDivisorMass
  calc
    (∑ m ∈ n.divisors.filter (fun m => M < m), delta m) ≤
        ∑ _m ∈ n.divisors.filter (fun m => M < m), (1 : ℝ) := by
      exact Finset.sum_le_sum fun m _ => hdelta m
    _ = ((n.divisors.filter (fun m => M < m)).card : ℝ) := by simp
    _ ≤ n.divisors.card := by exact_mod_cast Finset.card_filter_le _ _

/-! ### Weighted logarithmic blocks

The sub-power argument uses the same double-exponential divisor blocks as the power-weight
argument, but the weight and the fractional-moment exponent now vary with the block.  The next
lemmas separate the combinatorial and Markov steps from the eventual real-variable estimates for
the particular sub-power weight. -/

/-- Contribution of an arbitrary weight from one double-exponential divisor block. -/
noncomputable def weightedDivisorBlockMass (weight : ℕ → ℝ) (ℓ n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter
    (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1)), weight d

lemma weightedDivisorBlockMass_nonneg (weight : ℕ → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (ℓ n : ℕ) :
    0 ≤ weightedDivisorBlockMass weight ℓ n := by
  unfold weightedDivisorBlockMass
  exact Finset.sum_nonneg fun d _ => hweight d

/-- Tail of an arbitrary divisor weight above a cutoff. -/
noncomputable def weightedDivisorTailMass (weight : ℕ → ℝ) (M n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => M < d), weight d

lemma weightedDivisorTailMass_nonneg (weight : ℕ → ℝ) (hweight : ∀ d, 0 ≤ weight d)
    (M n : ℕ) : 0 ≤ weightedDivisorTailMass weight M n := by
  unfold weightedDivisorTailMass
  exact Finset.sum_nonneg fun d _ => hweight d

lemma marginalDivisorMass_le_const_weight (delta weight : ℕ → ℝ) (C : ℝ)
    (hdelta : ∀ m, delta m ≤ C * weight m) (M n : ℕ) :
    marginalDivisorMass delta M n ≤ C * weightedDivisorTailMass weight M n := by
  unfold marginalDivisorMass weightedDivisorTailMass
  calc
    (∑ m ∈ n.divisors.filter (fun m => M < m), delta m) ≤
        ∑ m ∈ n.divisors.filter (fun m => M < m), C * weight m := by
      exact Finset.sum_le_sum fun m _ => hdelta m
    _ = C * ∑ m ∈ n.divisors.filter (fun m => M < m), weight m := by
      rw [Finset.mul_sum]

/-- The same comparison with the domination hypothesis required only above the active cutoff. -/
lemma marginalDivisorMass_le_const_weight_of_cutoff (delta weight : ℕ → ℝ) (C : ℝ)
    (M n : ℕ) (hdelta : ∀ m, M < m → delta m ≤ C * weight m) :
    marginalDivisorMass delta M n ≤ C * weightedDivisorTailMass weight M n := by
  unfold marginalDivisorMass weightedDivisorTailMass
  calc
    (∑ m ∈ n.divisors.filter (fun m => M < m), delta m) ≤
        ∑ m ∈ n.divisors.filter (fun m => M < m), C * weight m := by
      exact Finset.sum_le_sum fun m hm => hdelta m (Finset.mem_filter.mp hm).2
    _ = C * ∑ m ∈ n.divisors.filter (fun m => M < m), weight m := by
      rw [Finset.mul_sum]

lemma weightedDivisorTailMass_cutoff_step (weight : ℕ → ℝ) (ℓ n : ℕ) :
    weightedDivisorTailMass weight (dyadicExpCutoff ℓ) n =
      weightedDivisorBlockMass weight ℓ n +
        weightedDivisorTailMass weight (dyadicExpCutoff (ℓ + 1)) n := by
  rw [weightedDivisorTailMass, weightedDivisorBlockMass, weightedDivisorTailMass]
  let S := n.divisors.filter (fun d => dyadicExpCutoff ℓ < d)
  let p := fun d : ℕ => d ≤ dyadicExpCutoff (ℓ + 1)
  calc
    (∑ d ∈ S, weight d) =
        (∑ d ∈ S.filter p, weight d) + ∑ d ∈ S.filter (fun d => ¬p d), weight d :=
      (Finset.sum_filter_add_sum_filter_not S p weight).symm
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr
        · ext d
          simp [S, p, and_assoc]
        · intro d hd
          rfl
      · apply Finset.sum_congr
        · ext d
          simp only [S, p, Finset.mem_filter, Nat.not_le]
          have hcut := dyadicExpCutoff_le_succ ℓ
          constructor
          · rintro ⟨⟨hd, -⟩, hnext⟩
            exact ⟨hd, hnext⟩
          · rintro ⟨hd, hnext⟩
            exact ⟨⟨hd, hcut.trans_lt hnext⟩, hnext⟩
        · intro d hd
          rfl

lemma weightedDivisorTailMass_cutoff_iterate (weight : ℕ → ℝ) (L K n : ℕ) :
    weightedDivisorTailMass weight (dyadicExpCutoff L) n =
      (∑ i ∈ Finset.range K, weightedDivisorBlockMass weight (L + i) n) +
        weightedDivisorTailMass weight (dyadicExpCutoff (L + K)) n := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [ih, Finset.sum_range_succ, weightedDivisorTailMass_cutoff_step]
      simp only [Nat.add_assoc]
      ring

lemma weightedDivisorTailMass_eq_block_sum (weight : ℕ → ℝ) (L n : ℕ) (hn : 1 ≤ n) :
    weightedDivisorTailMass weight (dyadicExpCutoff L) n =
      ∑ i ∈ Finset.range n, weightedDivisorBlockMass weight (L + i) n := by
  rw [weightedDivisorTailMass_cutoff_iterate weight L n n]
  have htail : weightedDivisorTailMass weight (dyadicExpCutoff (L + n)) n = 0 := by
    unfold weightedDivisorTailMass
    apply Finset.sum_eq_zero
    intro d hd
    have hdn : d ≤ n := Nat.le_of_dvd (by omega)
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
    have hcutd := (Finset.mem_filter.mp hd).2
    have hcutn := index_le_dyadicExpCutoff_add L n
    omega
  rw [htail, add_zero]

/-- A pointwise cap on the weight throughout a block converts its mass to the already-controlled
smooth-divisor count at the right endpoint. -/
lemma weightedDivisorBlockMass_le_smoothDivisorCount
    (weight : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W) (ℓ n : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) → weight d ≤ W) :
    weightedDivisorBlockMass weight ℓ n ≤
      (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W := by
  let S := n.divisors.filter
    (fun d => dyadicExpCutoff ℓ < d ∧ d ≤ dyadicExpCutoff (ℓ + 1))
  calc
    weightedDivisorBlockMass weight ℓ n = ∑ d ∈ S, weight d := rfl
    _ ≤ ∑ _d ∈ S, W := by
      exact Finset.sum_le_sum fun d hd =>
        hweight d (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hd).2.2
    _ = (S.card : ℝ) * W := by simp [mul_comm]
    _ ≤ (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast divisorBlock_card_le n ℓ) hW

/-- Fractional moment of an arbitrary weighted block.  All dependence on the weight is through a
single block cap `W`; the smooth-divisor Euler product is uniform in `s ∈ (0,1]`. -/
lemma weightedDivisorBlockMass_rpow_sum_le
    (weight : ℕ → ℝ) (W s : ℝ) (hweight0 : ∀ d, 0 ≤ weight d) (hW : 0 ≤ W)
    (hs : 0 < s) (hs1 : s ≤ 1) (ℓ N : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) → weight d ≤ W) :
    (∑ n ∈ Finset.Icc 1 N, Real.rpow (weightedDivisorBlockMass weight ℓ n) s) ≤
      Real.rpow W s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  have hpoint : ∀ n, Real.rpow (weightedDivisorBlockMass weight ℓ n) s ≤
      Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s * Real.rpow W s := by
    intro n
    calc
      Real.rpow (weightedDivisorBlockMass weight ℓ n) s ≤
          Real.rpow ((smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) * W) s := by
        exact Real.rpow_le_rpow (weightedDivisorBlockMass_nonneg weight hweight0 ℓ n)
          (weightedDivisorBlockMass_le_smoothDivisorCount weight W hW ℓ n hweight) hs.le
      _ = Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
          Real.rpow W s := by
        exact Real.mul_rpow (by positivity) hW
  calc
    (∑ n ∈ Finset.Icc 1 N, Real.rpow (weightedDivisorBlockMass weight ℓ n) s) ≤
        ∑ n ∈ Finset.Icc 1 N,
          Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s *
            Real.rpow W s := by
      exact Finset.sum_le_sum fun n _ => hpoint n
    _ = Real.rpow W s *
        ∑ n ∈ Finset.Icc 1 N,
          Real.rpow (smoothDivisorCount (dyadicExpCutoff (ℓ + 1)) n : ℝ) s := by
      simp [Finset.mul_sum, mul_comm]
    _ ≤ Real.rpow W s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
      exact mul_le_mul_of_nonneg_left
        (smoothDivisorCount_rpow_sum_le_log_rpow s hs hs1 (dyadicExpCutoff (ℓ + 1))
          (dyadicExpCutoff_two_le (ℓ + 1)) N)
        (Real.rpow_nonneg hW _)

/-- Per-block counting Chernoff bound.  This is the exact form needed before summing over the shift
thresholds and over blocks: every large value pays `Y^s`, while the numerator is the uniform
smooth-divisor fractional moment. -/
lemma weightedDivisorBlockMass_large_card_mul_rpow_le
    (weight : ℕ → ℝ) (W Y s : ℝ) (hweight0 : ∀ d, 0 ≤ weight d) (hW : 0 ≤ W)
    (hY : 0 ≤ Y) (hs : 0 < s) (hs1 : s ≤ 1) (ℓ N : ℕ)
    (hweight : ∀ d : ℕ, dyadicExpCutoff ℓ < d → d ≤ dyadicExpCutoff (ℓ + 1) → weight d ≤ W) :
    (((Finset.Icc 1 N).filter
        (fun n => Y < weightedDivisorBlockMass weight ℓ n)).card : ℝ) * Real.rpow Y s ≤
      Real.rpow W s *
        (N * (Real.exp (((2 : ℝ) ^ s - 1) * Erdos67.PrimeEstimates.mertensBound + 1) *
          Real.rpow (Real.log (dyadicExpCutoff (ℓ + 1) : ℝ)) ((2 : ℝ) ^ s - 1))) := by
  let S := (Finset.Icc 1 N).filter
    (fun n => Y < weightedDivisorBlockMass weight ℓ n)
  calc
    (S.card : ℝ) * Real.rpow Y s = ∑ _n ∈ S, Real.rpow Y s := by simp [mul_comm]
    _ ≤ ∑ n ∈ S, Real.rpow (weightedDivisorBlockMass weight ℓ n) s := by
      exact Finset.sum_le_sum fun n hn =>
        (Real.rpow_lt_rpow hY (Finset.mem_filter.mp hn).2 hs).le
    _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.rpow (weightedDivisorBlockMass weight ℓ n) s := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => Real.rpow_nonneg
          (weightedDivisorBlockMass_nonneg weight hweight0 ℓ n) _)
    _ ≤ _ := weightedDivisorBlockMass_rpow_sum_le weight W s hweight0 hW hs hs1 ℓ N hweight

/-- Telescoping allocation of a global tail threshold among logarithmic blocks. -/
noncomputable def blockAllocation (ℓ : ℕ) : ℝ :=
  1 / (((ℓ : ℝ) + 1) * ((ℓ : ℝ) + 2))

lemma blockAllocation_pos (ℓ : ℕ) : 0 < blockAllocation ℓ := by
  unfold blockAllocation
  positivity

lemma blockAllocation_eq_sub (ℓ : ℕ) :
    blockAllocation ℓ = 1 / ((ℓ : ℝ) + 1) - 1 / ((ℓ : ℝ) + 2) := by
  unfold blockAllocation
  field_simp
  ring

lemma sum_range_blockAllocation (K : ℕ) :
    ∑ ℓ ∈ Finset.range K, blockAllocation ℓ = 1 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, blockAllocation_eq_sub]
      push_cast
      ring

lemma sum_range_blockAllocation_le_one (K : ℕ) :
    ∑ ℓ ∈ Finset.range K, blockAllocation ℓ ≤ 1 := by
  rw [sum_range_blockAllocation]
  have h : 0 ≤ 1 / ((K : ℝ) + 1) := by positivity
  linarith

lemma sum_range_blockAllocation_add (L K : ℕ) :
    ∑ i ∈ Finset.range K, blockAllocation (L + i) =
      1 / ((L : ℝ) + 1) - 1 / ((L + K : ℕ) + 1 : ℕ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, blockAllocation_eq_sub]
      push_cast
      ring

lemma sum_range_blockAllocation_add_le_one (L K : ℕ) :
    ∑ i ∈ Finset.range K, blockAllocation (L + i) ≤ 1 := by
  calc
    (∑ i ∈ Finset.range K, blockAllocation (L + i)) =
        1 / ((L : ℝ) + 1) - 1 / ((L + K : ℕ) + 1 : ℕ) :=
      sum_range_blockAllocation_add L K
    _ ≤ 1 / ((L : ℝ) + 1) := by
      exact sub_le_self _ (by positivity)
    _ ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (L : ℝ) + 1)).2
      have hL : (0 : ℝ) ≤ L := by positivity
      linarith

/-- If a weighted divisor tail exceeds `X`, one logarithmic block exceeds its telescoping share of
`X`. -/
lemma exists_weightedDivisorBlockMass_gt_allocation
    (weight : ℕ → ℝ) (L n : ℕ) (hn : 1 ≤ n) (X : ℝ) (hX : 0 ≤ X)
    (htail : X < weightedDivisorTailMass weight (dyadicExpCutoff L) n) :
    ∃ i ∈ Finset.range n,
      X * blockAllocation (L + i) < weightedDivisorBlockMass weight (L + i) n := by
  classical
  rw [weightedDivisorTailMass_eq_block_sum weight L n hn] at htail
  by_contra h
  push_neg at h
  have hsum :
      (∑ i ∈ Finset.range n, weightedDivisorBlockMass weight (L + i) n) ≤
        ∑ i ∈ Finset.range n, X * blockAllocation (L + i) := by
    exact Finset.sum_le_sum fun i hi => h i hi
  have halloc := sum_range_blockAllocation_add_le_one L n
  have hright : (∑ i ∈ Finset.range n, X * blockAllocation (L + i)) ≤ X := by
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_of_nonneg_left halloc hX
  linarith

lemma exists_weightedDivisorBlockMass_gt_of_marginal
    (delta weight : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (L n : ℕ) (hdelta : ∀ m, dyadicExpCutoff L < m → delta m ≤ C * weight m)
    (hn : 1 ≤ n) (Y : ℝ) (hY : 0 ≤ Y)
    (hmass : Y < marginalDivisorMass delta (dyadicExpCutoff L) n) :
    ∃ i ∈ Finset.range n,
      (Y / C) * blockAllocation (L + i) <
        weightedDivisorBlockMass weight (L + i) n := by
  have hupper := marginalDivisorMass_le_const_weight_of_cutoff delta weight C
    (dyadicExpCutoff L) n hdelta
  have htail : Y / C < weightedDivisorTailMass weight (dyadicExpCutoff L) n := by
    apply (div_lt_iff₀ hC).2
    simpa [mul_comm] using hmass.trans_le hupper
  exact exists_weightedDivisorBlockMass_gt_allocation weight L n hn (Y / C)
    (div_nonneg hY hC.le) htail

/-- A marginal large-value set is covered by the union of its allocated block large-value sets. -/
lemma marginalDivisorMass_large_card_le_sum_block_cards
    (delta weight : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (L T : ℕ) (hdelta : ∀ m, dyadicExpCutoff L < m → delta m ≤ C * weight m)
    (Y : ℝ) (hY : 0 ≤ Y) :
    (((Finset.Icc 1 T).filter
        (fun n => Y < marginalDivisorMass delta (dyadicExpCutoff L) n)).card) ≤
      ∑ i ∈ Finset.range T,
        ((Finset.Icc 1 T).filter (fun n =>
          (Y / C) * blockAllocation (L + i) <
            weightedDivisorBlockMass weight (L + i) n)).card := by
  classical
  let S := Finset.Icc 1 T
  let B : ℕ → Finset ℕ := fun i => S.filter (fun n =>
    (Y / C) * blockAllocation (L + i) < weightedDivisorBlockMass weight (L + i) n)
  have hsub : S.filter (fun n => Y < marginalDivisorMass delta (dyadicExpCutoff L) n) ⊆
      (Finset.range T).biUnion B := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hnI := Finset.mem_Icc.mp hnS
    obtain ⟨i, hi, hibad⟩ := exists_weightedDivisorBlockMass_gt_of_marginal
      delta weight C hC L n hdelta hnI.1 Y hY (Finset.mem_filter.mp hn).2
    have hiT : i ∈ Finset.range T := by
      rw [Finset.mem_range] at hi ⊢
      exact hi.trans_le hnI.2
    exact Finset.mem_biUnion.mpr ⟨i, hiT, Finset.mem_filter.mpr ⟨hnS, hibad⟩⟩
  calc
    (S.filter (fun n => Y < marginalDivisorMass delta (dyadicExpCutoff L) n)).card ≤
        ((Finset.range T).biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range T, (B i).card := Finset.card_biUnion_le
    _ = _ := by rfl

lemma blockAllocation_rpow_neg_le (ℓ : ℕ) (s δ : ℝ) (hs : 0 ≤ s)
    (hsδ : 2 * s ≤ δ) :
    Real.rpow (blockAllocation ℓ) (-s) ≤ Real.rpow ((ℓ : ℝ) + 2) δ := by
  let d : ℝ := ((ℓ : ℝ) + 1) * ((ℓ : ℝ) + 2)
  let v : ℝ := (ℓ : ℝ) + 2
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : 1 ≤ v := by
    dsimp [v]
    exact_mod_cast (show 1 ≤ ℓ + 2 by omega)
  have hdv : d ≤ v * v := by
    dsimp [d, v]
    nlinarith [show (0 : ℝ) ≤ ℓ by positivity]
  have halloc : blockAllocation ℓ = d⁻¹ := by
    simp [blockAllocation, d, one_div]
  have hpow : Real.rpow (blockAllocation ℓ) (-s) = Real.rpow d s := by
    change blockAllocation ℓ ^ (-s) = d ^ s
    rw [halloc, Real.inv_rpow hd0, Real.rpow_neg hd0, inv_inv]
  rw [hpow]
  calc
    d ^ s ≤ (v * v) ^ s := Real.rpow_le_rpow hd0 hdv hs
    _ = v ^ s * v ^ s := Real.mul_rpow hv0 hv0
    _ = v ^ (2 * s) := by
      rw [← Real.rpow_add (by positivity : 0 < v)]
      congr 1
      ring
    _ ≤ v ^ δ := Real.rpow_le_rpow_of_exponent_le hv1 hsδ

lemma rpow_neg_le_max_one_inv (A s : ℝ) (hA : 0 < A) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.rpow A (-s) ≤ max 1 A⁻¹ := by
  change A ^ (-s) ≤ max 1 A⁻¹
  by_cases hA1 : 1 ≤ A
  · exact (Real.rpow_le_one_of_one_le_of_nonpos hA1 (by linarith)).trans (le_max_left _ _)
  · have hAle : A ≤ 1 := le_of_not_ge hA1
    calc
      A ^ (-s) ≤ A ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hA hAle (by linarith)
      _ = A⁻¹ := Real.rpow_neg_one A
      _ ≤ max 1 A⁻¹ := le_max_right _ _

/-! ### The analytic Chernoff exponent -/

/-- Cubic Taylor control in the exact form used for the variable block exponent. -/
lemma exp_sub_one_sub_le_sq_half_add_cube {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 + x ^ 3 := by
  have h := Real.exp_bound' hx0 hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  nlinarith [mul_nonneg (sq_nonneg x) hx0]

/-- Algebraic core of the per-block exponent estimate.  The two displayed identities are exactly
what the later specialization `σ = sqrt (c log u / u)` supplies. -/
lemma chernoffExponent_le
    (u c σ : ℝ) (hu : 0 ≤ u) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hsq : u * σ ^ 2 = c * Real.log u)
    (hlin : σ * Real.sqrt (c * u * Real.log u) = c * Real.log u) :
    u * (Real.exp σ - 1 - σ) - σ * Real.sqrt (c * u * Real.log u) ≤
      -(c / 2) * Real.log u + u * σ ^ 3 := by
  have h := mul_le_mul_of_nonneg_left (exp_sub_one_sub_le_sq_half_add_cube hσ0 hσ1) hu
  rw [mul_add] at h
  have hquad : u * (σ ^ 2 / 2) = c * Real.log u / 2 := by
    rw [← mul_div_assoc, hsq]
  rw [hquad] at h
  rw [hlin]
  linarith

/-- The variable Chernoff exponent attached to a logarithmic block parameter `u`. -/
noncomputable def blockSigma (c u : ℝ) : ℝ :=
  Real.sqrt (c * Real.log u / u)

/-- The exact `log log` coordinate of the left endpoint of logarithmic block `ℓ`. -/
noncomputable def blockLogLog (ℓ : ℕ) : ℝ :=
  Real.log (Real.log (dyadicExpCutoff ℓ : ℝ))

lemma blockLogLog_eq (ℓ : ℕ) :
    blockLogLog ℓ = (ℓ : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  rw [blockLogLog, log_dyadicExpCutoff]
  rw [Real.log_mul (pow_ne_zero _ (by norm_num))
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
  rw [Real.log_pow]

lemma blockLogLog_succ (ℓ : ℕ) :
    blockLogLog (ℓ + 1) = blockLogLog ℓ + Real.log 2 := by
  rw [blockLogLog_eq, blockLogLog_eq]
  push_cast
  ring

lemma blockLogLog_ge_quarter_add (ℓ : ℕ) (hℓ : 6 ≤ ℓ) :
    ((ℓ : ℝ) + 2) / 4 ≤ blockLogLog ℓ := by
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hexp_log : Real.exp (-1) < Real.log 2 :=
    Real.exp_neg_one_lt_half.trans_le hlogtwo
  have hloglog : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    rw [← Real.log_exp (-1)]
    exact (Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos (-1)))
      (Set.mem_Ioi.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2))) hexp_log.le)
  rw [blockLogLog_eq]
  have hℓr : (6 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  nlinarith [mul_le_mul_of_nonneg_left hlogtwo (by positivity : (0 : ℝ) ≤ ℓ)]

lemma blockLogLog_le_natCast (ℓ : ℕ) : blockLogLog ℓ ≤ (ℓ : ℝ) := by
  have hlogtwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogtwo_one : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hloglog : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hlogtwo_pos.le hlogtwo_one
  rw [blockLogLog_eq]
  nlinarith [mul_le_mul_of_nonneg_left hlogtwo_one (by positivity : (0 : ℝ) ≤ ℓ)]

lemma tendsto_blockLogLog_atTop : Tendsto blockLogLog atTop atTop := by
  rw [show blockLogLog = fun ℓ : ℕ =>
      (ℓ : ℝ) * Real.log 2 + Real.log (Real.log 2) by
    funext ℓ
    exact blockLogLog_eq ℓ]
  exact tendsto_atTop_add_const_right atTop _
    (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

lemma tendsto_blockSigma_atTop_zero (c : ℝ) :
    Tendsto (blockSigma c) atTop (nhds 0) := by
  have hratio : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmul : Tendsto (fun u : ℝ => c * Real.log u / u) atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using tendsto_const_nhds.mul hratio
  change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
    (fun u : ℝ => c * Real.log u / u)) atTop (nhds 0)
  simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hmul

lemma tendsto_blockSigma_blockLogLog_zero (c : ℝ) :
    Tendsto (fun ℓ => blockSigma c (blockLogLog ℓ)) atTop (nhds 0) :=
  (tendsto_blockSigma_atTop_zero c).comp tendsto_blockLogLog_atTop

lemma blockSigma_sq (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    u * blockSigma c u ^ 2 = c * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  rw [blockSigma, Real.sq_sqrt (div_nonneg (mul_nonneg hc hlog) hu0.le)]
  field_simp

lemma blockSigma_mul_sqrt (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    blockSigma c u * Real.sqrt (c * u * Real.log u) = c * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hA : 0 ≤ c * Real.log u := mul_nonneg hc (Real.log_nonneg hu)
  have hsqrtu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  rw [blockSigma, Real.sqrt_div hA]
  rw [show c * u * Real.log u = u * (c * Real.log u) by ring, Real.sqrt_mul hu0.le]
  field_simp [ne_of_gt hsqrtu]
  rw [Real.sq_sqrt hA]

lemma blockSigma_cubic (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) :
    u * blockSigma c u ^ 3 = c * Real.log u * blockSigma c u := by
  calc
    u * blockSigma c u ^ 3 = (u * blockSigma c u ^ 2) * blockSigma c u := by ring
    _ = c * Real.log u * blockSigma c u := by rw [blockSigma_sq c u hc hu]

/-- Once `log u ≥ 1`, the reciprocal variable exponent costs at most a square-root of the block
coordinate.  This is the single `u^(1/2)` loss responsible for the threshold `c > 3`. -/
lemma blockSigma_inv_le_sqrt_div_sqrt (c u : ℝ) (hc : 0 < c) (hu : 1 ≤ u)
    (hlog : 1 ≤ Real.log u) :
    (blockSigma c u)⁻¹ ≤ Real.sqrt u / Real.sqrt c := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlog0 : 0 < Real.log u := zero_lt_one.trans_le hlog
  have hσ0 : 0 < blockSigma c u := by
    unfold blockSigma
    exact Real.sqrt_pos.mpr (div_pos (mul_pos hc hlog0) hu0)
  have hsqrtc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsqrtu0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hsqrt_le : Real.sqrt c ≤ blockSigma c u * Real.sqrt u := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hσ0.le (Real.sqrt_nonneg _))]
    rw [Real.sq_sqrt hc.le, mul_pow, Real.sq_sqrt hu0.le]
    have hsq := blockSigma_sq c u hc.le hu
    nlinarith [mul_le_mul_of_nonneg_left hlog hc.le]
  apply (le_div_iff₀ hsqrtc0).2
  calc
    (blockSigma c u)⁻¹ * Real.sqrt c = Real.sqrt c / blockSigma c u := by
      field_simp
    _ ≤ Real.sqrt u := (div_le_iff₀ hσ0).2 (by simpa [mul_comm] using hsqrt_le)

/-- The geometric shift sum with ratio `exp (-σ/2)` loses at most `4/σ` when `0 < σ ≤ 1`. -/
lemma one_sub_exp_neg_half_inv_le (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (1 - Real.exp (-σ / 2))⁻¹ ≤ 4 / σ := by
  let x : ℝ := σ / 2
  have hx0 : 0 < x := div_pos hσ0 (by norm_num)
  have hxhalf : x ≤ 1 / 2 := by dsimp [x]; linarith
  have hexplower : 1 / 2 ≤ Real.exp (-x) := by
    calc
      (1 / 2 : ℝ) ≤ 1 - x := by linarith
      _ ≤ Real.exp (-x) := by simpa using Real.one_sub_le_exp_neg x
  have hmul : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
    rw [add_mul, ← Real.exp_add] at h
    norm_num at h
    linarith
  have hlower : σ / 4 ≤ 1 - Real.exp (-σ / 2) := by
    rw [show -σ / 2 = -x by dsimp [x]; ring]
    calc
      σ / 4 = x * (1 / 2) := by dsimp [x]; ring
      _ ≤ x * Real.exp (-x) := mul_le_mul_of_nonneg_left hexplower hx0.le
      _ ≤ 1 - Real.exp (-x) := hmul
  have hquarter : 0 < σ / 4 := div_pos hσ0 (by norm_num)
  calc
    (1 - Real.exp (-σ / 2))⁻¹ = 1 / (1 - Real.exp (-σ / 2)) := by rw [one_div]
    _ ≤ 1 / (σ / 4) := one_div_le_one_div_of_le hquarter hlower
    _ = 4 / σ := by field_simp

lemma blockSigma_le_one (c u : ℝ) (hu : 1 ≤ u)
    (hbudget : c * Real.log u ≤ u) : blockSigma c u ≤ 1 := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  rw [blockSigma, Real.sqrt_le_one]
  exact (div_le_one hu0).mpr hbudget

/-- The per-block exponent bound after substituting `σ = sqrt(c log u / u)`.  Subsequent work only
has to make the cubic remainder small and choose `u` large enough that `σ ≤ 1`. -/
lemma chernoffExponent_blockSigma_le
    (c u : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) (hbudget : c * Real.log u ≤ u) :
    u * (Real.exp (blockSigma c u) - 1 - blockSigma c u) -
        blockSigma c u * Real.sqrt (c * u * Real.log u) ≤
      -(c / 2) * Real.log u + u * blockSigma c u ^ 3 := by
  exact chernoffExponent_le u c (blockSigma c u) (zero_le_one.trans hu) (Real.sqrt_nonneg _)
    (blockSigma_le_one c u hu hbudget) (blockSigma_sq c u hc hu)
    (blockSigma_mul_sqrt c u hc hu)

/-- Explicit slack form of the exponent estimate.  Once `blockSigma c u ≤ ρ`, any fixed
`ρ < 1/2` turns the cubic remainder into only a `ρ`-fraction of the main decay. -/
lemma chernoffExponent_blockSigma_le_slack
    (c u ρ : ℝ) (hc : 0 ≤ c) (hu : 1 ≤ u) (hρhalf : ρ < 1 / 2)
    (hσρ : blockSigma c u ≤ ρ) :
    u * (Real.exp (blockSigma c u) - 1 - blockSigma c u) -
        blockSigma c u * Real.sqrt (c * u * Real.log u) ≤
      -(1 / 2 - ρ) * c * Real.log u := by
  have hσ1 : blockSigma c u ≤ 1 := by linarith
  have hmain := chernoffExponent_le u c (blockSigma c u) (zero_le_one.trans hu)
    (Real.sqrt_nonneg _) hσ1 (blockSigma_sq c u hc hu)
    (blockSigma_mul_sqrt c u hc hu)
  have hclog : 0 ≤ c * Real.log u := mul_nonneg hc (Real.log_nonneg hu)
  have hcubic : u * blockSigma c u ^ 3 ≤ c * Real.log u * ρ := by
    rw [blockSigma_cubic c u hc hu]
    exact mul_le_mul_of_nonneg_left hσρ hclog
  calc
    u * (Real.exp (blockSigma c u) - 1 - blockSigma c u) -
        blockSigma c u * Real.sqrt (c * u * Real.log u) ≤
        -(c / 2) * Real.log u + u * blockSigma c u ^ 3 := hmain
    _ ≤ -(c / 2) * Real.log u + c * Real.log u * ρ := by
      simpa [add_comm] using add_le_add_left hcubic (-(c / 2) * Real.log u)
    _ = -(1 / 2 - ρ) * c * Real.log u := by ring

/-- The deterministic residual obtained by replacing every selector by its marginal mass. -/
noncomputable def marginalShiftResidual (b : ℕ) (delta : ℕ → ℝ)
    (M n : ℕ) : ℝ :=
  ∑' j : ℕ, (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1)

lemma summable_marginalShiftResidual_terms (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (M n : ℕ) :
    Summable (fun j : ℕ =>
      (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1)) := by
  let r : ℝ := 1 / (b : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    rw [div_lt_one (by positivity : (0 : ℝ) < b)]
    exact_mod_cast (show 1 < b by omega)
  have hgeom : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_norm_lt_one hr1
  have hjgeom : Summable (fun j : ℕ => (j : ℝ) * r ^ j) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr1)
  have hmajor : Summable (fun j : ℕ => r * ((n + 1 : ℝ) * r ^ j + (j : ℝ) * r ^ j)) :=
    ((hgeom.mul_left ((n : ℝ) + 1)).add hjgeom).mul_left r
  apply hmajor.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr0 _)
    (marginalDivisorMass_nonneg delta (fun m => (hdelta m).1) M _))]
  calc
    r ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) ≤
        r ^ (j + 1) * ((n + j + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
          ((marginalDivisorMass_le_card_divisors delta (fun m => (hdelta m).2) M _).trans
            (by exact_mod_cast Nat.card_divisors_le_self (n + j + 1)))
          (pow_nonneg hr0 _)
    _ = r * ((n + 1 : ℝ) * r ^ j + (j : ℝ) * r ^ j) := by
      push_cast
      rw [pow_succ]
      ring

lemma marginalShiftResidual_nonneg (b : ℕ) (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m) (M n : ℕ) :
    0 ≤ marginalShiftResidual b delta M n := by
  unfold marginalShiftResidual
  exact tsum_nonneg fun j => mul_nonneg (pow_nonneg (by positivity) _)
    (marginalDivisorMass_nonneg delta hdelta M _)

/-! ### Deterministic good/bad residual decomposition -/

/-- A summable majorant for the far shift tail, using only `delta m ≤ 1`. -/
noncomputable def residualTailMajorant (j : ℕ) : ℝ :=
  (j : ℝ) * (1 / 2 : ℝ) ^ j

lemma summable_residualTailMajorant : Summable residualTailMajorant := by
  unfold residualTailMajorant
  simpa using (summable_pow_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))

lemma marginalShiftResidual_tail_le
    (b : ℕ) (hb : 2 ≤ b) (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1)
    (M n J : ℕ) (hnJ : n < J) :
    (∑' k : ℕ, (1 / (b : ℝ)) ^ (k + J + 1) *
        marginalDivisorMass delta M (n + (k + J) + 1)) ≤
      ∑' k : ℕ, residualTailMajorant (k + J) := by
  have hbase : (1 / (b : ℝ)) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb)
  have hleft : Summable (fun k : ℕ =>
      (1 / (b : ℝ)) ^ (k + J + 1) *
        marginalDivisorMass delta M (n + (k + J) + 1)) := by
    have hs := summable_marginalShiftResidual_terms b hb delta hdelta M n
    exact hs.comp_injective (fun _ _ h => Nat.add_right_cancel
      (by simpa only [Nat.add_assoc] using h))
  have hright : Summable (fun k : ℕ => residualTailMajorant (k + J)) :=
    summable_residualTailMajorant.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  apply hleft.tsum_le_tsum _ hright
  intro k
  let j := k + J
  have hjJ : J ≤ j := by dsimp [j]; omega
  have hnj : n < j := hnJ.trans_le hjJ
  have hmass : marginalDivisorMass delta M (n + j + 1) ≤ (2 : ℝ) * j := by
    calc
      marginalDivisorMass delta M (n + j + 1) ≤
          (n + j + 1).divisors.card :=
        marginalDivisorMass_le_card_divisors delta (fun m => (hdelta m).2) M _
      _ ≤ n + j + 1 := by exact_mod_cast Nat.card_divisors_le_self (n + j + 1)
      _ ≤ (2 : ℝ) * j := by exact_mod_cast (show n + j + 1 ≤ 2 * j by omega)
  have hpow : (1 / (b : ℝ)) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) := by
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hmass0 : 0 ≤ marginalDivisorMass delta M (n + j + 1) :=
    marginalDivisorMass_nonneg delta (fun m => (hdelta m).1) M _
  change (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) ≤
    residualTailMajorant j
  calc
    (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) ≤
        (1 / 2 : ℝ) ^ (j + 1) * ((2 : ℝ) * j) :=
      mul_le_mul hpow hmass hmass0 (pow_nonneg (by norm_num) _)
    _ = residualTailMajorant j := by
      unfold residualTailMajorant
      rw [pow_succ]
      ring

/-- The geometric majorant when all first `J` marginal divisor masses are below their
`2^(j/2)` thresholds. -/
noncomputable def residualGoodMajorant (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (Real.rpow 2 (-1 / 2)) ^ j

lemma residualGoodMajorant_eq (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) * Real.rpow 2 ((j : ℝ) / 2) =
      residualGoodMajorant j := by
  have hhalf : (1 / 2 : ℝ) = Real.rpow 2 (-1 : ℝ) := by
    change (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ)
    rw [Real.rpow_neg_one]
    norm_num
  have hbase : (1 / 2 : ℝ) * Real.rpow 2 (1 / 2 : ℝ) =
      Real.rpow 2 (-1 / 2 : ℝ) := by
    calc
      (1 / 2 : ℝ) * Real.rpow 2 (1 / 2 : ℝ) =
          Real.rpow 2 (-1 : ℝ) * Real.rpow 2 (1 / 2 : ℝ) := by rw [hhalf]
      _ = Real.rpow 2 ((-1 : ℝ) + 1 / 2) := by
        change (2 : ℝ) ^ (-1 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) =
          (2 : ℝ) ^ ((-1 : ℝ) + 1 / 2)
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = _ := by congr 1; ring
  have hjpow : Real.rpow 2 ((j : ℝ) / 2) =
      (Real.rpow 2 (1 / 2 : ℝ)) ^ j := by
    calc
      Real.rpow 2 ((j : ℝ) / 2) = Real.rpow 2 ((1 / 2 : ℝ) * j) := by
        congr 1
        ring
      _ = _ := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (1 / 2 : ℝ) j
  unfold residualGoodMajorant
  rw [pow_succ, hjpow]
  calc
    (1 / 2 : ℝ) ^ j * (1 / 2) * (Real.rpow 2 (1 / 2 : ℝ)) ^ j =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ j * (Real.rpow 2 (1 / 2 : ℝ)) ^ j) := by ring
    _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) * Real.rpow 2 (1 / 2 : ℝ)) ^ j := by
      rw [mul_pow]
    _ = _ := by rw [hbase]

lemma summable_residualGoodMajorant : Summable residualGoodMajorant := by
  let r : ℝ := Real.rpow 2 (-1 / 2 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hs : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1)
  change Summable (fun j : ℕ => (1 / 2 : ℝ) * r ^ j)
  exact hs.mul_left _

lemma marginalShiftResidual_le_of_small
    (b : ℕ) (hb : 2 ≤ b) (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1)
    (M n J : ℕ) (hnJ : n < J) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ∀ j ∈ Finset.range J,
      marginalDivisorMass delta M (n + j + 1) ≤
        ε * Real.rpow 2 ((j : ℝ) / 2)) :
    marginalShiftResidual b delta M n ≤
      ε * ∑' j : ℕ, residualGoodMajorant j +
        ∑' k : ℕ, residualTailMajorant (k + J) := by
  let term : ℕ → ℝ := fun j =>
    (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1)
  have hsum : Summable term := summable_marginalShiftResidual_terms b hb delta hdelta M n
  have hbase : (1 / (b : ℝ)) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb)
  have hfinite : (∑ j ∈ Finset.range J, term j) ≤
      ε * ∑' j : ℕ, residualGoodMajorant j := by
    calc
      (∑ j ∈ Finset.range J, term j) ≤
          ∑ j ∈ Finset.range J, ε * residualGoodMajorant j := by
        apply Finset.sum_le_sum
        intro j hj
        have hpow : (1 / (b : ℝ)) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
          pow_le_pow_left₀ (by positivity) hbase _
        have hmass0 : 0 ≤ marginalDivisorMass delta M (n + j + 1) :=
          marginalDivisorMass_nonneg delta (fun m => (hdelta m).1) M _
        dsimp [term]
        calc
          (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) ≤
              (1 / 2 : ℝ) ^ (j + 1) *
                (ε * Real.rpow 2 ((j : ℝ) / 2)) :=
            mul_le_mul hpow (hsmall j hj) hmass0 (pow_nonneg (by norm_num) _)
          _ = ε * residualGoodMajorant j := by
            rw [← residualGoodMajorant_eq j]
            ring
      _ = ε * ∑ j ∈ Finset.range J, residualGoodMajorant j := by
        rw [Finset.mul_sum]
      _ ≤ ε * ∑' j : ℕ, residualGoodMajorant j := by
        exact mul_le_mul_of_nonneg_left
          (summable_residualGoodMajorant.sum_le_tsum (Finset.range J)
            (fun j _ => by
              unfold residualGoodMajorant
              exact mul_nonneg (by norm_num)
                (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _))) hε
  have htail := marginalShiftResidual_tail_le b hb delta hdelta M n J hnJ
  change (∑' j : ℕ, term j) ≤ _
  rw [← hsum.sum_add_tsum_nat_add J]
  exact add_le_add hfinite htail

lemma min_one_marginalShiftResidual_le_bad_sum
    (b : ℕ) (hb : 2 ≤ b) (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1)
    (M n J : ℕ) (hnJ : n < J) (ε : ℝ) (hε : 0 ≤ ε) :
    min 1 (marginalShiftResidual b delta M n) ≤
      ε * ∑' j : ℕ, residualGoodMajorant j +
        ∑' k : ℕ, residualTailMajorant (k + J) +
          ∑ j ∈ Finset.range J,
            if ε * Real.rpow 2 ((j : ℝ) / 2) <
                marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0 := by
  have hgood0 : 0 ≤ ε * ∑' j : ℕ, residualGoodMajorant j := by
    exact mul_nonneg hε (tsum_nonneg fun j => by
      unfold residualGoodMajorant
      exact mul_nonneg (by norm_num)
        (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _))
  have htail0 : 0 ≤ ∑' k : ℕ, residualTailMajorant (k + J) :=
    tsum_nonneg fun k => by unfold residualTailMajorant; positivity
  by_cases hsmall : ∀ j ∈ Finset.range J,
      marginalDivisorMass delta M (n + j + 1) ≤
        ε * Real.rpow 2 ((j : ℝ) / 2)
  · calc
      min 1 (marginalShiftResidual b delta M n) ≤
          marginalShiftResidual b delta M n := min_le_right _ _
      _ ≤ ε * ∑' j : ℕ, residualGoodMajorant j +
          ∑' k : ℕ, residualTailMajorant (k + J) :=
        marginalShiftResidual_le_of_small b hb delta hdelta M n J hnJ ε hε hsmall
      _ ≤ _ := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => by split <;> norm_num)
  · push_neg at hsmall
    obtain ⟨j, hj, hbad⟩ := hsmall
    have hind : (1 : ℝ) ≤ ∑ j ∈ Finset.range J,
        if ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0 := by
      calc
        (1 : ℝ) = if ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0 := by
          rw [if_pos hbad]
        _ ≤ ∑ k ∈ Finset.range J,
            if ε * Real.rpow 2 ((k : ℝ) / 2) <
                marginalDivisorMass delta M (n + k + 1) then (1 : ℝ) else 0 := by
          exact Finset.single_le_sum
            (f := fun k : ℕ => if ε * Real.rpow 2 ((k : ℝ) / 2) <
              marginalDivisorMass delta M (n + k + 1) then (1 : ℝ) else 0)
            (fun k _ => by split <;> norm_num) hj
    calc
      min 1 (marginalShiftResidual b delta M n) ≤ 1 := min_le_left _ _
      _ ≤ ε * ∑' j : ℕ, residualGoodMajorant j +
          ∑' k : ℕ, residualTailMajorant (k + J) +
            ∑ j ∈ Finset.range J,
              if ε * Real.rpow 2 ((j : ℝ) / 2) <
                  marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0 := by
        linarith

/-- Shifting `n` by `j+1` injects each bad set into the corresponding bad set on `[1,N+J]`. -/
lemma sum_shifted_marginal_bad_indicators_le
    (delta : ℕ → ℝ) (M : ℕ) (ε : ℝ) (N J : ℕ) :
    (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range J,
        if ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0) ≤
      ∑ j ∈ Finset.range J,
        (((Finset.Icc 1 (N + J)).filter (fun k =>
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta M k)).card : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  let B := (Finset.range N).filter (fun n =>
    ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M (n + j + 1))
  let A := (Finset.Icc 1 (N + J)).filter (fun k =>
    ε * Real.rpow 2 ((j : ℝ) / 2) < marginalDivisorMass delta M k)
  have hcard : B.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun n => n + j + 1)
    · intro n hn
      have hn' : n ∈ Finset.range N ∧
          ε * Real.rpow 2 ((j : ℝ) / 2) <
            marginalDivisorMass delta M (n + j + 1) := by
        simpa [B] using hn
      have hnN := Finset.mem_range.mp hn'.1
      have hjJ := Finset.mem_range.mp hj
      change n + j + 1 ∈ A
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hn'.2⟩
    · intro a ha d hd had
      change a + j + 1 = d + j + 1 at had
      omega
  have hsum : (∑ n ∈ Finset.range N,
      if ε * Real.rpow 2 ((j : ℝ) / 2) <
          marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0) = B.card := by
    simp [B]
  rw [hsum]
  exact_mod_cast hcard

lemma marginalDivisorMass_eq_zero_of_le
    (delta : ℕ → ℝ) (M n : ℕ) (hnM : n ≤ M) :
    marginalDivisorMass delta M n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [marginalDivisorMass]
  unfold marginalDivisorMass
  apply Finset.sum_eq_zero
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have hMd := (Finset.mem_filter.mp hd).2
  omega

/-- Cesàro average of the deterministic residual, capped at one. -/
noncomputable def cappedMarginalResidualAverage (b : ℕ) (delta : ℕ → ℝ)
    (M N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, min 1 (marginalShiftResidual b delta M n)) / N

/-- The deterministic bridge from uniform large-marginal-set counts to the capped residual
average.  The split at `J=N+K` makes the bad-set interval at most `3N` when `K≤N`; when `N<K`,
the hypothesis `3K≤M` kills every initial marginal divisor mass outright. -/
lemma cappedMarginalResidualAverage_le_of_large_cards
    (b : ℕ) (hb : 2 ≤ b) (delta : ℕ → ℝ)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1)
    (M K : ℕ) (hMK : 3 * K ≤ M) (ε ζ τ : ℝ)
    (hε : 0 ≤ ε) (hζ : 0 ≤ ζ)
    (hlarge : ∀ T J : ℕ,
      (∑ j ∈ Finset.range J,
          (((Finset.Icc 1 T).filter (fun n =>
            ε * Real.rpow 2 ((j : ℝ) / 2) <
              marginalDivisorMass delta M n)).card : ℝ)) ≤ ζ * T)
    (htail : ∀ J : ℕ, K ≤ J →
      (∑' k : ℕ, residualTailMajorant (k + J)) ≤ τ)
    (N : ℕ) (hN : 1 ≤ N) :
    cappedMarginalResidualAverage b delta M N ≤
      ε * ∑' j : ℕ, residualGoodMajorant j + τ + 3 * ζ := by
  let J := N + K
  let good : ℝ := ε * ∑' j : ℕ, residualGoodMajorant j
  let bad : ℕ → ℝ := fun n => ∑ j ∈ Finset.range J,
    if ε * Real.rpow 2 ((j : ℝ) / 2) <
        marginalDivisorMass delta M (n + j + 1) then (1 : ℝ) else 0
  have hJ : K ≤ J := by dsimp [J]; omega
  have hbad : (∑ n ∈ Finset.range N, bad n) ≤ 3 * ζ * N := by
    by_cases hKN : K ≤ N
    · calc
        (∑ n ∈ Finset.range N, bad n) ≤
            ∑ j ∈ Finset.range J,
              (((Finset.Icc 1 (N + J)).filter (fun k =>
                ε * Real.rpow 2 ((j : ℝ) / 2) <
                  marginalDivisorMass delta M k)).card : ℝ) := by
          exact sum_shifted_marginal_bad_indicators_le delta M ε N J
        _ ≤ ζ * (N + J) := by
          simpa only [Nat.cast_add] using hlarge (N + J) J
        _ ≤ ζ * (3 * N) := by
          apply mul_le_mul_of_nonneg_left _ hζ
          exact_mod_cast (show N + J ≤ 3 * N by dsimp [J]; omega)
        _ = 3 * ζ * N := by ring
    · have hNK : N < K := by omega
      have hzero : (∑ n ∈ Finset.range N, bad n) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        unfold bad
        apply Finset.sum_eq_zero
        intro j hj
        rw [if_neg]
        rw [marginalDivisorMass_eq_zero_of_le delta M (n + j + 1) (by
          have hnN := Finset.mem_range.mp hn
          have hjJ := Finset.mem_range.mp hj
          dsimp [J] at hjJ
          omega)]
        exact not_lt_of_ge (mul_nonneg hε (Real.rpow_nonneg (by norm_num) _))
      rw [hzero]
      positivity
  have hpoint : ∀ n ∈ Finset.range N,
      min 1 (marginalShiftResidual b delta M n) ≤ good + τ + bad n := by
    intro n hn
    have hnN := Finset.mem_range.mp hn
    have hnJ : n < J := hnN.trans_le (by dsimp [J]; omega)
    have hraw := min_one_marginalShiftResidual_le_bad_sum
      b hb delta hdelta M n J hnJ ε hε
    have ht := htail J hJ
    dsimp [good, bad]
    exact hraw.trans (add_le_add (add_le_add le_rfl ht) le_rfl)
  unfold cappedMarginalResidualAverage
  have hsum : (∑ n ∈ Finset.range N,
      min 1 (marginalShiftResidual b delta M n)) ≤
      N * (good + τ + 3 * ζ) := by
    calc
      (∑ n ∈ Finset.range N,
          min 1 (marginalShiftResidual b delta M n)) ≤
          ∑ n ∈ Finset.range N, (good + τ + bad n) :=
        Finset.sum_le_sum hpoint
      _ = N * (good + τ) + ∑ n ∈ Finset.range N, bad n := by
        simp [Finset.sum_add_distrib]
        ring
      _ ≤ N * (good + τ) + 3 * ζ * N := add_le_add le_rfl hbad
      _ = N * (good + τ + 3 * ζ) := by ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNr).2
  calc
    (∑ n ∈ Finset.range N, min 1 (marginalShiftResidual b delta M n)) ≤
        N * (good + τ + 3 * ζ) := hsum
    _ = (ε * ∑' j : ℕ, residualGoodMajorant j + τ + 3 * ζ) * N := by
      dsimp [good]
      ring

/-- Cesàro average of the random residual, capped at one. -/
noncomputable def cappedShiftResidualAverage {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) : ℝ :=
  (∑ n ∈ Finset.range N, min 1 (shiftResidual b X M n w)) / N

lemma cappedShiftResidualAverage_nonneg {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) :
    0 ≤ cappedShiftResidualAverage b X M N w := by
  unfold cappedShiftResidualAverage
  exact div_nonneg (Finset.sum_nonneg fun n _ =>
    le_min zero_le_one (shiftResidual_nonneg b X M n w)) (by positivity)

lemma measurable_cappedShiftResidualAverage {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (M N : ℕ) :
    Measurable (cappedShiftResidualAverage b X M N) := by
  unfold cappedShiftResidualAverage
  exact (Finset.measurable_sum _ fun n _ =>
    measurable_const.min (measurable_shiftResidual b X hX M n)).div_const _

/-- Finite approximation to the capped random residual average. -/
noncomputable def cappedShiftResidualPartialAverage {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N J : ℕ) (w : Ω) : ℝ :=
  (∑ n ∈ Finset.range N, min 1 (shiftResidualPartial b X M n J w)) / N

lemma cappedShiftResidualPartialAverage_nonneg {Ω : Type*} (b : ℕ)
    (X : ℕ → Ω → Bool) (M N J : ℕ) (w : Ω) :
    0 ≤ cappedShiftResidualPartialAverage b X M N J w := by
  unfold cappedShiftResidualPartialAverage
  exact div_nonneg (Finset.sum_nonneg fun n _ =>
    le_min zero_le_one (shiftResidualPartial_nonneg b X M n J w)) (by positivity)

lemma measurable_cappedShiftResidualPartialAverage {Ω : Type*} [MeasurableSpace Ω]
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m)) (M N J : ℕ) :
    Measurable (cappedShiftResidualPartialAverage b X M N J) := by
  unfold cappedShiftResidualPartialAverage
  exact (Finset.measurable_sum _ fun n _ =>
    measurable_const.min (measurable_shiftResidualPartial b X hX M n J)).div_const _

lemma integrable_shiftResidualPartial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : ℕ) (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n J : ℕ) :
    Integrable (shiftResidualPartial b X M n J) μ := by
  simpa using integrable_shiftResidualPartial_rpow μ b X hX M n J 1 zero_lt_one

lemma integrable_min_one_shiftResidualPartial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : ℕ) (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M n J : ℕ) :
    Integrable (fun w => min 1 (shiftResidualPartial b X M n J w)) μ := by
  apply Integrable.of_bound
    (measurable_const.min (measurable_shiftResidualPartial b X hX M n J)).aestronglyMeasurable 1
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg
    (le_min zero_le_one (shiftResidualPartial_nonneg b X M n J w))]
  exact min_le_left _ _

lemma integrable_cappedShiftResidualPartialAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : ℕ) (X : ℕ → Ω → Bool)
    (hX : ∀ m, Measurable (X m)) (M N J : ℕ) :
    Integrable (cappedShiftResidualPartialAverage b X M N J) μ := by
  unfold cappedShiftResidualPartialAverage
  exact (integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_min_one_shiftResidualPartial μ b X hX M n J).div_const _

lemma integral_selectedDivisorCount_eq_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)) (M n : ℕ) :
    (∫ w, selectedDivisorCount X M n w ∂μ) = marginalDivisorMass delta M n := by
  rw [integral_selectedDivisorCount μ X hX M n]
  unfold marginalDivisorMass
  apply Finset.sum_congr rfl
  intro m hm
  rw [Measure.real, hLaw m, ENNReal.toReal_ofReal (hdelta m)]

lemma integral_shiftResidualPartial_eq_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (delta : ℕ → ℝ)
    (X : ℕ → Ω → Bool) (hdelta : ∀ m, 0 ≤ delta m)
    (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)) (M n J : ℕ) :
    (∫ w, shiftResidualPartial b X M n J w ∂μ) =
      ∑ j ∈ Finset.range J,
        (1 / (b : ℝ)) ^ (j + 1) * marginalDivisorMass delta M (n + j + 1) := by
  unfold shiftResidualPartial
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, integral_selectedDivisorCount_eq_marginal μ delta X hdelta hX hLaw]
  · intro j hj
    exact (integrable_selectedDivisorCount μ X hX M (n + j + 1)).const_mul _

lemma integral_min_one_shiftResidualPartial_le_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m)) (M n J : ℕ) :
    (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤
      min 1 (marginalShiftResidual b delta M n) := by
  have hInt := integrable_shiftResidualPartial μ b X hX M n J
  have hminInt := integrable_min_one_shiftResidualPartial μ b X hX M n J
  have hleOne : (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤ 1 := by
    calc
      (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤
          ∫ _w, (1 : ℝ) ∂μ :=
        integral_mono hminInt (integrable_const _) (fun w => min_le_left _ _)
      _ = 1 := by simp
  have hlePartial : (∫ w, min 1 (shiftResidualPartial b X M n J w) ∂μ) ≤
      ∫ w, shiftResidualPartial b X M n J w ∂μ :=
    integral_mono hminInt hInt (fun w => min_le_right _ _)
  have hpartial : (∫ w, shiftResidualPartial b X M n J w ∂μ) ≤
      marginalShiftResidual b delta M n := by
    rw [integral_shiftResidualPartial_eq_marginal μ b delta X (fun m => (hdelta m).1)
      hX hLaw]
    unfold marginalShiftResidual
    exact (summable_marginalShiftResidual_terms b hb delta hdelta M n).sum_le_tsum
      (Finset.range J) (fun j hj => mul_nonneg (pow_nonneg (by positivity) _)
        (marginalDivisorMass_nonneg delta (fun m => (hdelta m).1) M _))
  exact le_min hleOne (hlePartial.trans hpartial)

lemma integral_cappedShiftResidualPartialAverage_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m))
    (M N J : ℕ) :
    (∫ w, cappedShiftResidualPartialAverage b X M N J w ∂μ) ≤
      cappedMarginalResidualAverage b delta M N := by
  unfold cappedShiftResidualPartialAverage cappedMarginalResidualAverage
  rw [integral_div]
  rw [integral_finsetSum]
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun n hn =>
        integral_min_one_shiftResidualPartial_le_marginal μ b hb delta X hdelta hX hLaw M n J)
      (by positivity)
  · intro n hn
    exact integrable_min_one_shiftResidualPartial μ b X hX M n J

lemma tendsto_cappedShiftResidualPartialAverage {Ω : Type*}
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) :
    Tendsto (fun J => cappedShiftResidualPartialAverage b X M N J w) atTop
      (nhds (cappedShiftResidualAverage b X M N w)) := by
  unfold cappedShiftResidualPartialAverage cappedShiftResidualAverage
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro n hn
  exact tendsto_const_nhds.min (tendsto_shiftResidualPartial b hb X M n w)

/-- The expected capped residual average is bounded by its deterministic marginal counterpart. -/
lemma lintegral_cappedShiftResidualAverage_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : ℕ) (hb : 2 ≤ b)
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool)
    (hdelta : ∀ m, 0 ≤ delta m ∧ delta m ≤ 1) (hX : ∀ m, Measurable (X m))
    (hLaw : ∀ m, μ {w | X m w = true} = ENNReal.ofReal (delta m))
    (M N : ℕ) :
    (∫⁻ w, ENNReal.ofReal (cappedShiftResidualAverage b X M N w) ∂μ) ≤
      ENNReal.ofReal (cappedMarginalResidualAverage b delta M N) := by
  let f : ℕ → Ω → ENNReal := fun J w =>
    ENNReal.ofReal (cappedShiftResidualPartialAverage b X M N J w)
  let F : Ω → ENNReal := fun w =>
    ENNReal.ofReal (cappedShiftResidualAverage b X M N w)
  have hfMeas : ∀ J, Measurable (f J) := fun J =>
    (measurable_cappedShiftResidualPartialAverage b X hX M N J).ennreal_ofReal
  have hlim : ∀ w, Tendsto (fun J => f J w) atTop (nhds (F w)) := by
    intro w
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_cappedShiftResidualPartialAverage b hb X M N w)
  have hpartial : ∀ J, (∫⁻ w, f J w ∂μ) ≤
      ENNReal.ofReal (cappedMarginalResidualAverage b delta M N) := by
    intro J
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_cappedShiftResidualPartialAverage μ b X hX M N J)
      (Eventually.of_forall fun w => cappedShiftResidualPartialAverage_nonneg b X M N J w)]
    exact ENNReal.ofReal_le_ofReal
      (integral_cappedShiftResidualPartialAverage_le μ b hb delta X hdelta hX hLaw M N J)
  have hfatou := lintegral_liminf_le hfMeas (μ := μ) (u := atTop)
  have hpoint : (fun w => liminf (fun J => f J w) atTop) = F := by
    funext w
    exact (hlim w).liminf_eq
  rw [hpoint] at hfatou
  exact hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hpartial))

lemma orbitAverage_le_cappedShiftResidualAverage {Ω : Type*}
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (M N : ℕ) (w : Ω) :
    (∑ n ∈ Finset.range N, NormalNumbers.orbit b (ebLambertTail b X M w) n) / N ≤
      cappedShiftResidualAverage b X M N w := by
  unfold cappedShiftResidualAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro n hn
  have hfract : NormalNumbers.orbit b (ebLambertTail b X M w) n ≤
      shiftResidual b X M n w := by
    simpa only [NormalNumbers.orbit, mul_comm] using
      fract_pow_mul_ebLambertTail_le_shiftResidual b hb X M n w
  exact le_min (Int.fract_lt_one _).le hfract

/-- A normal deleted-head orbit forces a positive capped residual average. -/
lemma isNormal_eventually_cappedShiftResidualAverage_ge {Ω : Type*}
    (b : ℕ) (hb : 2 ≤ b) (X : ℕ → Ω → Bool) (M : ℕ) (w : Ω)
    (hnormal : NormalNumbers.IsNormal b (ebLambertTail b X M w)) :
    ∀ᶠ N : ℕ in atTop,
      normalMomentThreshold 1 ≤ cappedShiftResidualAverage b X M N w := by
  let u : ℕ → ℝ := NormalNumbers.orbit b (ebLambertTail b X M w)
  have hequid : NormalNumbers.Equidistributed u := by
    exact (NormalNumbers.isNormal_iff_equidistributed_orbit b hb _).mp hnormal
  have htend : Tendsto
      (fun N => (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) / N)
      atTop (nhds (1 / 2 : ℝ)) := by
    have h := hequid (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hvisit : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) ≤ (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) / N :=
    (htend.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))).mono
      fun N hN => hN.le
  filter_upwards [hvisit, eventually_ge_atTop 1] with N hfreq hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlower : (1 / 2 : ℝ) * (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) ≤
      ∑ n ∈ Finset.range N, u n := by
    calc
      (1 / 2 : ℝ) * (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) =
          ∑ n ∈ (Finset.range N).filter (fun n => u n ∈ Set.Ico (1 / 2) 1), (1 / 2 : ℝ) := by
        unfold NormalNumbers.visitCount
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ n ∈ (Finset.range N).filter (fun n => u n ∈ Set.Ico (1 / 2) 1), u n := by
        apply Finset.sum_le_sum
        intro n hn
        exact (Finset.mem_filter.mp hn).2.1
      _ ≤ ∑ n ∈ Finset.range N, u n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n hn hnot
        exact Int.fract_nonneg _
  calc
    normalMomentThreshold 1 = (1 / 2 : ℝ) * (1 / 4) := by
      norm_num [normalMomentThreshold]
    _ ≤ (1 / 2 : ℝ) *
        ((NormalNumbers.visitCount u (1 / 2) 1 N : ℝ) / N) :=
      mul_le_mul_of_nonneg_left hfreq (by norm_num)
    _ = ((1 / 2 : ℝ) * (NormalNumbers.visitCount u (1 / 2) 1 N : ℝ)) / N := by ring
    _ ≤ (∑ n ∈ Finset.range N, u n) / N :=
      div_le_div_of_nonneg_right hlower hNpos.le
    _ ≤ cappedShiftResidualAverage b X M N w := by
      exact orbitAverage_le_cappedShiftResidualAverage b hb X M N w

/-- Uniform expectation control bounds the measure of the eventual positive capped-residual event. -/
lemma measure_eventually_cappedShiftResidualAverage_ge_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (b : ℕ) (X : ℕ → Ω → Bool) (hX : ∀ m, Measurable (X m))
    (M : ℕ) (ε R : ℝ) (hε : 0 < ε)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      (∫⁻ w, ENNReal.ofReal (cappedShiftResidualAverage b X M N w) ∂μ) ≤
        ENNReal.ofReal R) :
    μ {w | ∀ᶠ N : ℕ in atTop,
      ε ≤ cappedShiftResidualAverage b X M N w} ≤ ENNReal.ofReal (R / ε) := by
  let E : ℕ → Set Ω := fun N => {w | ε ≤ cappedShiftResidualAverage b X M N w}
  let T : ℕ → Set Ω := fun K => {w | ∀ N, K ≤ N → w ∈ E N}
  have hE : ∀ N : ℕ, 1 ≤ N → μ (E N) ≤ ENNReal.ofReal (R / ε) := by
    intro N hN
    have hset : {w | ENNReal.ofReal ε ≤
        ENNReal.ofReal (cappedShiftResidualAverage b X M N w)} = E N := by
      ext w
      simp only [E, Set.mem_setOf_eq]
      exact ENNReal.ofReal_le_ofReal_iff (cappedShiftResidualAverage_nonneg b X M N w)
    have hmarkov := mul_meas_ge_le_lintegral
      ((measurable_cappedShiftResidualAverage b X hX M N).ennreal_ofReal)
      (ENNReal.ofReal ε) (μ := μ)
    rw [hset] at hmarkov
    rw [ENNReal.ofReal_div_of_pos hε]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hε)))
      (Or.inl ENNReal.ofReal_ne_top)).2
    rw [mul_comm]
    exact hmarkov.trans (hbound N hN)
  have hTmono : Monotone T := by
    intro K L hKL w hw N hLN
    exact hw N (hKL.trans hLN)
  have hT : ∀ K, μ (T K) ≤ ENNReal.ofReal (R / ε) := by
    intro K
    calc
      μ (T K) ≤ μ (E (max K 1)) := by
        apply measure_mono
        intro w hw
        exact hw (max K 1) (le_max_left K 1)
      _ ≤ ENNReal.ofReal (R / ε) := hE (max K 1) (le_max_right K 1)
  have hunion : μ (⋃ K, T K) ≤ ENNReal.ofReal (R / ε) := by
    rw [hTmono.measure_iUnion]
    exact iSup_le hT
  have heq : {w | ∀ᶠ N : ℕ in atTop,
      ε ≤ cappedShiftResidualAverage b X M N w} = ⋃ K, T K := by
    ext w
    constructor
    · intro hw
      obtain ⟨K, hK⟩ := eventually_atTop.1 hw
      exact Set.mem_iUnion.2 ⟨K, hK⟩
    · intro hw
      obtain ⟨K, hK⟩ := Set.mem_iUnion.1 hw
      exact eventually_atTop.2 ⟨K, hK⟩
  rw [heq]
  exact hunion

/-- Marginal-only capped-residual criterion for random Erdős--Borwein non-normality. -/
theorem ae_not_normal_of_capped_marginal_residual
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (htail : ∀ b : ℕ, 2 ≤ b → ∀ η : ℝ, 0 < η →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, 1 ≤ N →
        cappedMarginalResidualAverage b delta M N ≤ η) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
  classical
  obtain ⟨hdelta, hMeas, -, hLaw⟩ := hX
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · have hbase : ∀ᵐ w ∂μ, ¬ NormalNumbers.IsNormal b (ebLambert b X w) := by
      rw [ae_iff]
      simp only [not_not]
      let A : Set Ω := {w | NormalNumbers.IsNormal b (ebLambert b X w)}
      change μ A = 0
      by_contra hA0
      have hAtop : μ A ≠ ⊤ := measure_ne_top μ A
      let p : ℝ := (μ A).toReal
      have hp : 0 < p := ENNReal.toReal_pos hA0 hAtop
      let ε : ℝ := normalMomentThreshold 1
      have hε : 0 < ε := normalMomentThreshold_pos 1
      let η : ℝ := p * ε / 2
      have hη : 0 < η := by dsimp [η]; positivity
      obtain ⟨M, hM, htailM⟩ := htail b hb η hη
      have hlintegral : ∀ N : ℕ, 1 ≤ N →
          (∫⁻ w, ENNReal.ofReal (cappedShiftResidualAverage b X M N w) ∂μ) ≤
            ENNReal.ofReal η := by
        intro N hN
        exact (lintegral_cappedShiftResidualAverage_le μ b hb delta X hdelta hMeas hLaw M N).trans
          (ENNReal.ofReal_le_ofReal (htailM N hN))
      let E : Set Ω := {w | ∀ᶠ N : ℕ in atTop,
        ε ≤ cappedShiftResidualAverage b X M N w}
      have hE : μ E ≤ ENNReal.ofReal (η / ε) := by
        exact measure_eventually_cappedShiftResidualAverage_ge_le μ b X hMeas M ε η hε
          hlintegral
      have hsub : A ⊆ E := by
        intro w hw
        have hnormal := ebLambertTail_isNormal_of_ebLambert b hb X M w hw
        exact isNormal_eventually_cappedShiftResidualAverage_ge b hb X M w hnormal
      have hmeasure : μ A ≤ ENNReal.ofReal (η / ε) := (measure_mono hsub).trans hE
      have hp_le : p ≤ η / ε := by
        dsimp [p]
        exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hη.le hε.le) hmeasure
      have hhalf : η / ε = p / 2 := by
        dsimp [η]
        field_simp
      rw [hhalf] at hp_le
      linarith
    filter_upwards [hbase] with w hw
    exact fun _ => hw
  · exact ae_of_all μ fun w hb' => (hb hb').elim

end NormalNumbers.ErdosBorweinSubpower
