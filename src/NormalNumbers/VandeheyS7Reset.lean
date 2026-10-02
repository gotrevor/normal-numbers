/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-RS: `ClockLinear` is a THEOREM — reset counting kills Vandehey's Lemma 6.1 as a hypothesis

S7-GR made the stall clock affine in the slack.  This module supplies the other half: a bound on
how many times can have a *small* stall clock.

Each emission opens at most `K` times of age `< K`, so the map

    n ↦ (n − stallAge n, stallAge n)

is injective (the two coordinates reconstruct `n`) into (resets) × (range K), and the resets up to
`q` number at most `runClock q + 1` (`card_smallAge_le`).  Hence

    q  ≤  K·(runClock q + 1)  +  (1/K)·Σ_{n<q} stallAge n            (`card_range_le`)

and if the mean stall age is at most `C`, taking `K` with `C/K ≤ 1/2` gives
`runClock q ≥ q/(2K) − 1` (`clockLinear_of_meanStallAge`).  Composing with S7-GR:

    **`clockLinear_of_meanSlack` : MeanSlack ⟹ ClockLinear.**

So the §7 front (S7-FT) has TWO hypotheses, not three: `ClassFreqBound` and `MeanSlack`.
Vandehey's Lemma 6.1 — the linear growth of the output length — is not an extra input; it is
implied by positive recurrence of the height walk.
-/
import NormalNumbers.VandeheyS7Growth

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

variable {Φ : MapState} {x : ℝ}

/-- The clock counts the emitting steps. -/
lemma runClock_eq_card (Φ : MapState) (x : ℝ) (q : ℕ) :
    runClock Φ x q = ((range q).filter (fun m => runWord Φ x m ≠ [])).card := by
  classical
  induction q with
  | zero => simp [runClock]
  | succ q ih =>
    rw [runClock_succ, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : runWord Φ x q ≠ []
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      have hlen : (runWord Φ x q).length = 1 := by
        have h1 := runWord_length_le_one Φ x q
        have h2 : (runWord Φ x q).length ≠ 0 := by
          simpa [List.length_eq_zero_iff] using h
        omega
      omega
    · rw [if_neg h]
      have : (runWord Φ x q).length = 0 := by
        simp [List.length_eq_zero_iff, not_not.mp h]
      omega

/-- The stall clock resets exactly at emissions. -/
lemma stallAge_eq_zero_succ {Φ : MapState} {x : ℝ} {m : ℕ} (h : stallAge Φ x (m + 1) = 0) :
    runWord Φ x m ≠ [] := by
  rw [stallAge_succ] at h
  by_cases hw : runWord Φ x m = []
  · rw [if_pos hw] at h; omega
  · exact hw

/-- **The reset time has zero age.** -/
theorem stallAge_sub_self (Φ : MapState) (x : ℝ) :
    ∀ n, stallAge Φ x (n - stallAge Φ x n) = 0 := by
  intro n
  induction n with
  | zero => simp [stallAge]
  | succ n ih =>
    by_cases hw : runWord Φ x n = []
    · have hage : stallAge Φ x (n + 1) = stallAge Φ x n + 1 := by
        rw [stallAge_succ, if_pos hw]
      have hle : stallAge Φ x n ≤ n := stallAge_le_self Φ x n
      have : n + 1 - stallAge Φ x (n + 1) = n - stallAge Φ x n := by omega
      rw [this]; exact ih
    · have hage : stallAge Φ x (n + 1) = 0 := by rw [stallAge_succ, if_neg hw]
      rw [hage]; simpa using hage

/-! ## The counting -/

open Classical in
/-- **Reset counting.**  Times of small stall clock are few. -/
theorem card_smallAge_le (Φ : MapState) (x : ℝ) (q K : ℕ) :
    ((range q).filter (fun n => stallAge Φ x n < K)).card ≤ (runClock Φ x q + 1) * K := by
  classical
  set R : Finset ℕ :=
    insert 0 (((range q).filter (fun m => runWord Φ x m ≠ [])).image (· + 1)) with hR
  have hRcard : R.card ≤ runClock Φ x q + 1 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := Finset.card_image_le (s := (range q).filter (fun m => runWord Φ x m ≠ []))
      (f := (· + 1 : ℕ → ℕ))
    rw [runClock_eq_card]
    omega
  have hmaps : ∀ n ∈ (range q).filter (fun n => stallAge Φ x n < K),
      (n - stallAge Φ x n, stallAge Φ x n) ∈ R ×ˢ range K := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_range.mpr hn.2⟩
    set r := n - stallAge Φ x n with hr
    have hzero : stallAge Φ x r = 0 := stallAge_sub_self Φ x n
    have hrle : r ≤ n := by omega
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [hR, h0]; exact Finset.mem_insert_self _ _
    · obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hzero' : stallAge Φ x (m + 1) = 0 := by rw [← hm]; exact hzero
      have hne := stallAge_eq_zero_succ hzero'
      rw [hm]
      refine Finset.mem_insert_of_mem ?_
      refine Finset.mem_image.mpr ⟨m, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne⟩
  have hinj : ∀ n ∈ (range q).filter (fun n => stallAge Φ x n < K),
      ∀ m ∈ (range q).filter (fun n => stallAge Φ x n < K),
      (n - stallAge Φ x n, stallAge Φ x n) = (m - stallAge Φ x m, stallAge Φ x m) → n = m := by
    intro n _ m _ heq
    have h1 : n - stallAge Φ x n = m - stallAge Φ x m := congrArg Prod.fst heq
    have h2 : stallAge Φ x n = stallAge Φ x m := congrArg Prod.snd heq
    have hn := stallAge_le_self Φ x n
    have hm := stallAge_le_self Φ x m
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  calc ((range q).filter (fun n => stallAge Φ x n < K)).card
      ≤ (R ×ˢ range K).card := hcard
    _ = R.card * K := by rw [Finset.card_product, Finset.card_range]
    _ ≤ (runClock Φ x q + 1) * K := Nat.mul_le_mul_right _ hRcard

open Classical in
/-- **The counting inequality.** -/
theorem card_range_le (Φ : MapState) (x : ℝ) (q : ℕ) {K : ℕ} (hK : 0 < K) :
    (q : ℝ) ≤ (K : ℝ) * ((runClock Φ x q : ℕ) + 1) +
      (1 / (K : ℝ)) * ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ) := by
  classical
  set S := (range q).filter (fun n => stallAge Φ x n < K) with hS
  set Sc := (range q).filter (fun n => ¬ stallAge Φ x n < K) with hSc
  have hKR : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsplit : S.card + Sc.card = q := by
    rw [hS, hSc, Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hbig : (K : ℝ) * (Sc.card : ℝ) ≤ ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ) := by
    have h1 : (K : ℝ) * (Sc.card : ℝ) ≤ ∑ n ∈ Sc, ((stallAge Φ x n : ℕ) : ℝ) := by
      have hc : ∑ _n ∈ Sc, (K : ℝ) = (K : ℝ) * (Sc.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      rw [← hc]
      refine Finset.sum_le_sum fun n hn => ?_
      have := (Finset.mem_filter.mp (hSc ▸ hn)).2
      exact_mod_cast Nat.le_of_not_lt this
    refine le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    intro n _ _; exact Nat.cast_nonneg _
  have hsmall : (S.card : ℝ) ≤ (K : ℝ) * ((runClock Φ x q : ℕ) + 1) := by
    have h := card_smallAge_le Φ x q K
    have : (S.card : ℝ) ≤ ((runClock Φ x q + 1) * K : ℕ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hq : (q : ℝ) = (S.card : ℝ) + (Sc.card : ℝ) := by exact_mod_cast hsplit.symm
  have hScb : (Sc.card : ℝ) ≤ (1 / (K:ℝ)) * ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hKR]
    linarith [hbig]
  linarith

/-! ## `ClockLinear` -/

/-- **S7-RS.**  A bounded mean stall age forces a linear clock. -/
theorem clockLinear_of_meanStallAge (Φ : MapState) (x : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ q in atTop, ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ) ≤ C * q) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ q in atTop, c * q ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 0 < K ∧ C / K ≤ 1 / 2 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * C + 1)
    have hKposR : (0:ℝ) < (K:ℝ) := by linarith
    have hKpos : 0 < K := by exact_mod_cast hKposR
    refine ⟨K, hKpos, ?_⟩
    rw [div_le_div_iff₀ hKposR (by norm_num)]
    linarith
  obtain ⟨hKpos, hKC⟩ := hK
  have hKR : (0:ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  refine ⟨1 / (4 * K), by positivity, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (4 * K)] with q hm hq
  have hqR : (4 * K : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbase := card_range_le Φ x q hKpos
  have h2 : (1 / (K:ℝ)) * ∑ n ∈ range q, ((stallAge Φ x n : ℕ) : ℝ) ≤ (1/(K:ℝ)) * (C * q) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have h3 : (1/(K:ℝ)) * (C * q) ≤ (1/2) * q := by
    have : (1/(K:ℝ)) * (C * q) = (C / K) * q := by ring
    rw [this]
    have hqnn : (0:ℝ) ≤ (q:ℝ) := by positivity
    nlinarith [hKC, hqnn]
  have hhalf : (q : ℝ) / 2 ≤ (K : ℝ) * ((runClock Φ x q : ℕ) + 1) := by linarith
  have hmono : ((runClock Φ x q : ℕ) : ℝ) ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) := by
    exact_mod_cast runClock_mono Φ x (by omega : q ≤ q + 2)
  have hq1 : (1:ℝ) ≤ (q:ℝ) / (4 * K) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hfin : (q:ℝ) / (4 * K) ≤ ((runClock Φ x q : ℕ) : ℝ) := by
    have hKq : (q:ℝ) / (2 * K) - 1 ≤ ((runClock Φ x q : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
      nlinarith [hhalf]
    have : (q:ℝ) / (4 * K) ≤ (q:ℝ) / (2 * K) - 1 := by
      have h4 : (q:ℝ) / (2 * K) = 2 * ((q:ℝ) / (4 * K)) := by field_simp; ring
      rw [h4]; linarith
    linarith
  calc (1 / (4 * (K:ℝ))) * q = (q:ℝ) / (4 * K) := by ring
    _ ≤ ((runClock Φ x q : ℕ) : ℝ) := hfin
    _ ≤ ((runClock Φ x (q + 2) : ℕ) : ℝ) := hmono

end MapState

section Audit

#print axioms MapState.runClock_eq_card
#print axioms MapState.stallAge_sub_self
#print axioms MapState.card_smallAge_le
#print axioms MapState.card_range_le
#print axioms MapState.clockLinear_of_meanStallAge

end Audit

end NormalNumbers.VandeheyS7
