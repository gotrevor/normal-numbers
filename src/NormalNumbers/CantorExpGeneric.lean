/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouvilleAll

/-!
# Generic estimates for the coin points `pt free ω`

Infrastructure for `CantorExactExponent`, stated for an arbitrary free-position predicate
`free`: the head/tail split of `pt free ω`, separation of cylinders, the Frostman ball bound,
the trivial count of numerators near the support, and the zero-window mass.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorExpGeneric

open CantorLiouville Derandomize

instance : IsProbabilityMeasure coins := by unfold coins; infer_instance

/-! ## Head and tail -/

/-- Integer numerator of the depth-`n` head: `Σ_{i<n} d_i 3^{n-1-i}`. -/
def hd (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, ptDigit free ω i * 3 ^ (n - 1 - i)

theorem ptDigit_le_two (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ptDigit free ω i ≤ 2 := by
  unfold ptDigit; split_ifs <;> norm_num

theorem ptDigit_eq_zero_or (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) :
    ptDigit free ω i = 0 ∨ ptDigit free ω i = 2 := by
  unfold ptDigit; split_ifs <;> simp

theorem ptDigit_eq_zero_iff (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) :
    ptDigit free ω i = 0 ↔ ¬ (free i = true ∧ ω i = true) := by
  unfold ptDigit; split_ifs with h <;> simp_all

theorem hd_succ (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    hd free ω (n + 1) = 3 * hd free ω n + ptDigit free ω n := by
  unfold hd
  rw [Finset.sum_range_succ, Finset.mul_sum, show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, pow_succ]; ring

theorem hd_congr (free : ℕ → Bool) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : ∀ j < n, ptDigit free ω j = ptDigit free ω' j) : hd free ω n = hd free ω' n := by
  unfold hd
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem hd_lt (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : hd free ω n < 3 ^ n := by
  induction n with
  | zero => simp [hd]
  | succ n ih =>
    rw [hd_succ, pow_succ]
    have := ptDigit_le_two free ω n
    omega

theorem head_eq (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    ((hd free ω n : ℕ) : ℝ) / 3 ^ n = ∑ i ∈ Finset.range n, (ptDigit free ω i : ℝ) / 3 ^ (i + 1) := by
  unfold hd
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
    show n - 1 - i + (i + 1) = n by omega]

/-- The tail beyond depth `n`. -/
noncomputable def tl (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑' k, (ptDigit free ω (k + n) : ℝ) / (3 : ℝ) ^ (k + n + 1)

theorem pt_split (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    pt free ω = (hd free ω n : ℝ) / 3 ^ n + tl free ω n := by
  rw [head_eq, pt, realOfDigits, tl]
  simp only [Nat.cast_ofNat]
  exact ((summable_ptDigit free ω).sum_add_tsum_nat_add n).symm

theorem summable_tl (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    Summable fun k => (ptDigit free ω (k + n) : ℝ) / (3 : ℝ) ^ (k + n + 1) :=
  (summable_ptDigit free ω).comp_injective (add_left_injective n)

theorem tl_nonneg (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : 0 ≤ tl free ω n :=
  tsum_nonneg fun k => by positivity

theorem tsum_two_geom (n : ℕ) :
    Summable (fun k : ℕ => (2 : ℝ) / 3 ^ (k + n + 1)) ∧
      ∑' k : ℕ, (2 : ℝ) / 3 ^ (k + n + 1) = 1 / 3 ^ n := by
  have hterm : (fun k : ℕ => (2 : ℝ) / 3 ^ (k + n + 1)) =
      fun k => 2 / 3 ^ (n + 1) * (3⁻¹ : ℝ) ^ k := by
    funext k; rw [inv_pow]; field_simp; ring
  have hgeo := summable_geometric_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
  refine ⟨by rw [hterm]; exact hgeo.mul_left _, ?_⟩
  rw [hterm, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
  field_simp; norm_num

theorem tl_le (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : tl free ω n ≤ 1 / 3 ^ n := by
  rw [← (tsum_two_geom n).2, tl]
  refine (summable_tl free ω n).tsum_le_tsum (fun k => ?_) (tsum_two_geom n).1
  have : (ptDigit free ω (k + n) : ℝ) ≤ 2 := by exact_mod_cast ptDigit_le_two _ _ _
  exact div_le_div_of_nonneg_right this (by positivity)

/-- A digit `2` at place `i ≥ n` makes the tail at least `2·3^{-(i+1)}`. -/
theorem tl_ge (free : ℕ → Bool) (ω : ℕ → Bool) (n i : ℕ) (hi : n ≤ i)
    (h2 : ptDigit free ω i = 2) : 2 / (3 : ℝ) ^ (i + 1) ≤ tl free ω n := by
  rw [tl]
  have := (summable_tl free ω n).le_tsum (i - n) (fun k _ => by positivity)
  simp only [Nat.sub_add_cancel hi, h2, Nat.cast_ofNat] at this
  exact this

/-- Digits are zero on `[n, L)` once the tail is below `2·3^{-L}`. -/
theorem ptDigit_zero_of_tl_lt (free : ℕ → Bool) (ω : ℕ → Bool) (n L : ℕ)
    (h : tl free ω n < 2 / (3 : ℝ) ^ L) : ∀ i, n ≤ i → i < L → ptDigit free ω i = 0 := by
  intro i hni hiL
  rcases ptDigit_eq_zero_or free ω i with h0 | h2
  · exact h0
  · exfalso
    have h1 := tl_ge free ω n i hni h2
    have : 2 / (3 : ℝ) ^ L ≤ 2 / (3 : ℝ) ^ (i + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
    linarith

theorem hd_div_le_pt (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    (hd free ω n : ℝ) / 3 ^ n ≤ pt free ω := by
  rw [pt_split free ω n]; linarith [tl_nonneg free ω n]

theorem pt_le_hd_div (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    pt free ω ≤ (hd free ω n : ℝ) / 3 ^ n + 1 / 3 ^ n := by
  rw [pt_split free ω n]; linarith [tl_le free ω n]

/-! ## Separation and the Frostman ball bound -/

/-- First difference at a place `i` with digits `2` vs `0` separates by `3^{-(i+1)}`. -/
theorem sep (free : ℕ → Bool) (ω ω' : ℕ → Bool) (i : ℕ)
    (hpre : ∀ j < i, ptDigit free ω j = ptDigit free ω' j)
    (h2 : ptDigit free ω i = 2) (h0 : ptDigit free ω' i = 0) :
    1 / (3 : ℝ) ^ (i + 1) ≤ pt free ω - pt free ω' := by
  have hh : hd free ω (i + 1) = hd free ω' (i + 1) + 2 := by
    rw [hd_succ, hd_succ, hd_congr free ω ω' i hpre, h2, h0]
  have e1 := hd_div_le_pt free ω (i + 1)
  have e2 := pt_le_hd_div free ω' (i + 1)
  rw [hh] at e1
  push_cast at e1
  have : ((hd free ω' (i + 1) : ℝ) + 2) / 3 ^ (i + 1) =
      (hd free ω' (i + 1) : ℝ) / 3 ^ (i + 1) + 2 / 3 ^ (i + 1) := by ring
  rw [this] at e1
  have : (2 : ℝ) / 3 ^ (i + 1) = 1 / 3 ^ (i + 1) + 1 / 3 ^ (i + 1) := by ring
  linarith

/-- Two points closer than `3^{-n}` agree on the free coins below `n`. -/
theorem agree_of_close (free : ℕ → Bool) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : |pt free ω - pt free ω'| < 1 / (3 : ℝ) ^ n) :
    ∀ i < n, free i = true → ω i = ω' i := by
  classical
  by_contra hc
  push Not at hc
  have hex : ∃ i, i < n ∧ free i = true ∧ ω i ≠ ω' i := hc
  set i := Nat.find hex
  have hin : i < n := (Nat.find_spec hex).1
  have hfi : free i = true := (Nat.find_spec hex).2.1
  have hne : ω i ≠ ω' i := (Nat.find_spec hex).2.2
  have hpre : ∀ j < i, ptDigit free ω j = ptDigit free ω' j := by
    intro j hj
    have hnot := Nat.find_min hex hj
    unfold ptDigit
    by_cases hf : free j = true
    · have : ω j = ω' j := by
        by_contra hne'; exact hnot ⟨by omega, hf, hne'⟩
      rw [this]
    · simp [Bool.not_eq_true] at hf; simp [hf]
  have hmono : 1 / (3 : ℝ) ^ n ≤ 1 / (3 : ℝ) ^ (i + 1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  cases hω : ω i with
  | false =>
    have hω' : ω' i = true := by cases h' : ω' i <;> simp_all
    have := sep free ω' ω i (fun j hj => (hpre j hj).symm)
      (by simp [ptDigit, hfi, hω']) (by simp [ptDigit, hω])
    rw [abs_sub_comm] at h
    have := le_abs_self (pt free ω' - pt free ω)
    linarith
  | true =>
    have hω' : ω' i = false := by cases h' : ω' i <;> simp_all
    have := sep free ω ω' i hpre (by simp [ptDigit, hfi, hω]) (by simp [ptDigit, hω'])
    have := le_abs_self (pt free ω - pt free ω')
    linarith

/-- Mass of a free-coin cylinder. -/
theorem coins_cyl (ω₀ : ℕ → Bool) (S : Finset ℕ) :
    coins {ω | ∀ i ∈ S, ω i = ω₀ i} = (2⁻¹ : ENNReal) ^ S.card := by
  have hset : {ω : ℕ → Bool | ∀ i ∈ S, ω i = ω₀ i} = Set.pi (S : Set ℕ) (fun i => {ω₀ i}) := by
    ext ω; simp
  rw [hset]
  show ExplicitSquare.coinMeasure _ = _
  unfold ExplicitSquare.coinMeasure
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  rw [Finset.prod_congr rfl (g := fun _ => (2⁻¹ : ENNReal)) (fun i _ => by
    rw [CantorSelfSimilar.uniform_apply]; cases ω₀ i <;> simp), Finset.prod_const]

theorem coins_real_cyl (ω₀ : ℕ → Bool) (S : Finset ℕ) :
    coins.real {ω | ∀ i ∈ S, ω i = ω₀ i} = (1 / 2 : ℝ) ^ S.card := by
  rw [measureReal_def, coins_cyl, ENNReal.toReal_pow, ENNReal.toReal_inv]
  norm_num

/-- **Frostman ball bound** (sharp form): a ball of radius `≤ 3^{-(n+1)}` has coin mass at most
`2^{-F(n)}`. -/
theorem ball_le (free : ℕ → Bool) (y r : ℝ) (n : ℕ) (hr : r ≤ 1 / 3 ^ (n + 1)) :
    coins.real {ω | |pt free ω - y| < r} ≤ (1 / 2 : ℝ) ^ freeCount free n := by
  by_cases hE : ∃ ω₀, |pt free ω₀ - y| < r
  · obtain ⟨ω₀, h₀⟩ := hE
    set S := (Finset.range n).filter fun i => free i = true
    have hsub : {ω | |pt free ω - y| < r} ⊆ {ω | ∀ i ∈ S, ω i = ω₀ i} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro i hi
      simp only [S, Finset.mem_filter, Finset.mem_range] at hi
      refine agree_of_close free ω ω₀ n ?_ i hi.1 hi.2
      have h3 : 2 / (3 : ℝ) ^ (n + 1) < 1 / 3 ^ n := by
        rw [pow_succ, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) n]
      calc |pt free ω - pt free ω₀| ≤ |pt free ω - y| + |pt free ω₀ - y| := by
            rw [abs_sub_comm (pt free ω₀)]; exact abs_sub_le _ _ _
        _ < 2 * r := by linarith
        _ ≤ 2 / (3 : ℝ) ^ (n + 1) := by
            have := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
            linarith [show (2:ℝ) * (1 / 3 ^ (n + 1)) = 2 / 3 ^ (n + 1) by ring]
        _ < 1 / 3 ^ n := h3
    refine (measureReal_mono hsub).trans (le_of_eq ?_)
    rw [coins_real_cyl]; rfl
  · push Not at hE
    have : {ω | |pt free ω - y| < r} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]; exact hE ω
    rw [this, measureReal_empty]; positivity

/-! ## Counting numerators near the support -/

/-- The reachable depth-`n` head numerators. -/
def HS (free : ℕ → Bool) : ℕ → Finset ℕ
  | 0 => {0}
  | n + 1 => if free n then (HS free n).image (3 * ·) ∪ (HS free n).image (3 * · + 2)
      else (HS free n).image (3 * ·)

theorem freeCount_succ (free : ℕ → Bool) (n : ℕ) :
    freeCount free (n + 1) = freeCount free n + if free n then 1 else 0 := by
  unfold freeCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem card_HS (free : ℕ → Bool) (n : ℕ) : (HS free n).card ≤ 2 ^ freeCount free n := by
  induction n with
  | zero => simp [HS, freeCount]
  | succ n ih =>
    rw [HS, freeCount_succ]
    split_ifs with h
    · refine (Finset.card_union_le _ _).trans ?_
      rw [pow_succ]
      have := Finset.card_image_le (s := HS free n) (f := (3 * ·))
      have := Finset.card_image_le (s := HS free n) (f := (3 * · + 2))
      omega
    · simpa using (Finset.card_image_le (s := HS free n) (f := (3 * ·))).trans ih

theorem hd_mem_HS (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : hd free ω n ∈ HS free n := by
  induction n with
  | zero => simp [HS, hd]
  | succ n ih =>
    rw [HS, hd_succ]
    unfold ptDigit
    by_cases hf : free n = true
    · rw [if_pos hf]
      by_cases hω : ω n = true
      · simp only [hf, hω, Bool.and_self, if_true]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ih)
      · simp only [hf, Bool.true_and, Bool.not_eq_true] at hω ⊢
        simp only [hω, Bool.false_eq_true, if_false, add_zero]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ih)
    · have hf' : free n = false := by simpa using hf
      simp only [hf', Bool.false_and, Bool.false_eq_true, if_false, add_zero]
      exact Finset.mem_image_of_mem _ ih

open Classical in
/-- **Trivial count of numerators near the support** (sharp form, `3` per cylinder). -/
theorem card_near_le' (free : ℕ → Bool) (q m : ℕ) (hq : 0 < q) (hqm : q ≤ 3 ^ m) (r : ℝ)
    (hr : r ≤ 1 / q) :
    ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |pt free ω - p / q| < r).card ≤
      3 * 2 ^ freeCount free m := by
  have hsub : ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |pt free ω - p / q| < r) ⊆
      (HS free m).biUnion fun h => Finset.Icc (q * h / 3 ^ m) (q * h / 3 ^ m + 2) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨ω, hω⟩ := hp.2
    simp only [Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨hd free ω m, hd_mem_HS free ω m, ?_⟩
    set h := hd free ω m
    have e1 := hd_div_le_pt free ω m
    have e2 := pt_le_hd_div free ω m
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have h3 : (0 : ℝ) < 3 ^ m := by positivity
    have hq3 : (q : ℝ) ≤ 3 ^ m := by exact_mod_cast hqm
    have habs := abs_lt.1 hω
    have hrq : r * q ≤ 1 := by rw [le_div_iff₀ hqR] at hr; exact hr
    -- lower: (p+1) 3^m > q h
    have hlo : (q : ℝ) * h < ((p : ℝ) + 1) * 3 ^ m := by
      have a1 : (h : ℝ) / 3 ^ m - p / q < r := by linarith
      have a2 : ((h : ℝ) / 3 ^ m - p / q) * (q * 3 ^ m) < r * (q * 3 ^ m) :=
        mul_lt_mul_of_pos_right a1 (by positivity)
      have a3 : ((h : ℝ) / 3 ^ m - p / q) * (q * 3 ^ m) = q * h - p * 3 ^ m := by
        field_simp
      nlinarith
    have hhi : (p : ℝ) * 3 ^ m < q * h + 2 * 3 ^ m := by
      have a1 : (p : ℝ) / q - h / 3 ^ m < r + 1 / 3 ^ m := by linarith
      have a2 : ((p : ℝ) / q - h / 3 ^ m) * (q * 3 ^ m) < (r + 1 / 3 ^ m) * (q * 3 ^ m) :=
        mul_lt_mul_of_pos_right a1 (by positivity)
      have a3 : ((p : ℝ) / q - h / 3 ^ m) * (q * 3 ^ m) = p * 3 ^ m - q * h := by
        field_simp
      have a4 : (r + 1 / 3 ^ m) * (q * 3 ^ m) = r * q * 3 ^ m + q := by field_simp
      nlinarith
    have hlo' : q * h < (p + 1) * 3 ^ m := by exact_mod_cast hlo
    have hhi' : p * 3 ^ m < q * h + 2 * 3 ^ m := by exact_mod_cast hhi
    have hdiv := Nat.div_add_mod (q * h) (3 ^ m)
    have hmod := Nat.mod_lt (q * h) (show 0 < 3 ^ m by positivity)
    constructor
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by positivity)).2 hlo')
    · by_contra hc
      push Not at hc
      have : (q * h / 3 ^ m + 3) * 3 ^ m ≤ p * 3 ^ m := Nat.mul_le_mul_right _ hc
      nlinarith
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ h ∈ HS free m, (Finset.Icc (q * h / 3 ^ m) (q * h / 3 ^ m + 2)).card
      = ∑ h ∈ HS free m, 3 := Finset.sum_congr rfl fun h _ => by simp; omega
    _ = 3 * (HS free m).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 * 2 ^ freeCount free m := Nat.mul_le_mul_left _ (card_HS free m)

/-! ## Window free counts -/

/-- Free places in `[m, n)`. -/
def fc (free : ℕ → Bool) (m n : ℕ) : ℕ := ((Finset.Ico m n).filter fun i => free i = true).card

theorem fc_mono (free : ℕ → Bool) {m n m' n' : ℕ} (hm : m ≤ m') (hn : n' ≤ n) :
    fc free m' n' ≤ fc free m n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico hm hn))

theorem fc_add (free : ℕ → Bool) {m k n : ℕ} (h1 : m ≤ k) (h2 : k ≤ n) :
    fc free m n = fc free m k + fc free k n := by
  unfold fc
  rw [← Finset.Ico_union_Ico_eq_Ico h1 h2, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _))]

theorem fc_le (free : ℕ → Bool) (m n : ℕ) : fc free m n ≤ n - m :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem fc_of_free (free : ℕ → Bool) {m n : ℕ} (h : ∀ i, m ≤ i → i < n → free i = true) :
    fc free m n = n - m := by
  unfold fc
  rw [Finset.filter_true_of_mem (fun i hi => by rw [Finset.mem_Ico] at hi; exact h i hi.1 hi.2)]
  simp

theorem freeCount_eq_fc (free : ℕ → Bool) (n : ℕ) : freeCount free n = fc free 0 n := by
  unfold freeCount fc; rw [Finset.range_eq_Ico]

theorem freeCount_sub (free : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    freeCount free n = freeCount free m + fc free m n := by
  rw [freeCount_eq_fc, freeCount_eq_fc, fc_add free (Nat.zero_le m) h]

/-- Mass of "no free `true` in `[m, n)`". -/
theorem coins_zero_window (free : ℕ → Bool) (m n : ℕ) :
    coins.real {ω | ∀ i, m ≤ i → i < n → free i = true → ω i = false} =
      (1 / 2 : ℝ) ^ fc free m n := by
  have hset : {ω : ℕ → Bool | ∀ i, m ≤ i → i < n → free i = true → ω i = false} =
      {ω | ∀ i ∈ (Finset.Ico m n).filter fun i => free i = true, ω i = (fun _ => false) i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_Ico, and_imp]
  rw [hset, coins_real_cyl]; rfl

/-! ## Digit-structure lemmas -/

/-- Zero digits on `[a, E)` extend the head by zeros. -/
theorem hd_zero_ext (free : ℕ → Bool) (ω : ℕ → Bool) (a : ℕ) :
    ∀ E, a ≤ E → (∀ i, a ≤ i → i < E → ptDigit free ω i = 0) →
      hd free ω E = 3 ^ (E - a) * hd free ω a := by
  intro E
  induction E with
  | zero => intro h _; obtain rfl : a = 0 := by omega
            simp
  | succ E ih =>
    intro hE hz
    rcases Nat.eq_or_lt_of_le hE with h | h
    · subst h; simp
    · rw [hd_succ, ih (by omega) (fun i h1 h2 => hz i h1 (by omega)), hz E (by omega) (by omega),
        show E + 1 - a = (E - a) + 1 by omega, pow_succ]
      ring

/-- `3^j ∣ hd a` forces zero digits on `[a - j, a)`. -/
theorem digits_zero_of_dvd (free : ℕ → Bool) (ω : ℕ → Bool) :
    ∀ j a, j ≤ a → 3 ^ j ∣ hd free ω a → ∀ i, a - j ≤ i → i < a → ptDigit free ω i = 0 := by
  intro j
  induction j with
  | zero => intro a _ _ i h1 h2; omega
  | succ j ih =>
    intro a hja hdvd i h1 h2
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [hd_succ] at hdvd
    have h3 : 3 ∣ 3 * hd free ω a' + ptDigit free ω a' :=
      (dvd_pow_self 3 (by omega)).trans hdvd
    have hd0 : ptDigit free ω a' = 0 := by
      rcases ptDigit_eq_zero_or free ω a' with h | h
      · exact h
      · rw [h] at h3; omega
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.1 h2) with hi | hi
    · rw [hi]; exact hd0
    · rw [hd0, add_zero, pow_succ, mul_comm 3] at hdvd
      exact ih a' (by omega) (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd) i (by omega) hi

/-- Valuation step: `pp 3^a = P q` with `q < 3^{m+1}` gives `3^{a-m} ∣ P`. -/
theorem pow_dvd_of_eq {pp P q a m : ℕ} (hq : q ≠ 0) (hq3 : q < 3 ^ (m + 1))
    (h : pp * 3 ^ a = P * q) : 3 ^ (a - m) ∣ P := by
  obtain ⟨v, q', hq', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq 3 (by norm_num)
  have hv : v ≤ m := by
    by_contra hc
    have : 3 ^ (m + 1) ≤ 3 ^ v * q' :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hq)))
    omega
  rcases le_or_gt a v with hav | hav
  · rw [show a - m = 0 by omega]; simp
  have hdvd : 3 ^ (a - v) * 3 ^ v ∣ P * q' * 3 ^ v := by
    rw [← pow_add, show a - v + v = a by omega]
    exact ⟨pp, by rw [mul_comm (P * q')]; linarith [h]⟩
  have h2 : 3 ^ (a - v) ∣ P * q' := Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd
  have hcop : Nat.Coprime (3 ^ (a - v)) q' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hq')
  exact (Nat.pow_dvd_pow 3 (by omega)).trans (hcop.dvd_of_dvd_mul_right h2)

/-! ## The prefix test at scale `m` -/

/-- Ternary digit read from a coin prefix. -/
def tDig (free : ℕ → Bool) (p : List Bool) (i : ℕ) : ℕ := bif free i && p.getD i false then 2 else 0

/-- Head numerator of length `N` read from a prefix. -/
def tNum (free : ℕ → Bool) (N : ℕ) (p : List Bool) : ℕ :=
  ((List.range N).map fun i => tDig free p i * 3 ^ (N - 1 - i)).sum

/-- `|tNum/3^{L+1} − pp/q| ≤ 3^{-L}` with `q ∈ [3^m, 3^{m+1})`. -/
def hitCond (free : ℕ → Bool) (m L : ℕ) (p : List Bool) (q pp : ℕ) : Prop :=
  3 ^ m ≤ q ∧ tNum free (L + 1) p * q ≤ pp * 3 ^ (L + 1) + 3 * q ∧
    pp * 3 ^ (L + 1) ≤ tNum free (L + 1) p * q + 3 * q

instance (free : ℕ → Bool) (m L : ℕ) (p : List Bool) (q pp : ℕ) :
    Decidable (hitCond free m L p q pp) := by unfold hitCond; infer_instance

/-- Number of hits at scale `m`. -/
def hitCnt (free : ℕ → Bool) (m L : ℕ) (p : List Bool) : ℕ :=
  ((List.range (3 ^ (m + 1))).map fun q =>
    ((List.range (q + 1)).map fun pp => if hitCond free m L p q pp then 1 else 0).sum).sum

/-- The scale-`m` test. -/
def hitB (free : ℕ → Bool) (m L : ℕ) (p : List Bool) : Bool := decide (0 < hitCnt free m L p)

theorem tNum_pre (free : ℕ → Bool) (ω : ℕ → Bool) (N : ℕ) : tNum free N (pre ω N) = hd free ω N := by
  rw [tNum, ComputableNormalB.list_sum_range_map, hd]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold tDig ptDigit; rw [CantorLiouville.getD_pre ω hi']; cases free i && ω i <;> rfl

theorem hitB_iff (free : ℕ → Bool) (m L : ℕ) (p : List Bool) :
    hitB free m L p = true ↔ ∃ q pp, q < 3 ^ (m + 1) ∧ pp ≤ q ∧ hitCond free m L p q pp := by
  rw [hitB, decide_eq_true_eq, hitCnt, ComputableNormalB.list_sum_range_map]
  constructor
  · intro h
    obtain ⟨q, hq, hpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.1 h)
    rw [ComputableNormalB.list_sum_range_map] at hpos
    obtain ⟨pp, hpp, hpos'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
    simp only [Finset.mem_range] at hq hpp
    refine ⟨q, pp, hq, by omega, ?_⟩
    by_contra hc; simp [hc] at hpos'
  · rintro ⟨q, pp, hq, hpp, hc⟩
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hq))
    rw [ComputableNormalB.list_sum_range_map]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hpp)))
    simp [hc]

/-- Real form of `hitCond` on a true prefix. -/
theorem hitCond_pre_iff (free : ℕ → Bool) (ω : ℕ → Bool) (m L q pp : ℕ) (hq : 0 < q) :
    (|(hd free ω (L + 1) : ℝ) / 3 ^ (L + 1) - pp / q| ≤ 3 / 3 ^ (L + 1)) ↔
      (tNum free (L + 1) (pre ω (L + 1)) * q ≤ pp * 3 ^ (L + 1) + 3 * q ∧
        pp * 3 ^ (L + 1) ≤ tNum free (L + 1) (pre ω (L + 1)) * q + 3 * q) := by
  rw [tNum_pre]
  set h := hd free ω (L + 1)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 3 ^ (L + 1) := by positivity
  have e : (h : ℝ) / 3 ^ (L + 1) - pp / q = ((h : ℝ) * q - pp * 3 ^ (L + 1)) / (q * 3 ^ (L + 1)) := by
    field_simp
  have hD : (0:ℝ) < q * 3 ^ (L + 1) := by positivity
  rw [e, abs_div, abs_of_pos hD, div_le_div_iff₀ hD h3,
    show (3:ℝ) * (q * 3 ^ (L + 1)) = (3 * q) * 3 ^ (L + 1) by ring]
  rw [show (|(h : ℝ) * q - pp * 3 ^ (L + 1)| * 3 ^ (L + 1) ≤ (3 * q) * 3 ^ (L + 1)) ↔
      |(h : ℝ) * q - pp * 3 ^ (L + 1)| ≤ 3 * q from
    ⟨fun k => le_of_mul_le_mul_right k h3, fun k => mul_le_mul_of_nonneg_right k h3.le⟩, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (h : ℝ) * q ≤ pp * 3 ^ (L + 1) + 3 * q := by nlinarith
      exact_mod_cast this
    · have : (pp : ℝ) * 3 ^ (L + 1) ≤ h * q + 3 * q := by nlinarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (h : ℝ) * q ≤ pp * 3 ^ (L + 1) + 3 * q := by exact_mod_cast h1
    have h2' : (pp : ℝ) * 3 ^ (L + 1) ≤ h * q + 3 * q := by exact_mod_cast h2
    constructor <;> nlinarith

/-- **Firing**: a rational `pp/q` at scale `m` within `2·3^{-(L+1)}` of the point trips the test. -/
theorem hitB_of_near (free : ℕ → Bool) (ω : ℕ → Bool) (m L q pp : ℕ) (hq1 : 3 ^ m ≤ q)
    (hq2 : q < 3 ^ (m + 1)) (hpp : pp ≤ q)
    (h : |pt free ω - pp / q| ≤ 2 / 3 ^ (L + 1)) : hitB free m L (pre ω (L + 1)) = true := by
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hq1
  rw [hitB_iff]
  refine ⟨q, pp, hq2, hpp, hq1, (hitCond_pre_iff free ω m L q pp hq).1 ?_⟩
  have e1 := hd_div_le_pt free ω (L + 1)
  have e2 := pt_le_hd_div free ω (L + 1)
  have k : (3:ℝ) / 3 ^ (L + 1) = 2 / 3 ^ (L + 1) + 1 / 3 ^ (L + 1) := by ring
  rw [abs_le] at h ⊢
  rw [k]
  constructor <;> linarith [h.1, h.2]

/-- **Soundness**: a tripped test gives a rational at scale `m` within `2·3^{-L}`. -/
theorem near_of_hitB (free : ℕ → Bool) (ω : ℕ → Bool) (m L : ℕ)
    (h : hitB free m L (pre ω (L + 1)) = true) :
    ∃ q pp : ℕ, 3 ^ m ≤ q ∧ q < 3 ^ (m + 1) ∧ pp ≤ q ∧ |pt free ω - pp / q| < 2 / 3 ^ L := by
  obtain ⟨q, pp, hq2, hpp, hq1, hc⟩ := (hitB_iff free m L _).1 h
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hq1
  refine ⟨q, pp, hq1, hq2, hpp, ?_⟩
  have h' := (hitCond_pre_iff free ω m L q pp hq).2 hc
  have e1 := hd_div_le_pt free ω (L + 1)
  have e2 := pt_le_hd_div free ω (L + 1)
  have e3 : (3 : ℝ) ^ (L + 1) = 3 * 3 ^ L := by rw [pow_succ]; ring
  rw [e3] at h' e1 e2
  have h3 : (0 : ℝ) < 3 ^ L := by positivity
  have k1 : 3 / (3 * (3 : ℝ) ^ L) = 1 / 3 ^ L := by field_simp
  have k2 : 1 / (3 * (3 : ℝ) ^ L) < 1 / 3 ^ L := by
    apply one_div_lt_one_div_of_lt h3; linarith
  rw [k1] at h'
  rw [abs_le] at h'
  rw [abs_lt]
  have k3 : 2 / (3 : ℝ) ^ L = 1 / 3 ^ L + 1 / 3 ^ L := by ring
  constructor <;> linarith [h'.1, h'.2]

/-! ## Masses of the test -/

/-- Triangle inequality at a forced approximation (copy of the frozen leaf, for reuse). -/
theorem abs_sub_ge_of_near' (x : ℝ) (P a E q : ℕ) (p : ℤ) (hq : 0 < q)
    (hx : |x - P / 3 ^ a| ≤ 1 / 3 ^ E) (hne : (p : ℝ) / q ≠ P / 3 ^ a)
    (hqE : 2 * q * 3 ^ a ≤ 3 ^ E) :
    1 / (2 * (q : ℝ) * 3 ^ a) ≤ |x - p / q| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 3 ^ a := by positivity
  set n : ℤ := p * 3 ^ a - P * q with hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hne
    have : (p : ℝ) * 3 ^ a = P * q := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h0
      simp only [hn] at this; push_cast at this; linarith
    field_simp; linarith
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  have hdiff : (p : ℝ) / q - P / 3 ^ a = n / (q * 3 ^ a) := by
    simp only [hn]; push_cast; field_simp
  have hge : 1 / ((q : ℝ) * 3 ^ a) ≤ |(p : ℝ) / q - P / 3 ^ a| := by
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * 3 ^ a)]
    exact div_le_div_of_nonneg_right hn1 (by positivity)
  have hE : 1 / (3 : ℝ) ^ E ≤ 1 / (2 * q * 3 ^ a) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hqE
  have htri : |(p : ℝ) / q - P / 3 ^ a| ≤ |x - p / q| + |x - P / 3 ^ a| := by
    rw [abs_sub_comm x]; exact abs_sub_le _ _ _
  have : 1 / ((q : ℝ) * 3 ^ a) = 2 * (1 / (2 * q * 3 ^ a)) := by field_simp
  linarith

/-- **Borel–Cantelli mass of the scale-`m` test**: `≤ 6·3^m·2^{-W}`, `W` the free count of
`[m+1, L-2)`. -/
theorem hit_mass_bc (free : ℕ → Bool) (m L : ℕ) (hL : m + 3 ≤ L) :
    coins.real {ω | hitB free m L (pre ω (L + 1)) = true} ≤
      6 * 3 ^ m * (1 / 2 : ℝ) ^ fc free (m + 1) (L - 2) := by
  classical
  set r : ℝ := 2 / 3 ^ L with hr
  set near : ℕ → Finset ℕ := fun q =>
    (Finset.range (q + 1)).filter fun pp : ℕ => ∃ ω, |pt free ω - pp / q| < r
  have hsub : {ω | hitB free m L (pre ω (L + 1)) = true} ⊆
      ⋃ q ∈ Finset.Ico (3 ^ m) (3 ^ (m + 1)), ⋃ pp ∈ near q, {ω | |pt free ω - pp / q| < r} := by
    intro ω hω
    obtain ⟨q, pp, hq1, hq2, hpp, hlt⟩ := near_of_hitB free ω m L hω
    simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_setOf_eq]
    refine ⟨q, ⟨hq1, hq2⟩, pp, ?_, hlt⟩
    simp only [near, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ω, hlt⟩
  have hball : ∀ q pp : ℕ, coins.real {ω | |pt free ω - pp / q| < r} ≤
      (1 / 2 : ℝ) ^ freeCount free (L - 2) := by
    intro q pp
    refine ball_le free _ r (L - 2) ?_
    rw [show L - 2 + 1 = L - 1 by omega, hr]
    have : (3 : ℝ) ^ L = 3 * 3 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) (L - 1)]
  have hcard : ∀ q ∈ Finset.Ico (3 ^ m) (3 ^ (m + 1)), (near q).card ≤ 3 * 2 ^ freeCount free (m + 1) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq.1
    refine card_near_le' free q (m + 1) hq0 hq.2.le r ?_
    rw [hr, div_le_div_iff₀ (by positivity) (by exact_mod_cast hq0)]
    have h1 : (q : ℝ) < 3 ^ (m + 1) := by exact_mod_cast hq.2
    have h2 : (3 : ℝ) ^ (m + 1) * 3 ≤ 3 ^ L := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hF : freeCount free (L - 2) = freeCount free (m + 1) + fc free (m + 1) (L - 2) :=
    freeCount_sub free (by omega)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ q ∈ Finset.Ico (3 ^ m) (3 ^ (m + 1)),
        coins.real (⋃ pp ∈ near q, {ω | |pt free ω - pp / q| < r})
      ≤ ∑ q ∈ Finset.Ico (3 ^ m) (3 ^ (m + 1)),
          (3 * 2 ^ freeCount free (m + 1) : ℝ) * (1 / 2 : ℝ) ^ freeCount free (L - 2) := by
        refine Finset.sum_le_sum fun q hq => (measureReal_biUnion_finset_le _ _).trans ?_
        refine (Finset.sum_le_sum fun pp _ => hball q pp).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard q hq
    _ = 6 * 3 ^ m * (1 / 2 : ℝ) ^ fc free (m + 1) (L - 2) := by
        have e : 3 ^ (m + 1) - 3 ^ m = 2 * 3 ^ m := by rw [pow_succ]; omega
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, e, hF, pow_add (1 / 2 : ℝ)]
        push_cast
        have : (2 : ℝ) ^ freeCount free (m + 1) * (1 / 2) ^ freeCount free (m + 1) = 1 := by
          rw [← mul_pow]; norm_num
        calc (2 * 3 ^ m : ℝ) * (3 * 2 ^ freeCount free (m + 1) *
              ((1 / 2) ^ freeCount free (m + 1) * (1 / 2) ^ fc free (m + 1) (L - 2)))
            = 6 * 3 ^ m * (2 ^ freeCount free (m + 1) * (1 / 2) ^ freeCount free (m + 1)) *
              (1 / 2) ^ fc free (m + 1) (L - 2) := by ring
          _ = _ := by rw [this, mul_one]

/-- **Triangle-range mass of the scale-`m` test.**  Next to a forced run `[a, E)` with
`m + a + 2 ≤ E` and `m + a + 3 ≤ L`, the only rational that can trip the test is the
truncation `P/3^a`, and then all digits in `[m, L)` vanish. -/
theorem hit_mass_tri (free : ℕ → Bool) (m L a E : ℕ)
    (hz : ∀ i, a ≤ i → i < E → free i = false) (haE : m + a + 2 ≤ E) (hL : m + a + 3 ≤ L) :
    coins.real {ω | hitB free m L (pre ω (L + 1)) = true} ≤ (1 / 2 : ℝ) ^ fc free m L := by
  rw [← coins_zero_window]
  refine measureReal_mono fun ω hω => ?_
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨q, pp, hq1, hq2, hpp, hlt⟩ := near_of_hitB free ω m L hω
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  set P := hd free ω a
  have hzd : ∀ i, a ≤ i → i < E → ptDigit free ω i = 0 := fun i h1 h2 => by
    simp [ptDigit, hz i h1 h2]
  have hE := hd_zero_ext free ω a E (by omega) hzd
  have hsplitE := pt_split free ω E
  have hPE : (hd free ω E : ℝ) / 3 ^ E = P / 3 ^ a := by
    rw [hE]; push_cast
    rw [show (3 : ℝ) ^ E = 3 ^ (E - a) * 3 ^ a by rw [← pow_add]; congr 1; omega]
    field_simp
    rfl
  have hnear : |pt free ω - P / 3 ^ a| ≤ 1 / 3 ^ E := by
    rw [hsplitE, hPE, add_sub_cancel_left, abs_of_nonneg (tl_nonneg _ _ _)]; exact tl_le _ _ _
  have heq : (pp : ℝ) / q = P / 3 ^ a := by
    by_contra hne
    have hqE : 2 * q * 3 ^ a ≤ 3 ^ E := by
      have : 2 * q * 3 ^ a ≤ 2 * 3 ^ (m + 1) * 3 ^ a := by gcongr
      refine this.trans ?_
      rw [mul_assoc, ← pow_add]
      calc 2 * 3 ^ (m + 1 + a) ≤ 3 * 3 ^ (m + 1 + a) := by omega
        _ = 3 ^ (m + a + 2) := by rw [← pow_succ']; congr 1; omega
        _ ≤ 3 ^ E := Nat.pow_le_pow_right (by norm_num) haE
    have h1 := abs_sub_ge_of_near' (pt free ω) P a E q (pp : ℤ) hq0 hnear (by simpa using hne) hqE
    simp only [Int.cast_natCast] at h1
    have h2 : (2 : ℝ) / 3 ^ L ≤ 1 / (2 * q * 3 ^ a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (q : ℝ) < 3 ^ (m + 1) := by exact_mod_cast hq2
      have h3 : (3 : ℝ) ^ (m + 1) * 3 ^ a * 9 ≤ 3 ^ L := by
        rw [← pow_add, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : (0 : ℝ) < 3 ^ a := by positivity
      nlinarith
    linarith
  -- digits vanish on `[a, L)`
  have hsplit := pt_split free ω a
  have htl : tl free ω a < 2 / (3 : ℝ) ^ L := by
    have : pt free ω - pp / q = tl free ω a := by rw [heq, hsplit]; ring
    rw [this, abs_of_nonneg (tl_nonneg _ _ _)] at hlt; exact hlt
  have hza := ptDigit_zero_of_tl_lt free ω a L htl
  -- digits vanish on `[m, a)`
  have hzm : ∀ i, m ≤ i → i < a → ptDigit free ω i = 0 := by
    intro i h1 h2
    have hnat : pp * 3 ^ a = P * q := by
      have : (pp : ℝ) * 3 ^ a = P * q := by
        field_simp at heq; linarith
      exact_mod_cast this
    have hdvd := pow_dvd_of_eq (m := m) hq0.ne' hq2 hnat
    exact digits_zero_of_dvd free ω (a - m) a (by omega) hdvd i (by omega) h2
  intro i h1 h2 hf
  have hd0 : ptDigit free ω i = 0 := by
    rcases lt_or_ge i a with h | h
    · exact hzm i h1 h
    · exact hza i h h2
  rw [ptDigit_eq_zero_iff] at hd0
  cases hω' : ω i
  · rfl
  · exact absurd ⟨hf, hω'⟩ hd0

end NormalNumbers.CantorExpGeneric
