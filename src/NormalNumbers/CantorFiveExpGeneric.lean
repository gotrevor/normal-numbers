/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorFiveNormal

/-!
# Generic estimates for the base-5 coin points `ptF free ω`

Base-5 counterpart of `CantorExpGeneric`.  The one structural change: the digits `{0,1,3,4}`
leave no gap between the cylinders of `0`/`1` and of `3`/`4`, so two close points need not share
a cylinder.  The Frostman bound goes through head numerators instead: points within `2·5^{−n−1}`
have heads `hdF · n` within `1` (`hdF_close`), and a head determines the free coins below `n`.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorFiveExpGeneric

open CantorLiouville Derandomize CantorFiveMoment CantorFiveNormal CantorExpGeneric

/-! ## Heads -/

theorem hdF_lt (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : hdF free ω n < 5 ^ n := by
  induction n with
  | zero => simp [hdF]
  | succ n ih =>
    rw [hdF_succ, pow_succ]
    have := ptDigitF_le_four free ω n
    omega

theorem hdF_div_le_ptF (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    (hdF free ω n : ℝ) / 5 ^ n ≤ ptF free ω := by
  rw [ptF_split free ω n]; linarith [tlF_nonneg free ω n]

theorem ptF_le_hdF_div (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    ptF free ω ≤ (hdF free ω n : ℝ) / 5 ^ n + 1 / 5 ^ n := by
  rw [ptF_split free ω n]; linarith [tlF_le free ω n]

/-- A nonzero digit at place `i ≥ n` makes the tail at least `5^{-(i+1)}`. -/
theorem tlF_ge (free : ℕ → Bool) (ω : ℕ → Bool) (n i : ℕ) (hi : n ≤ i)
    (h : ptDigitF free ω i ≠ 0) : 1 / (5 : ℝ) ^ (i + 1) ≤ tlF free ω n := by
  rw [tlF]
  have := (summable_tlF free ω n).le_tsum (i - n) (fun k _ => by positivity)
  simp only [Nat.sub_add_cancel hi] at this
  have h1 : (1 : ℝ) ≤ ptDigitF free ω i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
  calc 1 / (5 : ℝ) ^ (i + 1) ≤ (ptDigitF free ω i : ℝ) / 5 ^ (i + 1) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ _ := this

/-- Digits vanish on `[n, L)` once the tail is below `5^{-L}`. -/
theorem ptDigitF_zero_of_tl_lt (free : ℕ → Bool) (ω : ℕ → Bool) (n L : ℕ)
    (h : tlF free ω n < 1 / (5 : ℝ) ^ L) : ∀ i, n ≤ i → i < L → ptDigitF free ω i = 0 := by
  intro i hni hiL
  by_contra h0
  have h1 := tlF_ge free ω n i hni h0
  have : 1 / (5 : ℝ) ^ L ≤ 1 / (5 : ℝ) ^ (i + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  linarith

/-- Equal heads have equal digits. -/
theorem hdF_inj (free : ℕ → Bool) (ω ω' : ℕ → Bool) :
    ∀ n, hdF free ω n = hdF free ω' n → ∀ i < n, ptDigitF free ω i = ptDigitF free ω' i := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    rw [hdF_succ, hdF_succ] at h
    have h1 := ptDigitF_le_four free ω n
    have h2 := ptDigitF_le_four free ω' n
    have hd : ptDigitF free ω n = ptDigitF free ω' n := by omega
    have hh : hdF free ω n = hdF free ω' n := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih hh i hi
    · exact hd

/-- Equal digits at a free place have equal coins. -/
theorem coins_eq_of_digit (free : ℕ → Bool) (ω ω' : ℕ → Bool) (i : ℕ) (hf : free i = true)
    (h : ptDigitF free ω i = ptDigitF free ω' i) :
    ω (2 * i) = ω' (2 * i) ∧ ω (2 * i + 1) = ω' (2 * i + 1) := by
  unfold ptDigitF at h
  rw [if_pos hf, if_pos hf] at h
  revert h
  generalize ω (2 * i) = a; generalize ω (2 * i + 1) = b
  generalize ω' (2 * i) = c; generalize ω' (2 * i + 1) = d
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-! ## Coin sets -/

/-- Coins read by the free places in `[m, n)`. -/
def coinSet (free : ℕ → Bool) (m n : ℕ) : Finset ℕ :=
  (Finset.Ico (2 * m) (2 * n)).filter fun j => free (j / 2) = true

theorem card_coinSet (free : ℕ → Bool) (m : ℕ) :
    ∀ n, m ≤ n → (coinSet free m n).card = 2 * fc free m n := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp [coinSet, fc]
  | succ n hmn ih =>
    have hS : coinSet free m (n + 1) = coinSet free m n ∪
        (({2 * n, 2 * n + 1} : Finset ℕ).filter fun j => free (j / 2) = true) := by
      unfold coinSet
      rw [← Finset.filter_union]
      congr 1
      ext j; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]; omega
    have hdisj : Disjoint (coinSet free m n)
        (({2 * n, 2 * n + 1} : Finset ℕ).filter fun j => free (j / 2) = true) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [coinSet, Finset.mem_filter, Finset.mem_Ico] at h1
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h2
      omega
    rw [hS, Finset.card_union_of_disjoint hdisj, ih, fc_add free hmn (Nat.le_succ n)]
    have e1 : (2 * n) / 2 = n := by omega
    have e2 : (2 * n + 1) / 2 = n := by omega
    have hfc : fc free n (n + 1) = if free n = true then 1 else 0 := by
      unfold fc
      rw [Nat.Ico_succ_singleton, Finset.filter_singleton]
      split_ifs <;> simp
    rw [hfc, Finset.filter_insert, Finset.filter_singleton, e1, e2]
    split_ifs with hf
    · rw [Finset.card_insert_of_notMem (by simp)]; simp; ring
    · simp

theorem mem_coinSet {free : ℕ → Bool} {m n j : ℕ} :
    j ∈ coinSet free m n ↔ 2 * m ≤ j ∧ j < 2 * n ∧ free (j / 2) = true := by
  simp [coinSet, and_assoc]

/-- Mass of "no free nonzero digit in `[m, n)`". -/
theorem coins_zero_windowF (free : ℕ → Bool) (m n : ℕ) (hmn : m ≤ n) :
    coins.real {ω | ∀ i, m ≤ i → i < n → free i = true → ω (2 * i) = false ∧ ω (2 * i + 1) = false} =
      (1 / 4 : ℝ) ^ fc free m n := by
  have hset : {ω : ℕ → Bool | ∀ i, m ≤ i → i < n → free i = true →
      ω (2 * i) = false ∧ ω (2 * i + 1) = false} =
      {ω | ∀ j ∈ coinSet free m n, ω j = (fun _ => false) j} := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_coinSet]
    constructor
    · intro h j ⟨h1, h2, h3⟩
      have := h (j / 2) (by omega) (by omega) h3
      rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
      · have : j = 2 * (j / 2) := by omega
        rw [this]; exact (h (j / 2) (by omega) (by omega) h3).1
      · have : j = 2 * (j / 2) + 1 := by omega
        rw [this]; exact (h (j / 2) (by omega) (by omega) h3).2
    · intro h i h1 h2 h3
      refine ⟨h (2 * i) ⟨by omega, by omega, by rw [show 2 * i / 2 = i by omega]; exact h3⟩,
        h (2 * i + 1) ⟨by omega, by omega, by rw [show (2 * i + 1) / 2 = i by omega]; exact h3⟩⟩
  rw [hset, coins_real_cyl, card_coinSet free m n hmn, pow_mul]
  norm_num

/-! ## The Frostman ball bound -/

/-- Points within `2·5^{−(n+1)}` have heads within `1`. -/
theorem hdF_close (free : ℕ → Bool) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : |ptF free ω - ptF free ω'| < 2 / (5 : ℝ) ^ (n + 1)) :
    hdF free ω n ≤ hdF free ω' n + 1 := by
  have e1 := hdF_div_le_ptF free ω n
  have e2 := ptF_le_hdF_div free ω' n
  have h5 : (0 : ℝ) < 5 ^ n := by positivity
  have k : (2 : ℝ) / 5 ^ (n + 1) < 1 / 5 ^ n := by
    rw [pow_succ, div_lt_div_iff₀ (by positivity) h5]; nlinarith
  have habs := (abs_lt.1 h).2
  have : (hdF free ω n : ℝ) / 5 ^ n < (hdF free ω' n : ℝ) / 5 ^ n + 2 / 5 ^ n := by
    have : (2 : ℝ) / 5 ^ n = 1 / 5 ^ n + 1 / 5 ^ n := by ring
    linarith
  rw [← add_div, div_lt_div_iff_of_pos_right h5] at this
  have : (hdF free ω n : ℝ) < hdF free ω' n + 2 := this
  have : hdF free ω n < hdF free ω' n + 2 := by exact_mod_cast this
  omega

/-- A head value fixes the free coins below `n`. -/
theorem coins_hd_le (free : ℕ → Bool) (n h : ℕ) :
    coins.real {ω | hdF free ω n = h} ≤ (1 / 4 : ℝ) ^ freeCount free n := by
  by_cases hE : ∃ ω₀, hdF free ω₀ n = h
  · obtain ⟨ω₀, h₀⟩ := hE
    have hsub : {ω | hdF free ω n = h} ⊆ {ω | ∀ j ∈ coinSet free 0 n, ω j = ω₀ j} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, mem_coinSet] at hω ⊢
      intro j ⟨_, hj2, hj3⟩
      have hdig := hdF_inj free ω ω₀ n (hω.trans h₀.symm) (j / 2) (by omega)
      have := coins_eq_of_digit free ω ω₀ (j / 2) hj3 hdig
      rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
      · have e : j = 2 * (j / 2) := by omega
        rw [e]; exact this.1
      · have e : j = 2 * (j / 2) + 1 := by omega
        rw [e]; exact this.2
    refine (measureReal_mono hsub).trans (le_of_eq ?_)
    rw [coins_real_cyl, card_coinSet free 0 n (Nat.zero_le _), pow_mul, freeCount_eq_fc]
    norm_num
  · push Not at hE
    have : {ω | hdF free ω n = h} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hE ω
    rw [this, measureReal_empty]; positivity

/-- **Frostman ball bound, base 5**: a ball of radius `≤ 5^{-(n+1)}` has mass `≤ 3·4^{-F(n)}`. -/
theorem ball_leF (free : ℕ → Bool) (y r : ℝ) (n : ℕ) (hr : r ≤ 1 / 5 ^ (n + 1)) :
    coins.real {ω | |ptF free ω - y| < r} ≤ 3 * (1 / 4 : ℝ) ^ freeCount free n := by
  by_cases hE : ∃ ω₀, |ptF free ω₀ - y| < r
  · obtain ⟨ω₀, h₀⟩ := hE
    set h₀' := hdF free ω₀ n
    have hsub : {ω | |ptF free ω - y| < r} ⊆
        ⋃ h ∈ Finset.Icc (h₀' - 1) (h₀' + 1), {ω | hdF free ω n = h} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      have hc : ∀ ω₁ ω₂ : ℕ → Bool, |ptF free ω₁ - y| < r → |ptF free ω₂ - y| < r →
          |ptF free ω₁ - ptF free ω₂| < 2 / (5 : ℝ) ^ (n + 1) := by
        intro ω₁ ω₂ h1 h2
        calc |ptF free ω₁ - ptF free ω₂| ≤ |ptF free ω₁ - y| + |ptF free ω₂ - y| := by
              rw [abs_sub_comm (ptF free ω₂)]; exact abs_sub_le _ _ _
          _ < 2 * r := by linarith
          _ ≤ 2 / (5 : ℝ) ^ (n + 1) := by
              have := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
              linarith [show (2:ℝ) * (1 / 5 ^ (n + 1)) = 2 / 5 ^ (n + 1) by ring]
      have a1 := hdF_close free ω ω₀ n (hc ω ω₀ hω h₀)
      have a2 := hdF_close free ω₀ ω n (hc ω₀ ω h₀ hω)
      simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_setOf_eq]
      exact ⟨_, ⟨by omega, by omega⟩, rfl⟩
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun h _ => coins_hd_le free n h).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    gcongr
    have : (Finset.Icc (h₀' - 1) (h₀' + 1)).card ≤ 3 := by simp; omega
    exact_mod_cast this
  · push Not at hE
    have : {ω | |ptF free ω - y| < r} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]; exact hE ω
    rw [this, measureReal_empty]; positivity

/-! ## Counting numerators near the support -/

/-- The reachable depth-`n` head numerators. -/
def HSF (free : ℕ → Bool) : ℕ → Finset ℕ
  | 0 => {0}
  | n + 1 => if free n then ((HSF free n).image (5 * ·) ∪ (HSF free n).image (5 * · + 1)) ∪
        ((HSF free n).image (5 * · + 3) ∪ (HSF free n).image (5 * · + 4))
      else (HSF free n).image (5 * ·)

theorem card_HSF (free : ℕ → Bool) (n : ℕ) : (HSF free n).card ≤ 4 ^ freeCount free n := by
  induction n with
  | zero => simp [HSF, freeCount]
  | succ n ih =>
    rw [HSF, freeCount_succ]
    split_ifs with h
    · refine (Finset.card_union_le _ _).trans ?_
      have a := (Finset.card_union_le ((HSF free n).image (5 * ·)) ((HSF free n).image (5 * · + 1)))
      have b := (Finset.card_union_le ((HSF free n).image (5 * · + 3)) ((HSF free n).image (5 * · + 4)))
      have := Finset.card_image_le (s := HSF free n) (f := (5 * ·))
      have := Finset.card_image_le (s := HSF free n) (f := (5 * · + 1))
      have := Finset.card_image_le (s := HSF free n) (f := (5 * · + 3))
      have := Finset.card_image_le (s := HSF free n) (f := (5 * · + 4))
      rw [pow_succ]
      omega
    · simpa using (Finset.card_image_le (s := HSF free n) (f := (5 * ·))).trans ih

theorem hdF_mem_HSF (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) : hdF free ω n ∈ HSF free n := by
  induction n with
  | zero => simp [HSF, hdF]
  | succ n ih =>
    rw [HSF, hdF_succ]
    unfold ptDigitF
    by_cases hf : free n = true
    · rw [if_pos hf, if_pos hf]
      simp only [Finset.mem_union, Finset.mem_image]
      have m0 := Finset.mem_image_of_mem (fun x => 5 * x) ih
      have m1 := Finset.mem_image_of_mem (fun x => 5 * x + 1) ih
      have m3 := Finset.mem_image_of_mem (fun x => 5 * x + 3) ih
      have m4 := Finset.mem_image_of_mem (fun x => 5 * x + 4) ih
      generalize ω (2 * n) = a; generalize ω (2 * n + 1) = b
      cases a <;> cases b
      · exact Or.inl (Or.inl (by simpa using m0))
      · exact Or.inl (Or.inr (by simpa using m1))
      · exact Or.inr (Or.inl (by simpa using m3))
      · exact Or.inr (Or.inr (by simpa using m4))
    · have hf' : free n = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, if_false, add_zero]
      exact Finset.mem_image_of_mem _ ih

open Classical in
/-- **Trivial count of numerators near the support**, base 5. -/
theorem card_near_leF (free : ℕ → Bool) (q m : ℕ) (hq : 0 < q) (hqm : q ≤ 5 ^ m) (r : ℝ)
    (hr : r ≤ 1 / q) :
    ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |ptF free ω - p / q| < r).card ≤
      3 * 4 ^ freeCount free m := by
  have hsub : ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |ptF free ω - p / q| < r) ⊆
      (HSF free m).biUnion fun h => Finset.Icc (q * h / 5 ^ m) (q * h / 5 ^ m + 2) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨ω, hω⟩ := hp.2
    simp only [Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨hdF free ω m, hdF_mem_HSF free ω m, ?_⟩
    set h := hdF free ω m
    have e1 := hdF_div_le_ptF free ω m
    have e2 := ptF_le_hdF_div free ω m
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have h3 : (0 : ℝ) < 5 ^ m := by positivity
    have hq3 : (q : ℝ) ≤ 5 ^ m := by exact_mod_cast hqm
    have habs := abs_lt.1 hω
    have hrq : r * q ≤ 1 := by rw [le_div_iff₀ hqR] at hr; exact hr
    have hlo : (q : ℝ) * h < ((p : ℝ) + 1) * 5 ^ m := by
      have a1 : (h : ℝ) / 5 ^ m - p / q < r := by linarith
      have a2 : ((h : ℝ) / 5 ^ m - p / q) * (q * 5 ^ m) < r * (q * 5 ^ m) :=
        mul_lt_mul_of_pos_right a1 (by positivity)
      have a3 : ((h : ℝ) / 5 ^ m - p / q) * (q * 5 ^ m) = q * h - p * 5 ^ m := by
        field_simp
      nlinarith
    have hhi : (p : ℝ) * 5 ^ m < q * h + 2 * 5 ^ m := by
      have a1 : (p : ℝ) / q - h / 5 ^ m < r + 1 / 5 ^ m := by linarith
      have a2 : ((p : ℝ) / q - h / 5 ^ m) * (q * 5 ^ m) < (r + 1 / 5 ^ m) * (q * 5 ^ m) :=
        mul_lt_mul_of_pos_right a1 (by positivity)
      have a3 : ((p : ℝ) / q - h / 5 ^ m) * (q * 5 ^ m) = p * 5 ^ m - q * h := by
        field_simp
      have a4 : (r + 1 / 5 ^ m) * (q * 5 ^ m) = r * q * 5 ^ m + q := by field_simp
      nlinarith
    have hlo' : q * h < (p + 1) * 5 ^ m := by exact_mod_cast hlo
    have hhi' : p * 5 ^ m < q * h + 2 * 5 ^ m := by exact_mod_cast hhi
    have hdiv := Nat.div_add_mod (q * h) (5 ^ m)
    have hmod := Nat.mod_lt (q * h) (show 0 < 5 ^ m by positivity)
    constructor
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by positivity)).2 hlo')
    · by_contra hc
      push Not at hc
      have : (q * h / 5 ^ m + 3) * 5 ^ m ≤ p * 5 ^ m := Nat.mul_le_mul_right _ hc
      nlinarith
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ h ∈ HSF free m, (Finset.Icc (q * h / 5 ^ m) (q * h / 5 ^ m + 2)).card
      = ∑ h ∈ HSF free m, 3 := Finset.sum_congr rfl fun h _ => by simp; omega
    _ = 3 * (HSF free m).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 3 * 4 ^ freeCount free m := Nat.mul_le_mul_left _ (card_HSF free m)

end NormalNumbers.CantorFiveExpGeneric
