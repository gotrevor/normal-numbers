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

/-! ## Digit-structure lemmas -/

theorem hdF_zero_ext (free : ℕ → Bool) (ω : ℕ → Bool) (a : ℕ) :
    ∀ E, a ≤ E → (∀ i, a ≤ i → i < E → ptDigitF free ω i = 0) →
      hdF free ω E = 5 ^ (E - a) * hdF free ω a := by
  intro E
  induction E with
  | zero => intro h _; obtain rfl : a = 0 := by omega
            simp
  | succ E ih =>
    intro hE hz
    rcases Nat.eq_or_lt_of_le hE with h | h
    · subst h; simp
    · rw [hdF_succ, ih (by omega) (fun i h1 h2 => hz i h1 (by omega)), hz E (by omega) (by omega),
        show E + 1 - a = (E - a) + 1 by omega, pow_succ]
      ring

theorem digitsF_zero_of_dvd (free : ℕ → Bool) (ω : ℕ → Bool) :
    ∀ j a, j ≤ a → 5 ^ j ∣ hdF free ω a → ∀ i, a - j ≤ i → i < a → ptDigitF free ω i = 0 := by
  intro j
  induction j with
  | zero => intro a _ _ i h1 h2; omega
  | succ j ih =>
    intro a hja hdvd i h1 h2
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [hdF_succ] at hdvd
    have h3 : 5 ∣ 5 * hdF free ω a' + ptDigitF free ω a' :=
      (dvd_pow_self 5 (by omega)).trans hdvd
    have hd0 : ptDigitF free ω a' = 0 := by
      have := ptDigitF_le_four free ω a'
      omega
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.1 h2) with hi | hi
    · rw [hi]; exact hd0
    · rw [hd0, add_zero, pow_succ, mul_comm 5] at hdvd
      exact ih a' (by omega) (Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd) i (by omega) hi

theorem pow_dvd_of_eqF {pp P q a m : ℕ} (hq : q ≠ 0) (hq5 : q < 5 ^ (m + 1))
    (h : pp * 5 ^ a = P * q) : 5 ^ (a - m) ∣ P := by
  obtain ⟨v, q', hq', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq 5 (by norm_num)
  have hv : v ≤ m := by
    by_contra hc
    have : 5 ^ (m + 1) ≤ 5 ^ v * q' :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hq)))
    omega
  rcases le_or_gt a v with hav | hav
  · rw [show a - m = 0 by omega]; simp
  have hdvd : 5 ^ (a - v) * 5 ^ v ∣ P * q' * 5 ^ v := by
    rw [← pow_add, show a - v + v = a by omega]
    exact ⟨pp, by rw [mul_comm (P * q')]; linarith [h]⟩
  have h2 : 5 ^ (a - v) ∣ P * q' := Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd
  have hcop : Nat.Coprime (5 ^ (a - v)) q' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hq')
  exact (Nat.pow_dvd_pow 5 (by omega)).trans (hcop.dvd_of_dvd_mul_right h2)

/-! ## The prefix test at scale `m` -/

/-- `|fNum/5^{L+1} − pp/q| ≤ 3·5^{-(L+1)}` with `q ∈ [5^m, 5^{m+1})`. -/
def hitCondF (free : ℕ → Bool) (m L : ℕ) (p : List Bool) (q pp : ℕ) : Prop :=
  5 ^ m ≤ q ∧ fNum free (L + 1) p * q ≤ pp * 5 ^ (L + 1) + 3 * q ∧
    pp * 5 ^ (L + 1) ≤ fNum free (L + 1) p * q + 3 * q

instance (free : ℕ → Bool) (m L : ℕ) (p : List Bool) (q pp : ℕ) :
    Decidable (hitCondF free m L p q pp) := by unfold hitCondF; infer_instance

def hitCntF (free : ℕ → Bool) (m L : ℕ) (p : List Bool) : ℕ :=
  ((List.range (5 ^ (m + 1))).map fun q =>
    ((List.range (q + 1)).map fun pp => if hitCondF free m L p q pp then 1 else 0).sum).sum

/-- The scale-`m` test, on a prefix of `2(L+1)` coins. -/
def hitBF (free : ℕ → Bool) (m L : ℕ) (p : List Bool) : Bool := decide (0 < hitCntF free m L p)

theorem fNum_pre (free : ℕ → Bool) (ω : ℕ → Bool) (N : ℕ) :
    fNum free N (pre ω (2 * N)) = hdF free ω N := by
  rw [fNum_eq]
  refine hdF_congr _ _ _ N fun j hj => ?_
  simp only [ptDigitF, getD_pre' ω, if_pos (show 2 * j < 2 * N by omega),
    if_pos (show 2 * j + 1 < 2 * N by omega)]

theorem hitBF_iff (free : ℕ → Bool) (m L : ℕ) (p : List Bool) :
    hitBF free m L p = true ↔ ∃ q pp, q < 5 ^ (m + 1) ∧ pp ≤ q ∧ hitCondF free m L p q pp := by
  rw [hitBF, decide_eq_true_eq, hitCntF, ComputableNormalB.list_sum_range_map]
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

theorem hitCondF_pre_iff (free : ℕ → Bool) (ω : ℕ → Bool) (m L q pp : ℕ) (hq : 0 < q) :
    (|(hdF free ω (L + 1) : ℝ) / 5 ^ (L + 1) - pp / q| ≤ 3 / 5 ^ (L + 1)) ↔
      (fNum free (L + 1) (pre ω (2 * (L + 1))) * q ≤ pp * 5 ^ (L + 1) + 3 * q ∧
        pp * 5 ^ (L + 1) ≤ fNum free (L + 1) (pre ω (2 * (L + 1))) * q + 3 * q) := by
  rw [fNum_pre]
  set h := hdF free ω (L + 1)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 5 ^ (L + 1) := by positivity
  have e : (h : ℝ) / 5 ^ (L + 1) - pp / q = ((h : ℝ) * q - pp * 5 ^ (L + 1)) / (q * 5 ^ (L + 1)) := by
    field_simp
  have hD : (0:ℝ) < q * 5 ^ (L + 1) := by positivity
  rw [e, abs_div, abs_of_pos hD, div_le_div_iff₀ hD h3,
    show (3:ℝ) * (q * 5 ^ (L + 1)) = (3 * q) * 5 ^ (L + 1) by ring]
  rw [show (|(h : ℝ) * q - pp * 5 ^ (L + 1)| * 5 ^ (L + 1) ≤ (3 * q) * 5 ^ (L + 1)) ↔
      |(h : ℝ) * q - pp * 5 ^ (L + 1)| ≤ 3 * q from
    ⟨fun k => le_of_mul_le_mul_right k h3, fun k => mul_le_mul_of_nonneg_right k h3.le⟩, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (h : ℝ) * q ≤ pp * 5 ^ (L + 1) + 3 * q := by nlinarith
      exact_mod_cast this
    · have : (pp : ℝ) * 5 ^ (L + 1) ≤ h * q + 3 * q := by nlinarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (h : ℝ) * q ≤ pp * 5 ^ (L + 1) + 3 * q := by exact_mod_cast h1
    have h2' : (pp : ℝ) * 5 ^ (L + 1) ≤ h * q + 3 * q := by exact_mod_cast h2
    constructor <;> nlinarith

/-- **Firing**: a rational at scale `m` within `2·5^{-(L+1)}` trips the test. -/
theorem hitBF_of_near (free : ℕ → Bool) (ω : ℕ → Bool) (m L q pp : ℕ) (hq1 : 5 ^ m ≤ q)
    (hq2 : q < 5 ^ (m + 1)) (hpp : pp ≤ q)
    (h : |ptF free ω - pp / q| ≤ 2 / 5 ^ (L + 1)) :
    hitBF free m L (pre ω (2 * (L + 1))) = true := by
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hq1
  rw [hitBF_iff]
  refine ⟨q, pp, hq2, hpp, hq1, (hitCondF_pre_iff free ω m L q pp hq).1 ?_⟩
  have e1 := hdF_div_le_ptF free ω (L + 1)
  have e2 := ptF_le_hdF_div free ω (L + 1)
  have k : (3:ℝ) / 5 ^ (L + 1) = 2 / 5 ^ (L + 1) + 1 / 5 ^ (L + 1) := by ring
  rw [abs_le] at h ⊢
  rw [k]
  constructor <;> linarith [h.1, h.2]

/-- **Soundness**: a tripped test gives a rational at scale `m` within `4·5^{-(L+1)}`. -/
theorem near_of_hitBF (free : ℕ → Bool) (ω : ℕ → Bool) (m L : ℕ)
    (h : hitBF free m L (pre ω (2 * (L + 1))) = true) :
    ∃ q pp : ℕ, 5 ^ m ≤ q ∧ q < 5 ^ (m + 1) ∧ pp ≤ q ∧
      |ptF free ω - pp / q| ≤ 4 / 5 ^ (L + 1) := by
  obtain ⟨q, pp, hq2, hpp, hq1, hc⟩ := (hitBF_iff free m L _).1 h
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hq1
  refine ⟨q, pp, hq1, hq2, hpp, ?_⟩
  have h' := (hitCondF_pre_iff free ω m L q pp hq).2 hc
  have e1 := hdF_div_le_ptF free ω (L + 1)
  have e2 := ptF_le_hdF_div free ω (L + 1)
  rw [abs_le] at h' ⊢
  have k : (4:ℝ) / 5 ^ (L + 1) = 3 / 5 ^ (L + 1) + 1 / 5 ^ (L + 1) := by ring
  rw [k]
  constructor <;> linarith [h'.1, h'.2]

/-! ## Masses of the test -/

/-- **Borel–Cantelli mass of the scale-`m` test**: `≤ 36·5^m·4^{-W}`, `W` the free count of
`[m+1, L-1)`. -/
theorem hit_mass_bcF (free : ℕ → Bool) (m L : ℕ) (hL : m + 2 ≤ L) :
    coins.real {ω | hitBF free m L (pre ω (2 * (L + 1))) = true} ≤
      36 * 5 ^ m * (1 / 4 : ℝ) ^ fc free (m + 1) (L - 1) := by
  classical
  set r : ℝ := 5 / 5 ^ (L + 1) with hr
  set near : ℕ → Finset ℕ := fun q =>
    (Finset.range (q + 1)).filter fun pp : ℕ => ∃ ω, |ptF free ω - pp / q| < r
  have hsub : {ω | hitBF free m L (pre ω (2 * (L + 1))) = true} ⊆
      ⋃ q ∈ Finset.Ico (5 ^ m) (5 ^ (m + 1)), ⋃ pp ∈ near q, {ω | |ptF free ω - pp / q| < r} := by
    intro ω hω
    obtain ⟨q, pp, hq1, hq2, hpp, hle⟩ := near_of_hitBF free ω m L hω
    have hlt : |ptF free ω - pp / q| < r := by
      rw [hr]; refine lt_of_le_of_lt hle ?_
      exact div_lt_div_of_pos_right (by norm_num) (by positivity)
    simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_setOf_eq]
    refine ⟨q, ⟨hq1, hq2⟩, pp, ?_, hlt⟩
    simp only [near, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ω, hlt⟩
  have hball : ∀ q pp : ℕ, coins.real {ω | |ptF free ω - pp / q| < r} ≤
      3 * (1 / 4 : ℝ) ^ freeCount free (L - 1) := by
    intro q pp
    refine ball_leF free _ r (L - 1) ?_
    rw [show L - 1 + 1 = L by omega, hr, pow_succ]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 5) L]
  have hcard : ∀ q ∈ Finset.Ico (5 ^ m) (5 ^ (m + 1)), (near q).card ≤ 3 * 4 ^ freeCount free (m + 1) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq.1
    refine card_near_leF free q (m + 1) hq0 hq.2.le r ?_
    rw [hr, div_le_div_iff₀ (by positivity) (by exact_mod_cast hq0)]
    have h1 : (q : ℝ) < 5 ^ (m + 1) := by exact_mod_cast hq.2
    have h2 : (5 : ℝ) ^ (m + 1) * 5 ≤ 5 ^ (L + 1) := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hF : freeCount free (L - 1) = freeCount free (m + 1) + fc free (m + 1) (L - 1) :=
    freeCount_sub free (by omega)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ q ∈ Finset.Ico (5 ^ m) (5 ^ (m + 1)),
        coins.real (⋃ pp ∈ near q, {ω | |ptF free ω - pp / q| < r})
      ≤ ∑ q ∈ Finset.Ico (5 ^ m) (5 ^ (m + 1)),
          (3 * 4 ^ freeCount free (m + 1) : ℝ) * (3 * (1 / 4 : ℝ) ^ freeCount free (L - 1)) := by
        refine Finset.sum_le_sum fun q hq => (measureReal_biUnion_finset_le _ _).trans ?_
        refine (Finset.sum_le_sum fun pp _ => hball q pp).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard q hq
    _ = 36 * 5 ^ m * (1 / 4 : ℝ) ^ fc free (m + 1) (L - 1) := by
        have e : 5 ^ (m + 1) - 5 ^ m = 4 * 5 ^ m := by rw [pow_succ]; omega
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, e, hF, pow_add (1 / 4 : ℝ)]
        push_cast
        have : (4 : ℝ) ^ freeCount free (m + 1) * (1 / 4) ^ freeCount free (m + 1) = 1 := by
          rw [← mul_pow]; norm_num
        calc (4 * 5 ^ m : ℝ) * (3 * 4 ^ freeCount free (m + 1) * (3 *
              ((1 / 4) ^ freeCount free (m + 1) * (1 / 4) ^ fc free (m + 1) (L - 1))))
            = 36 * 5 ^ m * (4 ^ freeCount free (m + 1) * (1 / 4) ^ freeCount free (m + 1)) *
              (1 / 4) ^ fc free (m + 1) (L - 1) := by ring
          _ = _ := by rw [this, mul_one]

/-- Triangle inequality at a forced approximation, base 5. -/
theorem abs_sub_ge_of_nearF (x : ℝ) (P a E q : ℕ) (p : ℤ) (hq : 0 < q)
    (hx : |x - P / 5 ^ a| ≤ 1 / 5 ^ E) (hne : (p : ℝ) / q ≠ P / 5 ^ a)
    (hqE : 2 * q * 5 ^ a ≤ 5 ^ E) :
    1 / (2 * (q : ℝ) * 5 ^ a) ≤ |x - p / q| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 5 ^ a := by positivity
  set n : ℤ := p * 5 ^ a - P * q with hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hne
    have : (p : ℝ) * 5 ^ a = P * q := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h0
      simp only [hn] at this; push_cast at this; linarith
    field_simp; linarith
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  have hdiff : (p : ℝ) / q - P / 5 ^ a = n / (q * 5 ^ a) := by
    simp only [hn]; push_cast; field_simp
  have hge : 1 / ((q : ℝ) * 5 ^ a) ≤ |(p : ℝ) / q - P / 5 ^ a| := by
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * 5 ^ a)]
    exact div_le_div_of_nonneg_right hn1 (by positivity)
  have hE : 1 / (5 : ℝ) ^ E ≤ 1 / (2 * q * 5 ^ a) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hqE
  have htri : |(p : ℝ) / q - P / 5 ^ a| ≤ |x - p / q| + |x - P / 5 ^ a| := by
    rw [abs_sub_comm x]; exact abs_sub_le _ _ _
  have : 1 / ((q : ℝ) * 5 ^ a) = 2 * (1 / (2 * q * 5 ^ a)) := by field_simp
  linarith

/-- **Triangle-range mass of the scale-`m` test**, base 5. -/
theorem hit_mass_triF (free : ℕ → Bool) (m L a E : ℕ)
    (hz : ∀ i, a ≤ i → i < E → free i = false) (haE : m + a + 2 ≤ E) (hL : m + a + 3 ≤ L) :
    coins.real {ω | hitBF free m L (pre ω (2 * (L + 1))) = true} ≤ (1 / 4 : ℝ) ^ fc free m L := by
  rw [← coins_zero_windowF free m L (by omega)]
  refine measureReal_mono fun ω hω => ?_
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨q, pp, hq1, hq2, hpp, hle⟩ := near_of_hitBF free ω m L hω
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  set P := hdF free ω a
  have hzd : ∀ i, a ≤ i → i < E → ptDigitF free ω i = 0 := fun i h1 h2 => by
    simp [ptDigitF, hz i h1 h2]
  have hE := hdF_zero_ext free ω a E (by omega) hzd
  have hsplitE := ptF_split free ω E
  have hPE : (hdF free ω E : ℝ) / 5 ^ E = P / 5 ^ a := by
    rw [hE]; push_cast
    rw [show (5 : ℝ) ^ E = 5 ^ (E - a) * 5 ^ a by rw [← pow_add]; congr 1; omega]
    field_simp
    rfl
  have hnear : |ptF free ω - P / 5 ^ a| ≤ 1 / 5 ^ E := by
    rw [hsplitE, hPE, add_sub_cancel_left, abs_of_nonneg (tlF_nonneg _ _ _)]; exact tlF_le _ _ _
  have heq : (pp : ℝ) / q = P / 5 ^ a := by
    by_contra hne
    have hqE : 2 * q * 5 ^ a ≤ 5 ^ E := by
      have : 2 * q * 5 ^ a ≤ 2 * 5 ^ (m + 1) * 5 ^ a := by gcongr
      refine this.trans ?_
      rw [mul_assoc, ← pow_add]
      calc 2 * 5 ^ (m + 1 + a) ≤ 5 * 5 ^ (m + 1 + a) := by omega
        _ = 5 ^ (m + a + 2) := by rw [← pow_succ']; congr 1; omega
        _ ≤ 5 ^ E := Nat.pow_le_pow_right (by norm_num) haE
    have h1 := abs_sub_ge_of_nearF (ptF free ω) P a E q (pp : ℤ) hq0 hnear (by simpa using hne) hqE
    simp only [Int.cast_natCast] at h1
    have h2 : (4 : ℝ) / 5 ^ (L + 1) < 1 / (2 * q * 5 ^ a) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have : (q : ℝ) < 5 ^ (m + 1) := by exact_mod_cast hq2
      have h3 : (5 : ℝ) ^ (m + 1) * 5 ^ a * 25 ≤ 5 ^ (L + 1) := by
        rw [← pow_add, show (25 : ℝ) = 5 ^ 2 by norm_num, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : (0 : ℝ) < 5 ^ a := by positivity
      nlinarith
    linarith
  have hsplit := ptF_split free ω a
  have htl : tlF free ω a < 1 / (5 : ℝ) ^ L := by
    have : ptF free ω - pp / q = tlF free ω a := by rw [heq, hsplit]; ring
    rw [this, abs_of_nonneg (tlF_nonneg _ _ _)] at hle
    refine lt_of_le_of_lt hle ?_
    rw [pow_succ, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 5) L]
  have hza := ptDigitF_zero_of_tl_lt free ω a L htl
  have hzm : ∀ i, m ≤ i → i < a → ptDigitF free ω i = 0 := by
    intro i h1 h2
    have hnat : pp * 5 ^ a = P * q := by
      have : (pp : ℝ) * 5 ^ a = P * q := by
        field_simp at heq; linarith
      exact_mod_cast this
    have hdvd := pow_dvd_of_eqF (m := m) hq0.ne' hq2 hnat
    exact digitsF_zero_of_dvd free ω (a - m) a (by omega) hdvd i (by omega) h2
  intro i h1 h2 hf
  have hd0 : ptDigitF free ω i = 0 := by
    rcases lt_or_ge i a with h | h
    · exact hzm i h1 h
    · exact hza i h h2
  unfold ptDigitF at hd0
  rw [if_pos hf] at hd0
  revert hd0
  generalize ω (2 * i) = x; generalize ω (2 * i + 1) = y
  cases x <;> cases y <;> simp

end NormalNumbers.CantorFiveExpGeneric
