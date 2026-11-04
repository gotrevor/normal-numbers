/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertRuns
import NormalNumbers.PowerLambertWindow

/-!
# The orbit of a perfect-power Lambert constant has no mass near `0`

A run of `L` equal digits `0` or `b − 1` after position `n` forces
`2 L ≤ Σ_{j<L} c(n+1+j) + ⌊T_{n+L}⌋ + 2^r + 2` (`two_mul_le_of_run`, carry chain; for `b = 2`
the roots `d ≥ 2` carry the argument since every `2^r` consecutive integers contain a multiple
of `2^r`).  Window rigidity caps the window sum by `L + (11/12) L + K + (roots > K)`, so a run
forces `L/12 − K − 2^r − 2 ≤ (roots > K in the window) + T_{n+L}`, whose average over `n` is
`O(L N / K + N)`.  Markov finishes (`powerLambert_nearZero_density_aux`).
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset

/-- `c(m) ≥ 1` for `m ≥ 1` (the root `d = 1`). -/
theorem one_le_powerDivisorCount (r : ℕ) {m : ℕ} (hm : 0 < m) : 1 ≤ powerDivisorCount r m := by
  unfold powerDivisorCount
  apply Finset.card_pos.mpr
  exact ⟨1, by simp [Nat.mem_divisors, hm.ne']⟩

/-- `c(m) ≥ 2` when `2^r ∣ m`, `m ≥ 1` (the roots `1` and `2`). -/
theorem two_le_powerDivisorCount {r m : ℕ} (hr : 1 ≤ r) (hm : 0 < m) (h2 : 2 ^ r ∣ m) :
    2 ≤ powerDivisorCount r m := by
  unfold powerDivisorCount
  have hsub : ({1, 2} : Finset ℕ) ⊆ m.divisors.filter fun d => d ^ r ∣ m := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    simp only [Finset.mem_filter, Nat.mem_divisors]
    rcases hd with rfl | rfl
    · simp [hm.ne']
    · exact ⟨⟨(dvd_pow_self 2 (by omega)).trans h2, hm.ne'⟩, h2⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair (by norm_num)] at this

/-- Reversing the window: `Σ_{i<L} c(n+L−i) = Σ_{j<L} c(n+1+j)`. -/
theorem sum_powerDivisorCount_reflect (r n L : ℕ) :
    (∑ i ∈ range L, powerDivisorCount r (n + L - i)) =
      ∑ j ∈ range L, powerDivisorCount r (n + 1 + j) := by
  rw [← Finset.sum_range_reflect (fun j => powerDivisorCount r (n + 1 + j)) L]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  congr 1
  omega

/-- In base `2` the tail is at least `1`. -/
theorem one_le_powerTail_two (r m : ℕ) : 1 ≤ powerTail 2 r m := by
  unfold powerTail
  refine hasSum_le (fun j => ?_) hasSum_inv_two_pow_succ (summable_powerTail 2 r le_rfl m).hasSum
  push_cast
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast one_le_powerDivisorCount r (by omega : 0 < m + 1 + j)

theorem sum_range_two_pow_add_one (L : ℕ) : (∑ i ∈ range L, 2 ^ i) + 1 = 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **A run forces window mass.**  If the `L` digits after position `n` are all `0` or all
`b − 1`, then `2 L ≤ Σ_{j<L} c(n+1+j) + ⌊T_{n+L}⌋ + 2^r + 2`. -/
theorem two_mul_le_of_run (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) (n L : ℕ)
    (hev : orbit b (powerLambert b r) n < 1 / (b : ℝ) ^ L ∨
      1 - 1 / (b : ℝ) ^ L ≤ orbit b (powerLambert b r) n) :
    2 * L ≤ (∑ j ∈ range L, powerDivisorCount r (n + 1 + j)) +
      ⌊powerTail b r (n + L)⌋₊ + 2 ^ r + 2 := by
  set κ := ⌊powerTail b r (n + L)⌋₊ with hκdef
  set g : ℕ → ℕ := fun i => powerDivisorCount r (n + L - i) with hg
  rw [← sum_powerDivisorCount_reflect]
  change 2 * L ≤ (∑ i ∈ range L, g i) + κ + 2 ^ r + 2
  have hW : powerWindow b r L n = ∑ i ∈ range L, g i * b ^ i := rfl
  have hgpos : ∀ i < L, 1 ≤ g i := fun i hi => one_le_powerDivisorCount r (by omega)
  have hLsum : L ≤ ∑ i ∈ range L, g i := by
    calc L = ∑ i ∈ range L, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hgpos i (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge b 3 with hb2 | hb3
  · -- base 2: the roots `d ≥ 2` carry the argument
    obtain rfl : b = 2 := by omega
    by_cases hL : L < 2 ^ r
    · omega
    push_neg at hL
    have hgi : ∀ i ∈ range L, g i * 2 ^ i = (g i - 1) * 2 ^ i + 2 ^ i := by
      intro i hi
      obtain ⟨t, ht⟩ : ∃ t, g i = t + 1 :=
        ⟨g i - 1, by have := hgpos i (Finset.mem_range.mp hi); omega⟩
      rw [ht, Nat.add_sub_cancel]
      ring
    have hsplitW : (∑ i ∈ range L, g i * 2 ^ i) + 1 =
        (∑ i ∈ range L, (g i - 1) * 2 ^ i) + 2 ^ L := by
      rw [Finset.sum_congr rfl hgi, Finset.sum_add_distrib, ← sum_range_two_pow_add_one L]
      ring
    have hsumh : (∑ i ∈ range L, (g i - 1)) + L = ∑ i ∈ range L, g i := by
      have : (∑ i ∈ range L, g i) = ∑ i ∈ range L, ((g i - 1) + 1) :=
        Finset.sum_congr rfl fun i hi => by have := hgpos i (Finset.mem_range.mp hi); omega
      rw [this, Finset.sum_add_distrib]
      simp
    have hstart : ∃ i < 2 ^ r, 1 ≤ g i - 1 := by
      have hP : 0 < 2 ^ r := by positivity
      refine ⟨(n + L) % 2 ^ r, Nat.mod_lt _ hP, ?_⟩
      have hi : (n + L) % 2 ^ r < L := lt_of_lt_of_le (Nat.mod_lt _ hP) hL
      have hdvd : 2 ^ r ∣ n + L - (n + L) % 2 ^ r := Nat.dvd_sub_mod (n + L)
      have hpos : 0 < n + L - (n + L) % 2 ^ r := by omega
      have := two_le_powerDivisorCount (by omega : 1 ≤ r) hpos hdvd
      simp only [hg]
      omega
    rcases hev with h0 | h1
    · have hd := dvd_powerWindow_of_orbit_lt 2 r le_rfl (by omega) n L h0
      have hκ : 1 ≤ κ := Nat.le_floor (by exact_mod_cast one_le_powerTail_two r (n + L))
      have hd' : 2 ^ L ∣ (∑ i ∈ range L, (g i - 1) * 2 ^ i) + (κ - 1) := by
        have he : powerWindow 2 r L n + κ =
            (∑ i ∈ range L, (g i - 1) * 2 ^ i) + (κ - 1) + 2 ^ L := by
          rw [hW]; omega
        rw [he] at hd
        exact (Nat.dvd_add_left (dvd_refl _)).mp hd
      have := carry_le_of_dvd (b := 2) (by norm_num) L (fun i => g i - 1) (κ - 1) (2 ^ r) hd'
        (Or.inr hstart)
      norm_num at this
      omega
    · have hd := dvd_powerWindow_succ_of_le_orbit 2 r le_rfl (by omega) n L h1
      have hd' : 2 ^ L ∣ (∑ i ∈ range L, (g i - 1) * 2 ^ i) + κ := by
        have he : powerWindow 2 r L n + κ + 1 =
            (∑ i ∈ range L, (g i - 1) * 2 ^ i) + κ + 2 ^ L := by
          rw [hW]; omega
        rw [he] at hd
        exact (Nat.dvd_add_left (dvd_refl _)).mp hd
      have := carry_le_of_dvd (b := 2) (by norm_num) L (fun i => g i - 1) κ (2 ^ r) hd'
        (Or.inr hstart)
      norm_num at this
      omega
  · -- base `b ≥ 3`: every digit carries at least `b − 1 ≥ 2`
    rcases Nat.eq_zero_or_pos L with hL0 | hL0
    · subst hL0; simp
    have hb1 : 2 ≤ b - 1 := by omega
    rcases hev with h0 | h1
    · have hd := dvd_powerWindow_of_orbit_lt b r hb (by omega) n L h0
      rw [hW] at hd
      have := carry_le_of_dvd (b := b) (by omega) L g κ 1 hd (Or.inr ⟨0, by omega, hgpos 0 hL0⟩)
      have hm : 2 * (L - 1) ≤ (b - 1) * (L - 1) := Nat.mul_le_mul_right _ hb1
      generalize (b - 1) * (L - 1) = P at this hm
      generalize 2 ^ r = t
      omega
    · have hd := dvd_powerWindow_succ_of_le_orbit b r hb (by omega) n L h1
      rw [hW] at hd
      have := carry_le_of_dvd_succ (b := b) (by omega) L g κ hd
      have hm : 2 * L ≤ (b - 1) * L := Nat.mul_le_mul_right _ hb1
      generalize (b - 1) * L = P at this hm
      generalize 2 ^ r = t
      omega

/-- **Markov (counting form).**  `θ · #{n ∈ s : θ ≤ f n} ≤ Σ_{n ∈ s} f n` for `f ≥ 0`. -/
theorem mul_card_filter_le_sum {s : Finset ℕ} {f : ℕ → ℝ} (θ : ℝ) (hf : ∀ n ∈ s, 0 ≤ f n) :
    θ * ((s.filter fun n => θ ≤ f n).card : ℝ) ≤ ∑ n ∈ s, f n := by
  calc θ * ((s.filter fun n => θ ≤ f n).card : ℝ) = ∑ n ∈ s.filter (fun n => θ ≤ f n), θ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ n ∈ s.filter (fun n => θ ≤ f n), f n :=
        Finset.sum_le_sum fun n hn => (Finset.mem_filter.mp hn).2
    _ ≤ ∑ n ∈ s, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n hn _ => hf n hn

open Classical in
/-- **Near-zero density** (the statement frozen in `PowerLambertFrequenciesExist.lean`). -/
theorem powerLambert_nearZero_density_aux (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ᶠ N : ℕ in atTop,
      (((range N).filter fun n =>
        orbit b (powerLambert b r) n < 1 / (b : ℝ) ^ L ∨
          1 - 1 / (b : ℝ) ^ L ≤ orbit b (powerLambert b r) n).card : ℝ) ≤ ε * N := by
  intro ε hε
  set K : ℕ := ⌈192 / ε⌉₊ with hKdef
  set L : ℕ := 24 * (K + 2 ^ r + 2) + K with hLdef
  have hK : 192 / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hL : 192 / ε ≤ (L : ℝ) := hK.trans (by exact_mod_cast (by omega : K ≤ L))
  refine ⟨L, Filter.eventually_atTop.mpr ⟨L + 2, fun N hN => ?_⟩⟩
  set E := (range N).filter fun n =>
    orbit b (powerLambert b r) n < 1 / (b : ℝ) ^ L ∨
      1 - 1 / (b : ℝ) ^ L ≤ orbit b (powerLambert b r) n with hEdef
  set θ : ℝ := (L : ℝ) / 12 - K - 2 ^ r - 2 with hθdef
  set Φ : ℕ → ℝ := fun n =>
    ((∑ j ∈ range L, bigRootCount r K (n + 1 + j) : ℕ) : ℝ) + powerTail b r (n + L) with hΦ
  -- a run forces `θ ≤ Φ n`
  have hev : ∀ n ∈ E, θ ≤ Φ n := by
    intro n hn
    have h1 := two_mul_le_of_run b r hb hr n L (Finset.mem_filter.mp hn).2
    have h1' : (2 : ℝ) * L ≤ ((∑ j ∈ range L, powerDivisorCount r (n + 1 + j) : ℕ) : ℝ) +
        (⌊powerTail b r (n + L)⌋₊ : ℝ) + 2 ^ r + 2 := by exact_mod_cast h1
    have h2 := sum_window_le hr K n L
    have h3 : (⌊powerTail b r (n + L)⌋₊ : ℝ) ≤ powerTail b r (n + L) :=
      Nat.floor_le (powerTail_nonneg _ _ _)
    simp only [hθdef, hΦ]
    linarith
  have hsub : E ⊆ (range N).filter fun n => θ ≤ Φ n := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hev n hn⟩
  have hΦ0 : ∀ n ∈ range N, 0 ≤ Φ n := fun n _ => by
    simp only [hΦ]; have := powerTail_nonneg b r (n + L); positivity
  have hmarkov := mul_card_filter_le_sum θ hΦ0
  -- the average of `Φ`
  have hB := sum_range_bigRoot_window_le hr K N L
  have hT : (∑ n ∈ range N, powerTail b r (n + L)) ≤ 2 * (N + L + 2) :=
    sum_range_tail_le hb (powerDivisorCount r) (powerDivisorCount_le_self r) (by norm_num)
      (sum_powerDivisorCount_le hr) N L
  have hsumΦ : (∑ n ∈ range N, Φ n) ≤ L * (N + L) * (2 / ((K : ℝ) + 1)) + 2 * (N + L + 2) := by
    simp only [hΦ]
    rw [Finset.sum_add_distrib, ← Nat.cast_sum]
    linarith
  -- arithmetic
  have hNL : (L : ℝ) + 2 ≤ N := by exact_mod_cast hN
  have hθL : (L : ℝ) / 24 ≤ θ := by
    have : ((24 * (K + 2 ^ r + 2) : ℕ) : ℝ) ≤ L := by exact_mod_cast (by omega)
    push_cast at this
    simp only [hθdef]
    linarith
  have hcardE : (E.card : ℝ) ≤ ((range N).filter fun n => θ ≤ Φ n).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  have hK1 : 2 / ((K : ℝ) + 1) ≤ ε / 96 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := (div_le_iff₀ hε).mp hK
    nlinarith
  have hLε : 192 ≤ (L : ℝ) * ε := by
    have := (div_le_iff₀ hε).mp hL
    linarith
  have hS : L * (N + L) * (2 / ((K : ℝ) + 1)) + 2 * (N + L + 2) ≤ (L : ℝ) / 24 * (ε * N) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have e1 : (L : ℝ) * (N + L) * (2 / ((K : ℝ) + 1)) ≤ L * (2 * N) * (ε / 96) := by
      apply mul_le_mul _ hK1 (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) hLpos.le
    have e2 : (2 : ℝ) * (N + L + 2) ≤ 4 * N := by linarith
    have e3 : (4 : ℝ) * N ≤ (L * ε) / 48 * N := by
      apply mul_le_mul_of_nonneg_right _ hN0
      linarith
    nlinarith
  have hfin : (L : ℝ) / 24 * E.card ≤ (L : ℝ) / 24 * (ε * N) := by
    have hθpos : 0 ≤ θ := le_trans (by positivity) hθL
    calc (L : ℝ) / 24 * E.card ≤ θ * E.card := by
          apply mul_le_mul_of_nonneg_right hθL (by positivity)
      _ ≤ θ * ((range N).filter fun n => θ ≤ Φ n).card :=
          mul_le_mul_of_nonneg_left hcardE hθpos
      _ ≤ _ := hmarkov
      _ ≤ _ := hsumΦ
      _ ≤ _ := hS
  exact le_of_mul_le_mul_left hfin (by positivity)

end NormalNumbers.ArithmeticDisjunctivity
