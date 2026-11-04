/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertRich

/-!
# Window sums of the power-divisor count: rigidity and averages

* `sum_card_powerDivisors_filter_le`: `Σ_{m ≤ X} #{d : d^r ∣ m, P d} ≤ X Σ_{d ≤ X, P d} d^{-2}`.
* `sum_range_tail_le`: a Lambert tail of a coefficient sequence of mean `≤ λ` has
  `Σ_{n<N} T_{n+k} ≤ λ (N + k + 2)`.
* `sum_window_le`: in every window of length `L` the power-divisor mass is at most
  `L + (11/12) L + K` plus the mass of the roots `d > K` (rigidity of small roots).
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

/-- **Swap the divisor sum.**  For `r ≥ 2` and any predicate `P` on roots,
`Σ_{0<m≤X} #{d ∣ m : d^r ∣ m ∧ P d} ≤ X · Σ_{0<d≤X, P d} 1/d²`. -/
theorem sum_card_powerDivisors_filter_le {r : ℕ} (hr : 2 ≤ r) (P : ℕ → Prop)
    [DecidablePred P] (X : ℕ) :
    ((∑ m ∈ Ioc 0 X, (m.divisors.filter fun d => d ^ r ∣ m ∧ P d).card : ℕ) : ℝ) ≤
      X * ∑ d ∈ (Ioc 0 X).filter P, ((d : ℝ) ^ 2)⁻¹ := by
  classical
  have h1 : ∀ m ∈ Ioc 0 X, (m.divisors.filter fun d => d ^ r ∣ m ∧ P d) =
      (Ioc 0 X).filter (fun d => d ^ r ∣ m ∧ P d) := by
    intro m hm
    obtain ⟨hm0, hmX⟩ := Finset.mem_Ioc.mp hm
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hdm, _⟩, hdr, hP⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdm hm0, (Nat.le_of_dvd hm0 hdm).trans hmX⟩, hdr, hP⟩
    · rintro ⟨_, hdr, hP⟩
      exact ⟨⟨(dvd_pow_self d (by omega)).trans hdr, by omega⟩, hdr, hP⟩
  have h2 : (∑ m ∈ Ioc 0 X, (m.divisors.filter fun d => d ^ r ∣ m ∧ P d).card) =
      ∑ d ∈ (Ioc 0 X).filter P, X / d ^ r := by
    rw [Finset.sum_congr rfl fun m hm => by rw [h1 m hm]]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with hP
    · simp only [hP, and_true]
      rw [← Finset.card_filter, Nat.Ioc_filter_dvd_card_eq_div]
    · simp [hP]
  rw [h2, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
  calc ((X / d ^ r : ℕ) : ℝ) ≤ (X : ℝ) / ((d ^ r : ℕ) : ℝ) := Nat.cast_div_le
    _ ≤ (X : ℝ) / (d : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        push_cast
        exact pow_le_pow_right₀ (by exact_mod_cast hd1) hr
    _ = X * ((d : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-- Roots in `(K, X]`: `Σ 1/d² ≤ 2/(K+1)`. -/
theorem sum_filter_lt_inv_sq_le (K X : ℕ) :
    (∑ d ∈ (Ioc 0 X).filter (fun d => K < d), ((d : ℝ) ^ 2)⁻¹) ≤ 2 / ((K : ℝ) + 1) := by
  calc (∑ d ∈ (Ioc 0 X).filter (fun d => K < d), ((d : ℝ) ^ 2)⁻¹)
      ≤ ∑ d ∈ Ioo K (X + 1), ((d : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hd
          simp only [Finset.mem_Ioo]
          omega
        · intro _ _ _; positivity
    _ ≤ 2 / ((K : ℝ) + 1) := sum_Ioo_inv_sq_le _ _

/-- The mean of the power-divisor count is at most `2`: `Σ_{0<m≤X} c(m) ≤ 2X`. -/
theorem sum_powerDivisorCount_le {r : ℕ} (hr : 2 ≤ r) (X : ℕ) :
    ((∑ m ∈ Ioc 0 X, powerDivisorCount r m : ℕ) : ℝ) ≤ 2 * X := by
  have h := sum_card_powerDivisors_filter_le hr (fun d => 0 < d) X
  have heq : (∑ m ∈ Ioc 0 X, powerDivisorCount r m) =
      ∑ m ∈ Ioc 0 X, (m.divisors.filter fun d => d ^ r ∣ m ∧ 0 < d).card := by
    refine Finset.sum_congr rfl fun m hm => ?_
    unfold powerDivisorCount
    congr 1
    apply Finset.filter_congr
    intro d hd
    have := Nat.pos_of_mem_divisors hd
    simp [this]
  rw [heq]
  refine h.trans ?_
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := sum_filter_lt_inv_sq_le 0 X
  simpa using this

/-- A shifted sum below `N` sits inside an initial segment. -/
theorem sum_range_shift_le (f : ℕ → ℕ) (N s : ℕ) (hs : 1 ≤ s) :
    (∑ n ∈ range N, f (n + s)) ≤ ∑ m ∈ Ioc 0 (N + s), f m := by
  rw [show (∑ n ∈ range N, f (n + s)) = ∑ m ∈ (range N).map (addRightEmbedding s), f m by
    rw [Finset.sum_map]; rfl]
  apply Finset.sum_le_sum_of_subset
  intro m hm
  simp only [Finset.mem_map, Finset.mem_range, addRightEmbedding_apply] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  simp only [Finset.mem_Ioc]
  omega

/-- `Σ_j 1/2^{j+1} = 1`. -/
theorem hasSum_inv_two_pow_succ : HasSum (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 1)) 1 := by
  convert hasSum_geometric_two' 1 using 1
  funext j
  rw [pow_succ]
  field_simp

/-- `Σ_j j/2^{j+1} = 1`. -/
theorem hasSum_mul_inv_two_pow_succ : HasSum (fun j : ℕ => (j : ℝ) / 2 ^ (j + 1)) 1 := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2)
    (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)).div_const 2
  have e1 : (fun j : ℕ => (j : ℝ) / 2 ^ (j + 1)) = fun i : ℕ => (i : ℝ) * (1 / 2) ^ i / 2 := by
    funext j
    rw [pow_succ, one_div_pow]
    field_simp
  have e2 : (1 / 2 / (1 - 1 / 2) ^ 2 / 2 : ℝ) = 1 := by norm_num
  rw [e2] at h
  rw [e1]
  exact h

/-- **Averaged Lambert tail.**  If `f m ≤ m` and `Σ_{0<m≤X} f m ≤ λ X` for all `X`, then
`Σ_{n<N} Σ_j f(n+k+1+j)/b^{j+1} ≤ λ (N + k + 2)`. -/
theorem sum_range_tail_le {b : ℕ} (hb : 2 ≤ b) (f : ℕ → ℕ) (hf : ∀ m, f m ≤ m) {lam : ℝ}
    (hlam : 0 ≤ lam) (hmean : ∀ X, ((∑ m ∈ Ioc 0 X, f m : ℕ) : ℝ) ≤ lam * X) (N k : ℕ) :
    (∑ n ∈ range N, ∑' j : ℕ, (f (n + k + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) ≤
      lam * (N + k + 2) := by
  have hs : ∀ n, Summable (fun j : ℕ => (f (n + k + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) :=
    fun n => summable_tail_of_le b hb (n + k) f fun j => hf _
  rw [summable_sum_tsum_range N _ hs]
  have hR : HasSum (fun j : ℕ => lam * (((N + k + 1 : ℕ) : ℝ) * (1 / 2 ^ (j + 1)) +
      (j : ℝ) / 2 ^ (j + 1))) (lam * (((N + k + 1 : ℕ) : ℝ) * 1 + 1)) :=
    ((hasSum_inv_two_pow_succ.mul_left _).add hasSum_mul_inv_two_pow_succ).mul_left lam
  have hterm : ∀ j : ℕ, (∑ n ∈ range N, (f (n + k + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) ≤
      lam * (((N + k + 1 : ℕ) : ℝ) * (1 / 2 ^ (j + 1)) + (j : ℝ) / 2 ^ (j + 1)) := by
    intro j
    rw [← Finset.sum_div]
    have hb2 : (2 : ℝ) ^ (j + 1) ≤ (b : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) _
    have hsum : ((∑ n ∈ range N, f (n + k + 1 + j) : ℕ) : ℝ) ≤
        lam * ((N + k + 1 : ℕ) + j) := by
      have h1 : (∑ n ∈ range N, f (n + k + 1 + j)) ≤ ∑ m ∈ Ioc 0 (N + (k + 1 + j)), f m := by
        have := sum_range_shift_le f N (k + 1 + j) (by omega)
        simpa only [← add_assoc] using this
      calc ((∑ n ∈ range N, f (n + k + 1 + j) : ℕ) : ℝ)
          ≤ ((∑ m ∈ Ioc 0 (N + (k + 1 + j)), f m : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ lam * ((N + (k + 1 + j) : ℕ) : ℝ) := hmean _
        _ = lam * ((N + k + 1 : ℕ) + j) := by push_cast; ring
    push_cast at hsum ⊢
    calc (∑ n ∈ range N, (f (n + k + 1 + j) : ℝ)) / (b : ℝ) ^ (j + 1)
        ≤ (lam * ((N : ℝ) + k + 1 + j)) / (b : ℝ) ^ (j + 1) :=
          div_le_div_of_nonneg_right hsum (by positivity)
      _ ≤ (lam * ((N : ℝ) + k + 1 + j)) / (2 : ℝ) ^ (j + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hb2
      _ = lam * (((N : ℝ) + k + 1) * (1 / 2 ^ (j + 1)) + (j : ℝ) / 2 ^ (j + 1)) := by ring
  refine (hasSum_le hterm (summable_sum fun n _ => hs n).hasSum hR).trans (le_of_eq ?_)
  push_cast
  ring

/-! ### Rigidity of the small roots in a window -/

/-- Roots `2 ≤ d ≤ K` of power divisors of `m`. -/
def smallRootCount (r K m : ℕ) : ℕ := ((Icc 2 K).filter fun d => d ^ r ∣ m).card

/-- Roots `d > K` of power divisors of `m`. -/
def bigRootCount (r K m : ℕ) : ℕ := (m.divisors.filter fun d => d ^ r ∣ m ∧ K < d).card

/-- `c(m) ≤ 1 + (small roots) + (big roots)`. -/
theorem powerDivisorCount_le_small_add_big (r K m : ℕ) :
    powerDivisorCount r m ≤ 1 + smallRootCount r K m + bigRootCount r K m := by
  classical
  unfold powerDivisorCount smallRootCount bigRootCount
  have hsub : (m.divisors.filter fun d => d ^ r ∣ m) ⊆
      ({1} ∪ (Icc 2 K).filter (fun d => d ^ r ∣ m)) ∪
        m.divisors.filter (fun d => d ^ r ∣ m ∧ K < d) := by
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, hm0⟩, hdr⟩ := hd
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hm0)
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_divisors]
    by_cases h1 : d = 1
    · exact Or.inl (Or.inl h1)
    by_cases hK : d ≤ K
    · exact Or.inl (Or.inr ⟨⟨by omega, hK⟩, hdr⟩)
    · exact Or.inr ⟨⟨hdm, hm0⟩, hdr, by omega⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by
        have := Finset.card_union_le ({1} : Finset ℕ) ((Icc 2 K).filter (fun d => d ^ r ∣ m))
        rw [Finset.card_singleton] at this
        omega

/-- Multiples of `M ≥ 1` among `n+1, …, n+L`: at most `L/M + 1`. -/
theorem card_filter_dvd_window_le (M n L : ℕ) :
    (((range L).filter fun j => M ∣ n + 1 + j).card : ℝ) ≤ (L : ℝ) / M + 1 := by
  have h := card_le_of_modEq_class (S := (range L).filter fun j => M ∣ n + 1 + j) (K := L)
    (T := M) (fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1) ?_
  · calc (((range L).filter fun j => M ∣ n + 1 + j).card : ℝ) ≤ ((L / M + 1 : ℕ) : ℝ) := by
          exact_mod_cast h
      _ ≤ (L : ℝ) / M + 1 := by push_cast; linarith [Nat.cast_div_le (m := L) (n := M) (α := ℝ)]
  intro j hj j' hj'
  have h1 := (Finset.mem_filter.mp hj).2
  have h2 := (Finset.mem_filter.mp hj').2
  have h0 : n + 1 + j ≡ n + 1 + j' [MOD M] :=
    (Nat.modEq_zero_iff_dvd.mpr h1).trans (Nat.modEq_zero_iff_dvd.mpr h2).symm
  exact Nat.ModEq.add_left_cancel' (n + 1) h0

/-- `Σ_{2 ≤ d ≤ K} 1/d² ≤ 11/12`. -/
theorem sum_Icc_two_inv_sq_le (K : ℕ) : (∑ d ∈ Icc 2 K, ((d : ℝ) ^ 2)⁻¹) ≤ 11 / 12 := by
  calc (∑ d ∈ Icc 2 K, ((d : ℝ) ^ 2)⁻¹) ≤ ∑ d ∈ insert 2 (Ioo 2 (K + 1)), ((d : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [Finset.mem_Icc] at hd
          simp only [Finset.mem_insert, Finset.mem_Ioo]
          omega
        · intro _ _ _; positivity
    _ = (1 / 4 : ℝ) + ∑ d ∈ Ioo 2 (K + 1), ((d : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_insert (by simp)]
        norm_num
    _ ≤ 1 / 4 + 2 / ((2 : ℕ) + 1 : ℝ) := by
        have := sum_Ioo_inv_sq_le (α := ℝ) 2 (K + 1)
        push_cast at this ⊢
        linarith
    _ = 11 / 12 := by norm_num

/-- **Small-root rigidity.**  In any window of length `L`, the roots `2 ≤ d ≤ K` contribute at
most `(11/12) L + K`. -/
theorem sum_smallRootCount_window_le {r : ℕ} (hr : 2 ≤ r) (K n L : ℕ) :
    ((∑ j ∈ range L, smallRootCount r K (n + 1 + j) : ℕ) : ℝ) ≤ 11 / 12 * L + K := by
  classical
  have hswap : (∑ j ∈ range L, smallRootCount r K (n + 1 + j)) =
      ∑ d ∈ Icc 2 K, ((range L).filter fun j => d ^ r ∣ n + 1 + j).card := by
    unfold smallRootCount
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, Nat.cast_sum]
  calc (∑ d ∈ Icc 2 K, ((((range L).filter fun j => d ^ r ∣ n + 1 + j).card : ℕ) : ℝ))
      ≤ ∑ d ∈ Icc 2 K, ((L : ℝ) * ((d : ℝ) ^ 2)⁻¹ + 1) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
        refine (card_filter_dvd_window_le (d ^ r) n L).trans ?_
        have hsq : (d : ℝ) ^ 2 ≤ ((d ^ r : ℕ) : ℝ) := by
          push_cast
          exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ d)) hr
        have : (L : ℝ) / ((d ^ r : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
        rw [← div_eq_mul_inv]
        linarith
    _ = (L : ℝ) * (∑ d ∈ Icc 2 K, ((d : ℝ) ^ 2)⁻¹) + ((Icc 2 K).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (L : ℝ) * (11 / 12) + K := by
        gcongr
        · exact sum_Icc_two_inv_sq_le K
        · rw [Nat.card_Icc]; exact_mod_cast (by omega)
    _ = 11 / 12 * L + K := by ring

/-- **Window rigidity.**  `Σ_{j<L} c(n+1+j) ≤ L + (11/12) L + K + Σ_{j<L} (roots > K)`. -/
theorem sum_window_le {r : ℕ} (hr : 2 ≤ r) (K n L : ℕ) :
    ((∑ j ∈ range L, powerDivisorCount r (n + 1 + j) : ℕ) : ℝ) ≤
      L + 11 / 12 * L + K + ((∑ j ∈ range L, bigRootCount r K (n + 1 + j) : ℕ) : ℝ) := by
  have h1 : (∑ j ∈ range L, powerDivisorCount r (n + 1 + j)) ≤
      L + (∑ j ∈ range L, smallRootCount r K (n + 1 + j)) +
        ∑ j ∈ range L, bigRootCount r K (n + 1 + j) := by
    calc (∑ j ∈ range L, powerDivisorCount r (n + 1 + j))
        ≤ ∑ j ∈ range L, (1 + smallRootCount r K (n + 1 + j) + bigRootCount r K (n + 1 + j)) :=
          Finset.sum_le_sum fun j _ => powerDivisorCount_le_small_add_big r K _
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; simp
  have h2 := sum_smallRootCount_window_le hr K n L
  have h1' : ((∑ j ∈ range L, powerDivisorCount r (n + 1 + j) : ℕ) : ℝ) ≤
      L + ((∑ j ∈ range L, smallRootCount r K (n + 1 + j) : ℕ) : ℝ) +
        ((∑ j ∈ range L, bigRootCount r K (n + 1 + j) : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- **Big roots are rare on average.**  `Σ_{n<N} Σ_{j<L} (roots > K of n+1+j) ≤
2 L (N + L) / (K + 1)`. -/
theorem sum_range_bigRoot_window_le {r : ℕ} (hr : 2 ≤ r) (K N L : ℕ) :
    ((∑ n ∈ range N, ∑ j ∈ range L, bigRootCount r K (n + 1 + j) : ℕ) : ℝ) ≤
      L * (N + L) * (2 / ((K : ℝ) + 1)) := by
  rw [Finset.sum_comm]
  have hX : ∀ X, ((∑ m ∈ Ioc 0 X, bigRootCount r K m : ℕ) : ℝ) ≤ X * (2 / ((K : ℝ) + 1)) := by
    intro X
    have h := sum_card_powerDivisors_filter_le hr (fun d => K < d) X
    exact h.trans (mul_le_mul_of_nonneg_left (sum_filter_lt_inv_sq_le K X) (by positivity))
  rw [Nat.cast_sum]
  calc (∑ j ∈ range L, ((∑ n ∈ range N, bigRootCount r K (n + 1 + j) : ℕ) : ℝ))
      ≤ ∑ j ∈ range L, ((N + L : ℕ) : ℝ) * (2 / ((K : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjL := Finset.mem_range.mp hj
        have h1 : (∑ n ∈ range N, bigRootCount r K (n + 1 + j)) ≤
            ∑ m ∈ Ioc 0 (N + L), bigRootCount r K m := by
          calc (∑ n ∈ range N, bigRootCount r K (n + 1 + j))
              = ∑ n ∈ range N, bigRootCount r K (n + (1 + j)) := by simp only [add_assoc]
            _ ≤ ∑ m ∈ Ioc 0 (N + (1 + j)), bigRootCount r K m :=
                sum_range_shift_le _ N (1 + j) (by omega)
            _ ≤ ∑ m ∈ Ioc 0 (N + L), bigRootCount r K m :=
                Finset.sum_le_sum_of_subset (Finset.Ioc_subset_Ioc_right (by omega))
        calc ((∑ n ∈ range N, bigRootCount r K (n + 1 + j) : ℕ) : ℝ)
            ≤ ((∑ m ∈ Ioc 0 (N + L), bigRootCount r K m : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ _ := hX _
    _ = L * (N + L) * (2 / ((K : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end NormalNumbers.ArithmeticDisjunctivity
