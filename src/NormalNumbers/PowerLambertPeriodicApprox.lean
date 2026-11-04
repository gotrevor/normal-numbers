/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertNearZero
import NormalNumbers.PowerLambertFrequencies

/-!
# Word frequencies of a perfect-power Lambert constant exist

`u_n = orbit b S n = {v_n + R_n}` with `v_n = {periodicTail Q n}` exactly `Q`-periodic and
`R_n = aperiodicTail Q n ≥ 0` of mean `≤ 2/(D+1)` (`Q = (D!)^r`).  If `R_n < η` then `u_n ∈ I`
and `v_n ∈ I` agree for a cylinder `I = [W/b^ℓ, (W+1)/b^ℓ)` unless `u_n` lies in
`[k/b^ℓ, k/b^ℓ + η)` for some `k`, which forces `u_{n+ℓ} < b^ℓ η` (`orbit_shift_lt_of_mem_Ico`).
Near-zero density (`powerLambert_nearZero_density_aux`) and Markov for `R` make the mismatch
density small, and the periodic counts converge, so the word counts are Cauchy.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset

/-! ### Periodic counts -/

/-- Counting a `Q`-periodic predicate on `[0, Q q + s)`. -/
theorem card_filter_range_mul_add (p : ℕ → Prop) [DecidablePred p] {Q : ℕ}
    (hp : ∀ n k, p (n + k * Q) ↔ p n) (q s : ℕ) :
    ((range (Q * q + s)).filter p).card =
      q * ((range Q).filter p).card + ((range s).filter p).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_range_add]
  congr 1
  · induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.succ_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Q * q + i = i + q * Q by ring]
      exact if_congr (hp i q) rfl rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Q * q + i = i + q * Q by ring]
    exact if_congr (hp i q) rfl rfl

/-- **Periodic averages.**  For a `Q`-periodic predicate and `N ≥ 1`,
`|#{n<N : p n}/N − #{n<Q : p n}/Q| ≤ Q/N`. -/
theorem abs_card_filter_div_sub_le (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hp : ∀ n k, p (n + k * Q) ↔ p n) {N : ℕ} (hN : 0 < N) :
    |(((range N).filter p).card : ℝ) / N - (((range Q).filter p).card : ℝ) / Q| ≤
      (Q : ℝ) / N := by
  have hdecomp := card_filter_range_mul_add p hp (N / Q) (N % Q)
  rw [Nat.div_add_mod] at hdecomp
  set c := ((range Q).filter p).card with hc
  set e := ((range (N % Q)).filter p).card with he
  have hcQ : c ≤ Q := (Finset.card_filter_le _ _).trans (by simp)
  have heQ : e ≤ Q := (Finset.card_filter_le _ _).trans (by simp; exact (Nat.mod_lt _ hQ).le)
  have hsQ : N % Q ≤ Q := (Nat.mod_lt _ hQ).le
  have hNdec : (N : ℝ) = Q * (N / Q : ℕ) + (N % Q : ℕ) := by
    exact_mod_cast (Nat.div_add_mod N Q).symm
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hdecomp]
  push_cast
  have key : ((N / Q : ℕ) * (c : ℝ) + e) / N - c / Q =
      ((Q : ℝ) * e - (N % Q : ℕ) * c) / (Q * N) := by
    field_simp
    rw [hNdec]
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Q * N), div_le_div_iff₀
    (by positivity) hNr]
  have h1 : (e : ℝ) ≤ Q := by exact_mod_cast heQ
  have h2 : (c : ℝ) ≤ Q := by exact_mod_cast hcQ
  have h3 : ((N % Q : ℕ) : ℝ) ≤ Q := by exact_mod_cast hsQ
  have h4 : (0 : ℝ) ≤ e := by positivity
  have h5 : (0 : ℝ) ≤ c := by positivity
  have h6 : (0 : ℝ) ≤ ((N % Q : ℕ) : ℝ) := by positivity
  rw [show (Q : ℝ) * (Q * N) = Q * Q * N by ring]
  refine mul_le_mul_of_nonneg_right ?_ hNr.le
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hQr.le,
    mul_le_mul h3 h2 h5 hQr.le, mul_nonneg h6 h5, mul_nonneg hQr.le h4]

/-! ### Mismatch between the orbit and its periodic model -/

/-- **Mismatch.**  If `v ∈ [0,1)`, `0 ≤ R < η` and `u = {v + R}`, then `u ∈ [α, β)` and
`v ∈ [α, β)` agree unless `u ∈ [α, α+η)`, `u ∈ [β, β+η)` or `u < η`. -/
theorem mem_Ico_iff_of_fract_add {v R η α β : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hR : 0 ≤ R)
    (hRη : R < η) (hη : η ≤ 1) (hα : ¬ Int.fract (v + R) ∈ Set.Ico α (α + η))
    (hβ : ¬ Int.fract (v + R) ∈ Set.Ico β (β + η)) (h0 : ¬ Int.fract (v + R) < η) :
    (Int.fract (v + R) ∈ Set.Ico α β ↔ v ∈ Set.Ico α β) := by
  by_cases hw : v + R < 1
  · have hu : Int.fract (v + R) = v + R := Int.fract_eq_self.mpr ⟨by linarith, hw⟩
    rw [hu] at hα hβ ⊢
    simp only [Set.mem_Ico, not_and, not_lt] at hα hβ ⊢
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by linarith⟩
      by_contra h
      push Not at h
      linarith [hα h1]
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith, ?_⟩
      by_contra h
      push Not at h
      linarith [hβ h]
  · exfalso
    apply h0
    have hu : Int.fract (v + R) = v + R - 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 1, by push_cast; ring⟩
    rw [hu]
    linarith

/-- Orbit shift: `orbit b x (n + k) = {b^k · orbit b x n}`. -/
theorem orbit_add_shift (b : ℕ) (x : ℝ) (n k : ℕ) :
    orbit b x (n + k) = Int.fract (orbit b x n * (b : ℝ) ^ k) := by
  unfold orbit
  rw [pow_add, ← mul_assoc]
  have : Int.fract (x * (b : ℝ) ^ n) * (b : ℝ) ^ k
      = x * (b : ℝ) ^ n * (b : ℝ) ^ k - ((⌊x * (b : ℝ) ^ n⌋ * (b ^ k : ℤ) : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

/-- **Near a `b`-adic rational, shift to near `0`.**  If `orbit n ∈ [k/b^ℓ, k/b^ℓ + 1/b^(L+ℓ))`
then `orbit (n + ℓ) < 1/b^L`. -/
theorem orbit_shift_lt_of_mem_Ico {b : ℕ} (hb : 2 ≤ b) (x : ℝ) (n ℓ L k : ℕ)
    (h : orbit b x n ∈ Set.Ico ((k : ℝ) / (b : ℝ) ^ ℓ)
      ((k : ℝ) / (b : ℝ) ^ ℓ + 1 / (b : ℝ) ^ (L + ℓ))) :
    orbit b x (n + ℓ) < 1 / (b : ℝ) ^ L := by
  have hbℓ : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  rw [orbit_add_shift]
  set y := orbit b x n * (b : ℝ) ^ ℓ with hy
  have h1 : (k : ℝ) ≤ y := by
    have := h.1
    rw [div_le_iff₀ hbℓ] at this
    exact this
  have h2 : y < k + 1 / (b : ℝ) ^ L := by
    have := mul_lt_mul_of_pos_right h.2 hbℓ
    rw [add_mul, div_mul_cancel₀ _ hbℓ.ne', pow_add, one_div, mul_inv, mul_assoc,
      inv_mul_cancel₀ hbℓ.ne', mul_one, ← one_div] at this
    exact this
  have hbL1 : 1 / (b : ℝ) ^ L ≤ 1 := by
    rw [div_le_one hbL]
    exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b))
  have hf : Int.fract y = y - k := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, ?_, k, by push_cast; ring⟩
    rcases hbL1.lt_or_eq with hlt | heq
    · linarith
    · -- `L = 0`: then `1/b^L = 1`
      linarith
  rw [hf]
  linarith

/-! ### Markov for the non-periodic tail -/

/-- The non-periodic count is supported on roots `d > D` when every `d ≤ D` has `d^r ∣ Q`. -/
theorem aperiodicPowerCount_le_bigRootCount {r Q D : ℕ}
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (m : ℕ) :
    aperiodicPowerCount r Q m ≤ bigRootCount r D m := by
  unfold aperiodicPowerCount bigRootCount
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
  obtain ⟨⟨hdm, hm0⟩, hdr, hQ⟩ := hd
  refine ⟨⟨hdm, hm0⟩, hdr, ?_⟩
  by_contra hle
  push Not at hle
  exact hQ (hQD d (Nat.pos_of_dvd_of_pos hdm (Nat.pos_of_ne_zero hm0)) hle)

/-- **Mean of the non-periodic tail.**  `Σ_{n<N} R_Q(n) ≤ (2/(D+1)) (N + 2)`. -/
theorem sum_range_aperiodicTail_le {b r Q D : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r)
    (hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q) (N : ℕ) :
    (∑ n ∈ range N, aperiodicTail b r Q n) ≤ 2 / ((D : ℝ) + 1) * (N + 2) := by
  have hmean : ∀ X, ((∑ m ∈ Ioc 0 X, aperiodicPowerCount r Q m : ℕ) : ℝ) ≤
      2 / ((D : ℝ) + 1) * X := by
    intro X
    have h1 : (∑ m ∈ Ioc 0 X, aperiodicPowerCount r Q m) ≤
        ∑ m ∈ Ioc 0 X, bigRootCount r D m :=
      Finset.sum_le_sum fun m _ => aperiodicPowerCount_le_bigRootCount hQD m
    have h2 := sum_card_powerDivisors_filter_le hr (fun d => D < d) X
    have h3 := sum_filter_lt_inv_sq_le D X
    calc ((∑ m ∈ Ioc 0 X, aperiodicPowerCount r Q m : ℕ) : ℝ)
        ≤ ((∑ m ∈ Ioc 0 X, bigRootCount r D m : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ X * ∑ d ∈ (Ioc 0 X).filter (fun d => D < d), ((d : ℝ) ^ 2)⁻¹ := h2
      _ ≤ X * (2 / ((D : ℝ) + 1)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 / ((D : ℝ) + 1) * X := by ring
  have h := sum_range_tail_le hb (aperiodicPowerCount r Q) (aperiodicPowerCount_le_self r Q)
    (by positivity) hmean N 0
  simp only [add_zero, Nat.cast_zero] at h
  exact h

/-! ### Assembly -/

open Classical in
/-- **Approximation by a periodic model.**  For every word `w` and `ε > 0` there is a constant
`g` (a frequency of the `Q_D`-periodic model) with `|#{n<N : w occurs at n}/N − g| ≤ ε` for all
large `N`. -/
theorem exists_eventually_abs_wordFreq_sub_le (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ, ∀ᶠ N : ℕ in atTop,
      |(((range N).filter fun n => OccursAt b (powerLambert b r) w n).card : ℝ) / N - g| ≤
        ε := by
  set S := powerLambert b r with hS
  set ℓ := w.length with hℓ
  set W := blockNatVal b w with hW
  set α : ℝ := (W : ℝ) / (b : ℝ) ^ ℓ with hα
  set β : ℝ := ((W : ℝ) + 1) / (b : ℝ) ^ ℓ with hβ
  obtain ⟨L, hL⟩ := powerLambert_nearZero_density_aux b r hb hr (ε / 8) (by positivity)
  set η : ℝ := 1 / (b : ℝ) ^ (L + ℓ) with hηdef
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hηdef, div_le_one (by positivity)]
    exact one_le_pow₀ hb1
  set D : ℕ := ⌈32 / (ε * η)⌉₊ with hDdef
  set Q : ℕ := D.factorial ^ r with hQdef
  have hQ : 0 < Q := by positivity
  have hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q := fun d hd1 hdD =>
    pow_dvd_pow_of_dvd (Nat.dvd_factorial hd1 hdD) r
  set v : ℕ → ℝ := fun n => Int.fract (periodicTail b r Q n) with hv
  set R : ℕ → ℝ := fun n => aperiodicTail b r Q n with hRdef
  have hu : ∀ n, orbit b S n = Int.fract (v n + R n) := by
    intro n
    rw [hS, orbit_powerLambert_eq b r Q hb (by omega) hQ n]
    simp only [hv, hRdef]
    rw [← Int.self_sub_floor (periodicTail b r Q n), sub_add_eq_add_sub, Int.fract_sub_intCast]
  set pv : ℕ → Prop := fun n => v n ∈ Set.Ico α β with hpvdef
  have hpv : ∀ n k, pv (n + k * Q) ↔ pv n := by
    intro n k
    simp only [hpvdef, hv, periodicTail_add_mul]
  have hpu : ∀ n, OccursAt b S w n ↔ orbit b S n ∈ Set.Ico α β :=
    fun n => occursAt_iff_orbit_mem b hb S w hw n
  set E : ℕ → Prop := fun m => orbit b S m < 1 / (b : ℝ) ^ L with hEdef
  -- off the bad set, the orbit and its periodic model see the same cylinder
  have hagree : ∀ n, ¬ η ≤ R n → ¬ E (n + ℓ) → (OccursAt b S w n ↔ pv n) := by
    intro n hR hE
    rw [hpu, hu]
    push Not at hR
    have hshift : ∀ k : ℕ, ¬ orbit b S n ∈
        Set.Ico ((k : ℝ) / (b : ℝ) ^ ℓ) ((k : ℝ) / (b : ℝ) ^ ℓ + η) :=
      fun k hk => hE (orbit_shift_lt_of_mem_Ico hb S n ℓ L k hk)
    simp only [hu] at hshift
    refine mem_Ico_iff_of_fract_add (Int.fract_nonneg _) (Int.fract_lt_one _)
      (aperiodicTail_nonneg _ _ _ _) hR hη1 (hshift W) ?_ ?_
    · have := hshift (W + 1)
      push_cast at this
      exact this
    · intro h0
      apply hshift 0
      simp only [Nat.cast_zero, zero_div, zero_add]
      exact ⟨Int.fract_nonneg _, h0⟩
  refine ⟨(((range Q).filter pv).card : ℝ) / Q, ?_⟩
  have hL' : ∀ᶠ N : ℕ in atTop, ((((range (N + ℓ)).filter fun n =>
      E n ∨ 1 - 1 / (b : ℝ) ^ L ≤ orbit b S n).card : ℝ) ≤ ε / 8 * ((N + ℓ : ℕ) : ℝ)) :=
    (tendsto_add_atTop_nat ℓ).eventually hL
  filter_upwards [hL', eventually_ge_atTop (ℓ + 2 + ⌈8 * (Q : ℝ) / ε⌉₊)] with N hNL hN
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set A := (range N).filter fun n => OccursAt b S w n with hA
  set B := (range N).filter pv with hB
  set bad1 := (range N).filter fun n => η ≤ R n with hbad1
  set bad2 := (range N).filter fun n => E (n + ℓ) with hbad2
  have hAB : A.card ≤ B.card + (bad1.card + bad2.card) := by
    calc A.card ≤ (B ∪ (bad1 ∪ bad2)).card := by
          apply card_le_card
          intro n hn
          simp only [hA, hB, hbad1, hbad2, mem_filter, mem_union] at hn ⊢
          by_cases h1 : η ≤ R n
          · exact Or.inr (Or.inl ⟨hn.1, h1⟩)
          by_cases h2 : E (n + ℓ)
          · exact Or.inr (Or.inr ⟨hn.1, h2⟩)
          exact Or.inl ⟨hn.1, (hagree n h1 h2).mp hn.2⟩
      _ ≤ B.card + (bad1 ∪ bad2).card := card_union_le _ _
      _ ≤ B.card + (bad1.card + bad2.card) := by gcongr; exact card_union_le _ _
  have hBA : B.card ≤ A.card + (bad1.card + bad2.card) := by
    calc B.card ≤ (A ∪ (bad1 ∪ bad2)).card := by
          apply card_le_card
          intro n hn
          simp only [hA, hB, hbad1, hbad2, mem_filter, mem_union] at hn ⊢
          by_cases h1 : η ≤ R n
          · exact Or.inr (Or.inl ⟨hn.1, h1⟩)
          by_cases h2 : E (n + ℓ)
          · exact Or.inr (Or.inr ⟨hn.1, h2⟩)
          exact Or.inl ⟨hn.1, (hagree n h1 h2).mpr hn.2⟩
      _ ≤ A.card + (bad1 ∪ bad2).card := card_union_le _ _
      _ ≤ A.card + (bad1.card + bad2.card) := by gcongr; exact card_union_le _ _
  have hcard1 : (bad1.card : ℝ) ≤ ε / 8 * N := by
    have hm := mul_card_filter_le_sum (s := range N) (f := R) η
      (fun n _ => aperiodicTail_nonneg _ _ _ _)
    have hs := sum_range_aperiodicTail_le (b := b) hb hr hQD N
    have hD : 32 / (ε * η) ≤ (D : ℝ) := Nat.le_ceil _
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have h32 : 32 ≤ ε * η * ((D : ℝ) + 1) := by
      have := (div_le_iff₀ (by positivity : 0 < ε * η)).mp hD
      nlinarith
    have hfin : 2 / ((D : ℝ) + 1) * (N + 2) ≤ η * (ε / 8 * N) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    exact le_of_mul_le_mul_left (hm.trans (hs.trans hfin)) hη
  have hcard2 : (bad2.card : ℝ) ≤ ε / 4 * N := by
    have hsub : bad2.card ≤ ((range (N + ℓ)).filter fun n =>
        E n ∨ 1 - 1 / (b : ℝ) ^ L ≤ orbit b S n).card := by
      rw [← Finset.card_map (addRightEmbedding ℓ)]
      apply card_le_card
      intro m hm
      simp only [hbad2, Finset.mem_map, mem_filter, mem_range, addRightEmbedding_apply] at hm ⊢
      obtain ⟨n, ⟨hn, hE⟩, rfl⟩ := hm
      exact ⟨by omega, Or.inl hE⟩
    have hℓN : ((N + ℓ : ℕ) : ℝ) ≤ 2 * N := by
      push_cast
      have : (ℓ : ℝ) ≤ N := by exact_mod_cast (by omega : ℓ ≤ N)
      linarith
    calc (bad2.card : ℝ) ≤ _ := by exact_mod_cast hsub
      _ ≤ ε / 8 * ((N + ℓ : ℕ) : ℝ) := hNL
      _ ≤ ε / 8 * (2 * N) := by gcongr
      _ = ε / 4 * N := by ring
  have hper := abs_card_filter_div_sub_le pv hQ hpv hNpos
  have hQN : (Q : ℝ) / N ≤ ε / 8 := by
    have h1 : 8 * (Q : ℝ) / ε ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈8 * (Q : ℝ) / ε⌉₊ ≤ N))
    rw [div_le_iff₀ hNr]
    rw [div_le_iff₀ hε] at h1
    linarith
  have hAB' : |(A.card : ℝ) / N - (B.card : ℝ) / N| ≤ ε / 8 + ε / 4 := by
    rw [← sub_div, abs_div, abs_of_pos hNr, div_le_iff₀ hNr, abs_le]
    have h1 : (A.card : ℝ) ≤ B.card + (bad1.card + bad2.card) := by exact_mod_cast hAB
    have h2 : (B.card : ℝ) ≤ A.card + (bad1.card + bad2.card) := by exact_mod_cast hBA
    constructor <;> nlinarith
  calc |(A.card : ℝ) / N - (((range Q).filter pv).card : ℝ) / Q|
      ≤ |(A.card : ℝ) / N - (B.card : ℝ) / N| +
          |(B.card : ℝ) / N - (((range Q).filter pv).card : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ (ε / 8 + ε / 4) + ε / 8 := add_le_add hAB' (hper.trans hQN)
    _ ≤ ε := by linarith

/-- **Every word frequency exists** (the frozen headline of
`PowerLambertFrequenciesExist.lean`). -/
theorem powerLambertFrequenciesExist_aux (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    PowerLambertFrequenciesExist b r := by
  intro w hw
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨g, hg⟩ := exists_eventually_abs_wordFreq_sub_le b r hb hr w hw (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hg
  refine ⟨N₀, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have h1 := hN₀ n hn
  have h2 := hN₀ N₀ le_rfl
  rw [abs_sub_comm] at h2
  calc _ ≤ _ := abs_sub_le _ g _
    _ < ε := by linarith

end NormalNumbers.ArithmeticDisjunctivity
