/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertFrequenciesExist
import NormalNumbers.PowerLambertPeriodicApprox

/-!
# The word-frequency law of a perfect-power Lambert constant is computable

`powerLambertFrequenciesExist` gives every word `w` a limiting frequency `powerLambertFreq b r w`.
This file pins it down: it is the limit, along `Q_D = (D!)^r`, of the frequencies of the
`Q_D`-periodic model `n ↦ {periodicTail b r Q_D n}` (a finite computation for each `D`), and
packages the three properties of the constant: rich, every word frequency exists, not normal.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Filter Topology Finset NormalNumbers.CastingOut

open Classical in
/-- The limiting frequency of the word `w` in the base-`b` expansion of `powerLambert b r`
(its existence is `powerLambertFrequenciesExist`). -/
noncomputable def powerLambertFreq (b r : ℕ) (w : List ℕ) : ℝ :=
  limUnder atTop fun N : ℕ =>
    (((range N).filter fun n => OccursAt b (powerLambert b r) w n).card : ℝ) / N

open Classical in
/-- The frequency of the cylinder of `w` in the `Q`-periodic model: the share of `n < Q` whose
periodic orbit point `{periodicTail b r Q n}` lies in `[W/b^ℓ, (W+1)/b^ℓ)`. -/
noncomputable def periodicModelFreq (b r Q : ℕ) (w : List ℕ) : ℝ :=
  (((range Q).filter fun n => Int.fract (periodicTail b r Q n) ∈
      Set.Ico ((blockNatVal b w : ℝ) / (b : ℝ) ^ w.length)
        (((blockNatVal b w : ℝ) + 1) / (b : ℝ) ^ w.length)).card : ℝ) / Q

open Classical in
/-- **Approximation by every late periodic model.**  For every word `w` and `ε > 0` there is
`D₀` such that for *every* `D ≥ D₀` the empirical frequency of `w` is eventually within `ε` of the
frequency of the `(D!)^r`-periodic model.  (The proof of `exists_eventually_abs_wordFreq_sub_le`,
with its chosen `D` replaced by an arbitrary `D ≥ D₀`.) -/
theorem eventually_abs_wordFreq_sub_periodicModelFreq_le (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ᶠ N : ℕ in atTop,
      |(((range N).filter fun n => OccursAt b (powerLambert b r) w n).card : ℝ) / N -
        periodicModelFreq b r (D.factorial ^ r) w| ≤ ε := by
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
  refine ⟨⌈32 / (ε * η)⌉₊, fun D hD₀ => ?_⟩
  have hD : 32 / (ε * η) ≤ (D : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hD₀)
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
  show ∀ᶠ N : ℕ in atTop, |(((range N).filter fun n => OccursAt b S w n).card : ℝ) / N -
      (((range Q).filter pv).card : ℝ) / Q| ≤ ε
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


/-- **Frozen (2026-11-04).**  The word frequency is the limit of the periodic-model frequencies
along `Q_D = (D!)^r`: the law is computable. -/
theorem powerLambertFreq_eq_lim (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) (w : List ℕ)
    (hw : ∀ d ∈ w, d < b) :
    Tendsto (fun D : ℕ => periodicModelFreq b r (D.factorial ^ r) w) atTop
      (𝓝 (powerLambertFreq b r w)) := by
  classical
  set a : ℕ → ℝ := fun N =>
    (((range N).filter fun n => OccursAt b (powerLambert b r) w n).card : ℝ) / N with ha_def
  have ha : Tendsto a atTop (𝓝 (powerLambertFreq b r w)) := by
    obtain ⟨f, hf⟩ := powerLambertFrequenciesExist b r hb hr w hw
    exact tendsto_nhds_limUnder ⟨f, hf⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨D₀, hD₀⟩ :=
    eventually_abs_wordFreq_sub_periodicModelFreq_le b r hb hr w hw (ε / 2) (by positivity)
  refine ⟨D₀, fun D hD => ?_⟩
  set G := periodicModelFreq b r (D.factorial ^ r) w
  have hlim : Tendsto (fun N => |a N - G|) atTop (𝓝 |powerLambertFreq b r w - G|) :=
    (ha.sub_const G).abs
  have hle : |powerLambertFreq b r w - G| ≤ ε / 2 := le_of_tendsto hlim (hD₀ D hD)
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- **Frozen (2026-11-04).**  The three properties together: `Σ_{n≥1} 1/(b^{n^r} − 1)` is rich,
has a limiting frequency for every word, and is not normal. -/
theorem powerLambert_frequency_law (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsRich b (powerLambert b r) ∧ PowerLambertFrequenciesExist b r ∧
      ¬ IsNormal b (powerLambert b r) := by
  exact ⟨isRich_powerLambert b r hb hr, powerLambertFrequenciesExist b r hb hr,
    not_isNormal_powerLambert b r hb hr⟩

end NormalNumbers.ArithmeticDisjunctivity
