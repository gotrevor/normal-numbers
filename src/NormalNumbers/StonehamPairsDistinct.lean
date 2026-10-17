/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPairsClasses

/-!
# Distinct multiplicative classes of Stoneham pairs

This file packages the exact unequal-depth valuation into a reduced-denominator lower bound for
two Stoneham families in distinct multiplicative classes.
-/

namespace NormalNumbers.StonehamPairsNormal

/-- A small algebraic identity kept separate so the depth proof never asks `ring` to normalize
the full logarithmic expression. -/
private lemma slope_error_identity
    (A B K₁ K₂ l₁ l₂ L : ℝ) (hdepth : A * K₁ = B * K₂) :
    (A * l₂ - B * l₁) * L =
      A * (L - K₁ * l₁) * l₂ - B * (L - K₂ * l₂) * l₁ := by
  linear_combination (l₁ * l₂) * hdepth

/-- Unequal logarithmic slopes make the corresponding integral Stoneham depths eventually
different.  This is the only separation needed by the exact valuation theorem: once the smaller
depth survives in the numerator, the larger depth remains in the reduced denominator. -/
theorem eventually_natLog_depth_ne
    (c₁ c₂ a₁ a₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hslope : (a₁ : ℝ) * Real.log c₂ ≠ (a₂ : ℝ) * Real.log c₁) :
    ∀ᶠ n : ℕ in Filter.atTop,
      a₁ * Nat.log c₁ n ≠ a₂ * Nat.log c₂ n := by
  let l₁ : ℝ := Real.log c₁
  let l₂ : ℝ := Real.log c₂
  let s : ℝ := (a₁ : ℝ) * l₂ - (a₂ : ℝ) * l₁
  let P : ℝ := l₁ * l₂
  let B : ℝ := (a₁ + a₂ + 1 : ℕ) * P
  have hl₁ : 0 < l₁ := by
    dsimp only [l₁]
    exact Real.log_pos (by exact_mod_cast hc₁)
  have hl₂ : 0 < l₂ := by
    dsimp only [l₂]
    exact Real.log_pos (by exact_mod_cast hc₂)
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hs : s ≠ 0 := by
    simpa only [s, l₁, l₂, sub_ne_zero] using hslope
  have habss : 0 < |s| := abs_pos.mpr hs
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, B / |s| < Real.log n :=
    hlog.eventually (Filter.eventually_gt_atTop (B / |s|))
  filter_upwards [Filter.eventually_ge_atTop 1, hlarge] with n hn hnlarge
  obtain ⟨he₁lo, he₁hi⟩ := natLog_mul_log_base_error c₁ n hc₁ hn
  obtain ⟨he₂lo, he₂hi⟩ := natLog_mul_log_base_error c₂ n hc₂ hn
  let e₁ : ℝ := Real.log n - (Nat.log c₁ n : ℝ) * l₁
  let e₂ : ℝ := Real.log n - (Nat.log c₂ n : ℝ) * l₂
  have he₁lo' : 0 ≤ e₁ := by simpa only [e₁, l₁] using he₁lo
  have he₁hi' : e₁ ≤ l₁ := by
    exact (by simpa only [e₁, l₁] using he₁hi.le)
  have he₂lo' : 0 ≤ e₂ := by simpa only [e₂, l₂] using he₂lo
  have he₂hi' : e₂ ≤ l₂ := by
    exact (by simpa only [e₂, l₂] using he₂hi.le)
  have he₁bound : (a₁ : ℝ) * e₁ * l₂ ≤ (a₁ : ℝ) * P := by
    calc
      (a₁ : ℝ) * e₁ * l₂ ≤ (a₁ : ℝ) * l₁ * l₂ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he₁hi' (Nat.cast_nonneg a₁)) hl₂.le
      _ = (a₁ : ℝ) * P := by simp [P, mul_assoc]
  have he₁nonneg : 0 ≤ (a₁ : ℝ) * e₁ * l₂ := by positivity
  have he₂bound : (a₂ : ℝ) * e₂ * l₁ ≤ (a₂ : ℝ) * P := by
    calc
      (a₂ : ℝ) * e₂ * l₁ ≤ (a₂ : ℝ) * l₂ * l₁ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he₂hi' (Nat.cast_nonneg a₂)) hl₁.le
      _ = (a₂ : ℝ) * P := by dsimp only [P]; ac_rfl
  have he₂nonneg : 0 ≤ (a₂ : ℝ) * e₂ * l₁ := by positivity
  have ha₁B : (a₁ : ℝ) * P ≤ B := by
    dsimp only [B]
    have : (a₁ : ℝ) ≤ (a₁ + a₂ + 1 : ℕ) := by exact_mod_cast (by omega)
    exact mul_le_mul_of_nonneg_right this hP.le
  have ha₂B : (a₂ : ℝ) * P ≤ B := by
    dsimp only [B]
    have : (a₂ : ℝ) ≤ (a₁ + a₂ + 1 : ℕ) := by exact_mod_cast (by omega)
    exact mul_le_mul_of_nonneg_right this hP.le
  have hthreshold : B < |s| * Real.log n := by
    simpa [mul_comm] using (div_lt_iff₀ habss).mp hnlarge
  intro hdepth
  have hdepthR : (a₁ : ℝ) * Nat.log c₁ n = (a₂ : ℝ) * Nat.log c₂ n := by
    exact_mod_cast hdepth
  have hid : s * Real.log n = (a₁ : ℝ) * e₁ * l₂ -
      (a₂ : ℝ) * e₂ * l₁ := by
    simpa only [s, e₁, e₂] using slope_error_identity
      (a₁ : ℝ) (a₂ : ℝ) (Nat.log c₁ n : ℝ) (Nat.log c₂ n : ℝ)
        l₁ l₂ (Real.log n) hdepthR
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have habs : |s| = -s := abs_of_neg hsneg
    have : (-s) * Real.log n ≤ B := by
      calc
        (-s) * Real.log n = - (s * Real.log n) := neg_mul s (Real.log n)
        _ = (a₂ : ℝ) * e₂ * l₁ - (a₁ : ℝ) * e₁ * l₂ := by
          rw [hid, neg_sub]
        _ ≤ (a₂ : ℝ) * e₂ * l₁ := sub_le_self _ he₁nonneg
        _ ≤ (a₂ : ℝ) * P := he₂bound
        _ ≤ B := ha₂B
    rw [habs] at hthreshold
    exact (not_lt_of_ge this) hthreshold
  · have habs : |s| = s := abs_of_pos hspos
    have : s * Real.log n ≤ B := by
      calc
        s * Real.log n = (a₁ : ℝ) * e₁ * l₂ - (a₂ : ℝ) * e₂ * l₁ := hid
        _ ≤ (a₁ : ℝ) * e₁ * l₂ := sub_le_self _ he₂nonneg
        _ ≤ (a₁ : ℝ) * P := he₁bound
        _ ≤ B := ha₁B
    rw [habs] at hthreshold
    exact (not_lt_of_ge this) hthreshold

/-- The algebraic companion to `padicValInt_unit_mul_pow_add_mul_pow_of_lt`:
the same shallower unit term also prevents the sum from vanishing. -/
theorem unit_mul_pow_add_mul_pow_ne_zero_of_lt
    (p : ℕ) [Fact p.Prime] (A B : ℤ) (e f : ℕ)
    (hA : ¬ (p : ℤ) ∣ A) (hef : e < f) :
    A * (p : ℤ) ^ e + B * (p : ℤ) ^ f ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hpdvd : (p : ℤ) ∣ (p : ℤ) ^ (f - e) :=
    dvd_pow_self (p : ℤ) (by omega)
  have hterm : (p : ℤ) ∣ B * (p : ℤ) ^ (f - e) :=
    dvd_mul_of_dvd_right hpdvd B
  have hunit : ¬ (p : ℤ) ∣ A + B * (p : ℤ) ^ (f - e) := by
    intro hsum
    apply hA
    simpa using dvd_sub hsum hterm
  have hunit0 : A + B * (p : ℤ) ^ (f - e) ≠ 0 := by
    intro hz
    apply hunit
    simp [hz]
  have hpow0 : (p : ℤ) ^ e ≠ 0 := pow_ne_zero e hp0
  have hpowf : (p : ℤ) ^ f = (p : ℤ) ^ e * (p : ℤ) ^ (f - e) := by
    calc
      (p : ℤ) ^ f = (p : ℤ) ^ (e + (f - e)) := by congr 1; omega
      _ = (p : ℤ) ^ e * (p : ℤ) ^ (f - e) := pow_add _ _ _
  have hfactor :
      A * (p : ℤ) ^ e + B * (p : ℤ) ^ f =
        (p : ℤ) ^ e * (A + B * (p : ℤ) ^ (f - e)) := by
    rw [hpowf, mul_add]
    congr 1
    · exact mul_comm _ _
    · ac_rfl
  intro hzero
  exact (mul_ne_zero hpow0 hunit0) (hfactor.symm.trans hzero)

/-- The cleared numerator of two Stoneham families is nonzero whenever their depths at a
denominator prime are unequal and the shallower family has entered.  This complements the exact
valuation theorem with the nonvanishing hypothesis needed by rational valuation arithmetic. -/
theorem pairCleared_ne_zero_of_depth_lt
    (p b c₁ c₂ K₁ K₂ n : ℕ) (σ : ℤ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) (hpc₁ : p ∣ c₁)
    (hcb₁ : Nat.Coprime c₁ b) (hK₁ : 1 ≤ K₁)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hdepth : c₂.factorization p * K₂ < c₁.factorization p * K₁) :
    stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
        σ * stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁ ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let A₁ := stonehamClearedFamily b c₁ n K₁
  let A₂ := stonehamClearedFamily b c₂ n K₂
  let u₁ : ℕ := ordCompl[p] c₁
  let u₂ : ℕ := ordCompl[p] c₂
  let e := c₂.factorization p * K₂
  let f := c₁.factorization p * K₁
  have hA₁ : ¬ (p : ℤ) ∣ A₁ := by
    exact not_dvd_stonehamClearedFamily p b c₁ K₁ n hp hc₁0 hpc₁
      hcb₁ hK₁ hentered₁
  have hu₂ : ¬ p ∣ u₂ := Nat.not_dvd_ordCompl hp hc₂0
  have hu₂Z : ¬ (p : ℤ) ∣ (u₂ : ℤ) ^ K₂ := by
    intro hdvd
    apply hu₂
    have hdvdNat : p ∣ u₂ ^ K₂ := by exact_mod_cast hdvd
    exact hp.dvd_of_dvd_pow hdvdNat
  have hunit : ¬ (p : ℤ) ∣ A₁ * (u₂ : ℤ) ^ K₂ := by
    intro hdvd
    rcases Int.Prime.dvd_mul' hp hdvd with h | h
    · exact hA₁ h
    · exact hu₂Z h
  have hc₁pow : (c₁ : ℤ) ^ K₁ =
      (p : ℤ) ^ f * (u₁ : ℤ) ^ K₁ := by
    calc
      (c₁ : ℤ) ^ K₁ =
          (((p : ℤ) ^ c₁.factorization p) * (u₁ : ℤ)) ^ K₁ := by
            congr 1
            exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self c₁ p).symm
      _ = (p : ℤ) ^ f * (u₁ : ℤ) ^ K₁ := by
        rw [mul_pow, ← pow_mul]
  have hc₂pow : (c₂ : ℤ) ^ K₂ =
      (p : ℤ) ^ e * (u₂ : ℤ) ^ K₂ := by
    calc
      (c₂ : ℤ) ^ K₂ =
          (((p : ℤ) ^ c₂.factorization p) * (u₂ : ℤ)) ^ K₂ := by
            congr 1
            exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self c₂ p).symm
      _ = (p : ℤ) ^ e * (u₂ : ℤ) ^ K₂ := by
        rw [mul_pow, ← pow_mul]
  have hshape :
      stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
          σ * stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁ =
        (A₁ * (u₂ : ℤ) ^ K₂) * (p : ℤ) ^ e +
          (σ * A₂ * (u₁ : ℤ) ^ K₁) * (p : ℤ) ^ f := by
    rw [hc₁pow, hc₂pow]
    dsimp only [A₁, A₂]
    ac_rfl
  rw [hshape]
  exact unit_mul_pow_add_mul_pow_ne_zero_of_lt p
    (A₁ * (u₂ : ℤ) ^ K₂) (σ * A₂ * (u₁ : ℤ) ^ K₁) e f hunit hdepth

/-- An exact negative rational valuation forces the corresponding prime power into the reduced
denominator.  This is the cancellation-to-denominator bridge used after the cleared-pair
valuation calculation. -/
theorem prime_pow_dvd_rat_den_of_eq_div
    (p e v : ℕ) (A : ℤ) (D : ℕ) (q : ℚ)
    (hp : p.Prime) (hA : A ≠ 0) (hD : D ≠ 0)
    (hq : q = (A : ℚ) / (D : ℚ))
    (hvA : padicValInt p A = v) (hvD : padicValNat p D = v + e) :
    p ^ e ∣ q.den := by
  letI : Fact p.Prime := ⟨hp⟩
  have hAZ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hDZ : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hval : padicValRat p q = -(e : ℤ) := by
    rw [hq, padicValRat.div hAZ hDZ, padicValRat.of_int,
      padicValRat.of_nat, hvA, hvD]
    omega
  rw [padicValRat_def] at hval
  have he : e ≤ padicValNat p q.den := by omega
  exact (hp.pow_dvd_iff_le_factorization q.den_nz).2 (by
    rw [Nat.factorization_def _ hp]
    exact he)

/-- At an unequal-depth prime, the entire deeper Stoneham depth survives in the reduced
denominator of the literal pair state.  The shallower depth is exactly the numerator valuation,
so it cancels only its own contribution to the common denominator. -/
theorem prime_pow_dvd_pairFamilies_den_of_depth_lt
    (p b c₁ c₂ K₁ K₂ n : ℕ) (σ : ℤ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) (hpc₁ : p ∣ c₁)
    (hcb₁ : Nat.Coprime c₁ b) (hK₁ : 1 ≤ K₁)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hdepth : c₂.factorization p * K₂ < c₁.factorization p * K₁) :
    p ^ (c₁.factorization p * K₁) ∣
      ((∑ j ∈ Finset.Icc 1 K₁,
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
        (σ : ℚ) * (∑ j ∈ Finset.Icc 1 K₂,
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)).den := by
  letI : Fact p.Prime := ⟨hp⟩
  let A : ℤ :=
    stonehamClearedFamily b c₁ n K₁ * (c₂ : ℤ) ^ K₂ +
      σ * stonehamClearedFamily b c₂ n K₂ * (c₁ : ℤ) ^ K₁
  let D : ℕ := (c₁ ^ K₁) * (c₂ ^ K₂)
  let q : ℚ :=
    (∑ j ∈ Finset.Icc 1 K₁,
        (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
      (σ : ℚ) * (∑ j ∈ Finset.Icc 1 K₂,
        (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)
  have hA : A ≠ 0 := by
    dsimp only [A]
    exact pairCleared_ne_zero_of_depth_lt p b c₁ c₂ K₁ K₂ n σ hp
      hc₁0 hc₂0 hpc₁ hcb₁ hK₁ hentered₁ hdepth
  have hD : D ≠ 0 := by
    dsimp only [D]
    exact mul_ne_zero (pow_ne_zero _ hc₁0) (pow_ne_zero _ hc₂0)
  have hq : q = (A : ℚ) / (D : ℚ) := by
    dsimp only [q, A, D]
    exact stonehamPairFamilies_eq_cleared_div b c₁ c₂ n K₁ K₂ σ hc₁0 hc₂0
  have hvA : padicValInt p A = c₂.factorization p * K₂ := by
    dsimp only [A]
    exact padicValInt_pairCleared_eq_of_depth_lt p b c₁ c₂ K₁ K₂ n σ hp
      hc₁0 hc₂0 hpc₁ hcb₁ hK₁ hentered₁ hdepth
  have hvD : padicValNat p D =
      c₂.factorization p * K₂ + c₁.factorization p * K₁ := by
    dsimp only [D]
    rw [padicValNat.mul (pow_ne_zero _ hc₁0) (pow_ne_zero _ hc₂0),
      padicValNat.pow, padicValNat.pow,
      ← Nat.factorization_def c₁ hp, ← Nat.factorization_def c₂ hp]
    ac_rfl
  have hdiv := prime_pow_dvd_rat_den_of_eq_div p
    (c₁.factorization p * K₁) (c₂.factorization p * K₂) A D q
      hp hA hD hq hvA hvD
  simpa only [q] using hdiv

/-- For a literal sum, unequal depths leave the larger full depth in the reduced denominator. -/
theorem prime_pow_max_dvd_pairFamilies_add_den_of_depth_ne
    (p b c₁ c₂ K₁ K₂ n : ℕ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b)
    (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 K₂, c₂ ^ j ≤ n)
    (hne : c₁.factorization p * K₁ ≠ c₂.factorization p * K₂) :
    p ^ max (c₁.factorization p * K₁) (c₂.factorization p * K₂) ∣
      ((∑ j ∈ Finset.Icc 1 K₁,
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
        ∑ j ∈ Finset.Icc 1 K₂,
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j).den := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpc₂ : p ∣ c₂ := by
      by_contra hnot
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_mul] at hlt
      omega
    have h := prime_pow_dvd_pairFamilies_den_of_depth_lt
      p b c₂ c₁ K₂ K₁ n 1 hp hc₂0 hc₁0 hpc₂ hcb₂ hK₂ hentered₂ hlt
    simpa [Nat.max_eq_right hlt.le, add_comm] using h
  · have hpc₁ : p ∣ c₁ := by
      by_contra hnot
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_mul] at hgt
      omega
    have h := prime_pow_dvd_pairFamilies_den_of_depth_lt
      p b c₁ c₂ K₁ K₂ n 1 hp hc₁0 hc₂0 hpc₁ hcb₁ hK₁ hentered₁ hgt
    simpa [Nat.max_eq_left hgt.le] using h

/-- For a literal difference, unequal depths likewise leave the larger full depth in the reduced
denominator. -/
theorem prime_pow_max_dvd_pairFamilies_sub_den_of_depth_ne
    (p b c₁ c₂ K₁ K₂ n : ℕ) (hp : p.Prime)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b)
    (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 K₁, c₁ ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 K₂, c₂ ^ j ≤ n)
    (hne : c₁.factorization p * K₁ ≠ c₂.factorization p * K₂) :
    p ^ max (c₁.factorization p * K₁) (c₂.factorization p * K₂) ∣
      ((∑ j ∈ Finset.Icc 1 K₁,
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) -
        ∑ j ∈ Finset.Icc 1 K₂,
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j).den := by
  let F₁ : ℚ := ∑ j ∈ Finset.Icc 1 K₁,
    (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j
  let F₂ : ℚ := ∑ j ∈ Finset.Icc 1 K₂,
    (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j
  change p ^ max (c₁.factorization p * K₁) (c₂.factorization p * K₂) ∣ (F₁ - F₂).den
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpc₂ : p ∣ c₂ := by
      by_contra hnot
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_mul] at hlt
      omega
    have h := prime_pow_dvd_pairFamilies_den_of_depth_lt
      p b c₂ c₁ K₂ K₁ n (-1) hp hc₂0 hc₁0 hpc₂ hcb₂ hK₂ hentered₂ hlt
    have h' : p ^ (c₂.factorization p * K₂) ∣ (F₂ - F₁).den := by
      simpa [F₁, F₂, sub_eq_add_neg] using h
    have hden : (F₂ - F₁).den = (F₁ - F₂).den := by
      calc
        (F₂ - F₁).den = (-(F₁ - F₂)).den :=
          congrArg Rat.den (neg_sub F₁ F₂).symm
        _ = (F₁ - F₂).den := Rat.den_neg_eq_den _
    rw [Nat.max_eq_right hlt.le, ← hden]
    exact h'
  · have hpc₁ : p ∣ c₁ := by
      by_contra hnot
      rw [Nat.factorization_eq_zero_of_not_dvd hnot, zero_mul] at hgt
      omega
    have h := prime_pow_dvd_pairFamilies_den_of_depth_lt
      p b c₁ c₂ K₁ K₂ n (-1) hp hc₁0 hc₂0 hpc₁ hcb₁ hK₁ hentered₁ hgt
    simpa [F₁, F₂, Nat.max_eq_left hgt.le, sub_eq_add_neg] using h

/-! ### Fourier multipliers and the exact two-family state -/

/-- Multiplication by a fixed nonzero integer can remove at most its `p`-adic valuation from a
prime-power divisor of a reduced rational denominator. -/
theorem prime_pow_sub_padicValInt_dvd_mul_den
    (p E : ℕ) (h : ℤ) (q : ℚ) (hp : p.Prime) (hh : h ≠ 0)
    (hdiv : p ^ E ∣ q.den) :
    p ^ (E - padicValInt p h) ∣ ((h : ℚ) * q).den := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hsmall : E ≤ padicValInt p h
  · rw [Nat.sub_eq_zero_of_le hsmall, pow_zero]
    exact one_dvd _
  have hE : 0 < E := by omega
  have hpd : p ∣ q.den :=
    (dvd_pow_self p hE.ne').trans hdiv
  have hq : q ≠ 0 := by
    intro hzero
    subst q
    simp at hpd
    exact hp.ne_one hpd
  have hnum_not : ¬p ∣ q.num.natAbs := by
    exact (hp.coprime_iff_not_dvd.mp
      (q.reduced.symm.coprime_dvd_left hpd))
  have hnum_not_int : ¬(p : ℤ) ∣ q.num := by
    rw [Int.natCast_dvd]
    exact hnum_not
  have hnum : padicValInt p q.num = 0 :=
    padicValInt.eq_zero_of_not_dvd hnum_not_int
  have hqden : E ≤ padicValNat p q.den :=
    (padicValNat_dvd_iff_le q.den_nz).mp hdiv
  have hval :
      (padicValInt p (((h : ℚ) * q).num) : ℤ) -
          padicValNat p (((h : ℚ) * q).den) =
        (padicValInt p h : ℤ) - padicValNat p q.den := by
    calc
      _ = padicValRat p ((h : ℚ) * q) := rfl
      _ = padicValRat p (h : ℚ) + padicValRat p q :=
        padicValRat.mul (by exact_mod_cast hh) hq
      _ = (padicValInt p h : ℤ) - padicValNat p q.den := by
        rw [padicValRat.of_int, padicValRat_def, hnum]
        omega
  apply (padicValNat_dvd_iff_le (((h : ℚ) * q).den_nz)).mpr
  omega

/-- The `Fin 2` state for two unshifted Stoneham families is exactly the fixed Fourier
multiplier times the corresponding literal signed pair. -/
theorem stonehamState_pair_one_eq
    (b c₁ c₂ n : ℕ) (h σ : ℤ) :
    NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![c₁, c₂] ![1, 1] ![h, σ * h] n =
      (h : ℚ) *
        ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
            (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
          (σ : ℚ) * (∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
            (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)) := by
  simp [NormalNumbers.StonehamSumsNormal.stonehamState,
    NormalNumbers.StonehamSumsNormal.stonehamK, Fin.sum_univ_two]
  ring

/-- Transfer a prime-power denominator divisor for a literal signed pair to its exact
two-family Stoneham state, accounting for the fixed Fourier multiplier. -/
theorem prime_pow_sub_padicValInt_dvd_stonehamState_pair_one_den
    (p E b c₁ c₂ n : ℕ) (h σ : ℤ) (hp : p.Prime) (hh : h ≠ 0)
    (hdiv : p ^ E ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
        (σ : ℚ) * (∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)).den) :
    p ^ (E - padicValInt p h) ∣
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![c₁, c₂] ![1, 1] ![h, σ * h] n).den := by
  rw [stonehamState_pair_one_eq]
  exact prime_pow_sub_padicValInt_dvd_mul_den p E h _ hp hh hdiv

/-- The literal sum state retains the maximum unequal prime depth, minus only the fixed
valuation of its Fourier multiplier. -/
theorem prime_pow_max_sub_padicValInt_dvd_stonehamState_pair_add_den_of_depth_ne
    (p b c₁ c₂ n : ℕ) (h : ℤ) (hp : p.Prime) (hh : h ≠ 0)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b)
    (hK₁ : 1 ≤ Nat.log c₁ n) (hK₂ : 1 ≤ Nat.log c₂ n)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (Nat.log c₁ n), c₁ ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (Nat.log c₂ n), c₂ ^ j ≤ n)
    (hne : c₁.factorization p * Nat.log c₁ n ≠
      c₂.factorization p * Nat.log c₂ n) :
    p ^ (max (c₁.factorization p * Nat.log c₁ n)
          (c₂.factorization p * Nat.log c₂ n) - padicValInt p h) ∣
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![c₁, c₂] ![1, 1] ![h, h] n).den := by
  have hdiv := prime_pow_max_dvd_pairFamilies_add_den_of_depth_ne
    p b c₁ c₂ (Nat.log c₁ n) (Nat.log c₂ n) n hp hc₁0 hc₂0
      hcb₁ hcb₂ hK₁ hK₂ hentered₁ hentered₂ hne
  have hdiv' : p ^ max (c₁.factorization p * Nat.log c₁ n)
      (c₂.factorization p * Nat.log c₂ n) ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
        (1 : ℚ) * (∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)).den := by
    simpa using hdiv
  simpa using prime_pow_sub_padicValInt_dvd_stonehamState_pair_one_den
    p (max (c₁.factorization p * Nat.log c₁ n)
      (c₂.factorization p * Nat.log c₂ n)) b c₁ c₂ n h 1 hp hh hdiv'

/-- The literal difference state has the same maximum-depth denominator divisor after its fixed
Fourier-multiplier loss. -/
theorem prime_pow_max_sub_padicValInt_dvd_stonehamState_pair_sub_den_of_depth_ne
    (p b c₁ c₂ n : ℕ) (h : ℤ) (hp : p.Prime) (hh : h ≠ 0)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)
    (hcb₁ : Nat.Coprime c₁ b) (hcb₂ : Nat.Coprime c₂ b)
    (hK₁ : 1 ≤ Nat.log c₁ n) (hK₂ : 1 ≤ Nat.log c₂ n)
    (hentered₁ : ∀ j ∈ Finset.Icc 1 (Nat.log c₁ n), c₁ ^ j ≤ n)
    (hentered₂ : ∀ j ∈ Finset.Icc 1 (Nat.log c₂ n), c₂ ^ j ≤ n)
    (hne : c₁.factorization p * Nat.log c₁ n ≠
      c₂.factorization p * Nat.log c₂ n) :
    p ^ (max (c₁.factorization p * Nat.log c₁ n)
          (c₂.factorization p * Nat.log c₂ n) - padicValInt p h) ∣
      (NormalNumbers.StonehamSumsNormal.stonehamState b 1
        ![c₁, c₂] ![1, 1] ![h, -h] n).den := by
  have hdiv := prime_pow_max_dvd_pairFamilies_sub_den_of_depth_ne
    p b c₁ c₂ (Nat.log c₁ n) (Nat.log c₂ n) n hp hc₁0 hc₂0
      hcb₁ hcb₂ hK₁ hK₂ hentered₁ hentered₂ hne
  have hdiv' : p ^ max (c₁.factorization p * Nat.log c₁ n)
      (c₂.factorization p * Nat.log c₂ n) ∣
      ((∑ j ∈ Finset.Icc 1 (Nat.log c₁ n),
          (b : ℚ) ^ (n - c₁ ^ j) / (c₁ : ℚ) ^ j) +
        ((-1 : ℤ) : ℚ) * (∑ j ∈ Finset.Icc 1 (Nat.log c₂ n),
          (b : ℚ) ^ (n - c₂ ^ j) / (c₂ : ℚ) ^ j)).den := by
    simpa [sub_eq_add_neg] using hdiv
  simpa [sub_eq_add_neg] using
    prime_pow_sub_padicValInt_dvd_stonehamState_pair_one_den
      p (max (c₁.factorization p * Nat.log c₁ n)
        (c₂.factorization p * Nat.log c₂ n)) b c₁ c₂ n h (-1) hp hh hdiv'

end NormalNumbers.StonehamPairsNormal
