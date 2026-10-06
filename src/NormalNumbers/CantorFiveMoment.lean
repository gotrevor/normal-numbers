/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouvilleAll

/-!
# Base-5 coin points and their second moment

The base-5 coin point `ptF free ω = Σ dᵢ 5^{−i−1}`, `dᵢ = 3·ω(2i) + ω(2i+1) ∈ {0,1,3,4}` on free
places, `0` on forced ones.  This file ports the Cassels second-moment route of
`CantorLiouville`/`CantorLiouvilleAll` from base 3 to base 5:

* `charFun_realF`: `|𝔼 e(ξ x)| ≤ Π_{free p < M} φ₅(ξ/5^{p+1})`, `φ₅(t) = |1+e(t)+e(3t)+e(4t)|/4`;
* `five_point`: `Σ_{s<5} φ₅(x + s/5) ≤ 5/2` (Parseval: `Σ φ₅² = 5/4`, then Cauchy–Schwarz),
  the analogue of Cassels' three-point bound `≤ 2`;
* the residue/orbit sums for `5 ∤ b` via `b⁴ ≡ 1 (mod 5)` and lifting the exponent.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorFiveMoment

open DecayAeNormal ExplicitSquare CantorSelfSimilar CantorLiouville

/-! ## The point -/

/-- Free position `i` carries the base-5 digit `3·ω(2i) + ω(2i+1) ∈ {0,1,3,4}`; forced ones `0`. -/
def ptDigitF (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ℕ :=
  if free i then 3 * (ω (2 * i)).toNat + (ω (2 * i + 1)).toNat else 0

/-- The point coded by coins `ω`. -/
noncomputable def ptF (free : ℕ → Bool) (ω : ℕ → Bool) : ℝ := realOfDigits 5 (ptDigitF free ω)

theorem ptDigitF_lt (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) :
    ptDigitF free ω i < 5 ∧ ptDigitF free ω i ≠ 2 := by
  unfold ptDigitF; split_ifs <;> cases ω (2 * i) <;> cases ω (2 * i + 1) <;> simp

theorem ptDigitF_le_four (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : ptDigitF free ω i ≤ 4 :=
  Nat.lt_succ_iff.1 (ptDigitF_lt free ω i).1

theorem summable_ptDigitF (free : ℕ → Bool) (ω : ℕ → Bool) :
    Summable fun i => (ptDigitF free ω i : ℝ) / (5 : ℝ) ^ (i + 1) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_geometric_of_lt_one (r := (5 : ℝ)⁻¹) (by norm_num) (by norm_num)))
  have : (ptDigitF free ω i : ℝ) ≤ 5 := by exact_mod_cast (ptDigitF_lt free ω i).1.le
  rw [inv_pow, div_le_iff₀ (by positivity), pow_succ, inv_mul_cancel_left₀ (by positivity)]
  exact this

theorem measurable_ptF (free : ℕ → Bool) : Measurable (ptF free) := by
  unfold ptF realOfDigits
  refine Measurable.tsum fun i => Measurable.div_const ?_ _
  refine Measurable.comp (measurable_of_countable (fun n : ℕ => (n : ℝ))) ?_
  unfold ptDigitF
  have h1 : Measurable fun ω : ℕ → Bool => ω (2 * i) := measurable_pi_apply _
  have h2 : Measurable fun ω : ℕ → Bool => ω (2 * i + 1) := measurable_pi_apply _
  have : Measurable fun ω : ℕ → Bool => (ω (2 * i), ω (2 * i + 1)) := h1.prodMk h2
  exact (measurable_of_countable (fun q : Bool × Bool =>
    if free i then 3 * q.1.toNat + q.2.toNat else 0)).comp this

/-- Peeling one digit (two coins). -/
theorem ptF_cons (free : ℕ → Bool) (c₀ c₁ : Bool) (ω : ℕ → Bool) :
    ptF free (consB c₀ (consB c₁ ω)) =
      (if free 0 then (3 * c₀.toNat + c₁.toNat : ℕ) else (0 : ℕ)) / 5 +
        ptF (fun i => free (i + 1)) ω / 5 := by
  unfold ptF realOfDigits
  simp only [Nat.cast_ofNat]
  rw [(summable_ptDigitF free (consB c₀ (consB c₁ ω))).tsum_eq_zero_add, ← tsum_div_const]
  congr 1
  · simp only [ptDigitF, consB, zero_add, pow_one]
    split_ifs <;> simp
  · refine tsum_congr fun i => ?_
    have e1 : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
    simp only [ptDigitF, e1, consB]
    rw [pow_succ _ (i + 1)]; field_simp

/-! ## The per-digit factor -/

/-- `φ₅(t) = |1 + e(t) + e(3t) + e(4t)| / 4`, the modulus of the digit characteristic function. -/
noncomputable def phiF (t : ℝ) : ℝ := ‖(1 + ee t + ee (3 * t) + ee (4 * t)) / 4‖

theorem phiF_nonneg (t : ℝ) : 0 ≤ phiF t := norm_nonneg _

theorem phiF_le_one (t : ℝ) : phiF t ≤ 1 := by
  unfold phiF
  rw [norm_div]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4, div_le_one (by norm_num)]
  calc ‖1 + ee t + ee (3 * t) + ee (4 * t)‖ ≤ ‖1 + ee t + ee (3 * t)‖ + ‖ee (4 * t)‖ := norm_add_le _ _
    _ ≤ ‖1 + ee t‖ + ‖ee (3 * t)‖ + ‖ee (4 * t)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖(1 : ℂ)‖ + ‖ee t‖ + ‖ee (3 * t)‖ + ‖ee (4 * t)‖ := by gcongr; exact norm_add_le _ _
    _ = 4 := by simp [norm_ee]; norm_num

theorem ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by push_cast; ring⟩

theorem ee_add_int (t : ℝ) (n : ℤ) : ee (t + n) = ee t := by
  rw [ee_add, ee_int, mul_one]

theorem phiF_add_int (t : ℝ) (n : ℤ) : phiF (t + n) = phiF t := by
  unfold phiF
  have h3 : 3 * (t + n) = 3 * t + ((3 * n : ℤ) : ℝ) := by push_cast; ring
  have h4 : 4 * (t + n) = 4 * t + ((4 * n : ℤ) : ℝ) := by push_cast; ring
  rw [h3, h4, ee_add_int, ee_add_int, ee_add_int]

theorem phiF_neg (t : ℝ) : phiF (-t) = phiF t := by
  unfold phiF
  rw [← norm_star]
  congr 1
  simp only [star_div₀, star_add, star_one, RCLike.star_def, conj_ee, map_ofNat]
  ring_nf

/-! ## Characteristic function -/

theorem integral_split (g : (ℕ → Bool) → ℂ) (hgm : Measurable g) (hgb : ∀ ω, ‖g ω‖ ≤ 1) :
    ∫ ω, g ω ∂coinMeasure =
      2⁻¹ * ∫ ω, g (consB true ω) ∂coinMeasure + 2⁻¹ * ∫ ω, g (consB false ω) ∂coinMeasure := by
  have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  conv_lhs => rw [coinMeasure_eq]
  rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
      ((hgi _ inferInstance).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure,
    integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
    integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
  simp [ENNReal.toReal_inv]

/-- **Riesz-product bound, base 5.** -/
theorem charFun_realF (M : ℕ) : ∀ (free : ℕ → Bool) (ξ : ℝ),
    ‖∫ ω, ee (ξ * ptF free ω) ∂coinMeasure‖ ≤
      ∏ p ∈ (Finset.range M).filter (fun p => free p = true), phiF (ξ / 5 ^ (p + 1)) := by
  induction M with
  | zero =>
    intro free ξ
    simp only [Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    refine (norm_integral_le_of_norm_le_const (C := 1)
      (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
    simp
  | succ M ih =>
    intro free ξ
    set free' : ℕ → Bool := fun i => free (i + 1)
    set I' := ∫ ω, ee (ξ / 5 * ptF free' ω) ∂coinMeasure
    have hm : ∀ (c₀ c₁ : Bool), Measurable fun ω => ee (ξ * ptF free (consB c₀ (consB c₁ ω))) :=
      fun c₀ c₁ => measurable_ee.comp (((measurable_ptF free).comp
        ((measurable_consB c₀).comp (measurable_consB c₁))).const_mul ξ)
    have hc : ∀ c₀ c₁ : Bool, ∫ ω, ee (ξ * ptF free (consB c₀ (consB c₁ ω))) ∂coinMeasure =
        ee (ξ * ((if free 0 then (3 * c₀.toNat + c₁.toNat : ℕ) else (0 : ℕ)) / 5)) * I' := by
      intro c₀ c₁
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [ptF_cons, ← ee_add]
      congr 1; ring
    have hs1 := integral_split (fun ω => ee (ξ * ptF free ω))
      (measurable_ee.comp ((measurable_ptF free).const_mul ξ)) (fun ω => (norm_ee _).le)
    have hs2 : ∀ c₀ : Bool, ∫ ω, ee (ξ * ptF free (consB c₀ ω)) ∂coinMeasure =
        2⁻¹ * ∫ ω, ee (ξ * ptF free (consB c₀ (consB true ω))) ∂coinMeasure +
          2⁻¹ * ∫ ω, ee (ξ * ptF free (consB c₀ (consB false ω))) ∂coinMeasure := fun c₀ =>
      integral_split (fun ω => ee (ξ * ptF free (consB c₀ ω)))
        (measurable_ee.comp (((measurable_ptF free).comp (measurable_consB c₀)).const_mul ξ))
        (fun ω => (norm_ee _).le)
    have hI' := ih free' (ξ / 5)
    rw [hs1, hs2, hs2, hc, hc, hc, hc, Finset.prod_filter, Finset.prod_range_succ',
      ← Finset.prod_filter]
    have hre : ∏ p ∈ (Finset.range M).filter (fun p => free (p + 1) = true),
        phiF (ξ / 5 ^ (p + 1 + 1)) =
        ∏ p ∈ (Finset.range M).filter (fun p => free' p = true), phiF (ξ / 5 / 5 ^ (p + 1)) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      congr 1; rw [pow_succ]; ring
    rw [hre]
    by_cases h0 : free 0 = true
    · simp only [h0, if_true]
      have : 2⁻¹ * (2⁻¹ * (ee (ξ * (((3 * true.toNat + true.toNat : ℕ) : ℝ) / 5)) * I') +
            2⁻¹ * (ee (ξ * (((3 * true.toNat + false.toNat : ℕ) : ℝ) / 5)) * I')) +
          2⁻¹ * (2⁻¹ * (ee (ξ * (((3 * false.toNat + true.toNat : ℕ) : ℝ) / 5)) * I') +
            2⁻¹ * (ee (ξ * (((3 * false.toNat + false.toNat : ℕ) : ℝ) / 5)) * I')) =
          ((1 + ee (ξ / 5) + ee (3 * (ξ / 5)) + ee (4 * (ξ / 5))) / 4) * I' := by
        have e0 : ee 0 = 1 := by simpa using ee_int 0
        simp only [Bool.toNat_true, Bool.toNat_false]
        norm_num
        rw [e0]
        ring_nf
      have hφ : ‖(1 + ee (ξ / 5) + ee (3 * (ξ / 5)) + ee (4 * (ξ / 5))) / 4‖ =
          phiF (ξ / 5 ^ (0 + 1)) := by simp [phiF]
      rw [this, norm_mul, mul_comm, hφ]
      exact mul_le_mul_of_nonneg_right hI' (norm_nonneg _)
    · simp only [Bool.not_eq_true] at h0
      simp only [h0, Bool.false_eq_true, if_false, Nat.cast_zero, zero_div, mul_zero]
      have e0 : ee 0 = 1 := by simpa using ee_int 0
      rw [e0, mul_one]
      have : 2⁻¹ * (2⁻¹ * (1 * I') + 2⁻¹ * (1 * I')) + 2⁻¹ * (2⁻¹ * (1 * I') + 2⁻¹ * (1 * I'))
          = I' := by ring
      rw [this]
      exact hI'

/-! ## The five-point bound -/

theorem ee_pow (t : ℝ) (n : ℕ) : ee t ^ n = ee (n * t) := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem ee_ne_one_of_not_dvd (k : ℤ) (hk : ¬ (5 : ℤ) ∣ k) : ee ((k : ℝ) / 5) ≠ 1 := by
  intro h
  unfold ee at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((k : ℝ) / 5 : ℂ) = n := by
    have : 2 * Real.pi * Complex.I * (((k : ℝ) / 5 : ℝ) : ℂ) = 2 * Real.pi * Complex.I * n := by
      rw [hn]; ring
    exact_mod_cast mul_left_cancel₀ hpi this
  have h3 : (k : ℂ) = ((5 * n : ℤ) : ℂ) := by
    push_cast at h2 ⊢
    field_simp at h2
    linear_combination h2
  exact hk ⟨n, by exact_mod_cast h3⟩

/-- Five equally spaced characters sum to zero. -/
theorem sum_five_ee (k : ℤ) (hk : ¬ (5 : ℤ) ∣ k) (x : ℝ) :
    ∑ s ∈ Finset.range 5, ee (k * (x + s / 5)) = 0 := by
  set ζ := ee ((k : ℝ) / 5)
  have hs : ∀ s : ℕ, ee (k * (x + s / 5)) = ee (k * x) * ζ ^ s := by
    intro s
    rw [ee_pow, ← ee_add]; congr 1; ring
  simp_rw [hs, ← Finset.mul_sum]
  have h5 : ζ ^ 5 = 1 := by
    rw [ee_pow]; push_cast
    rw [show (5 : ℝ) * (k / 5) = ((k : ℤ) : ℝ) by ring, ee_int]
  have hg := geom_sum_mul ζ 5
  rw [h5, sub_self] at hg
  have : ∑ i ∈ Finset.range 5, ζ ^ i = 0 :=
    (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 (ee_ne_one_of_not_dvd k hk))
  rw [this, mul_zero]

theorem phiF_sq_sum (x : ℝ) : ∑ s ∈ Finset.range 5, phiF (x + s / 5) ^ 2 = 5 / 4 := by
  have key : ∀ t : ℝ, ((phiF t : ℝ) : ℂ) ^ 2 =
      (1 / 16 : ℂ) * (4 + ee (1 * t) + ee (-1 * t) + ee (3 * t) + ee (-3 * t) + ee (4 * t) +
        ee (-4 * t) + ee (2 * t) + ee (-2 * t) + ee (3 * t) + ee (-3 * t) + ee (1 * t) +
        ee (-1 * t)) := by
    intro t
    rw [← Complex.ofReal_pow]
    simp only [one_mul, neg_mul]
    unfold phiF
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [map_div₀, map_add, map_one, conj_ee, map_ofNat]
    have e : ∀ a b : ℝ, ee a * ee b = ee (a + b) := fun a b => (ee_add a b).symm
    have e0 : ee 0 = 1 := by simpa using ee_int 0
    ring_nf
    simp only [e]
    ring_nf
    rw [e0]
    ring_nf
  have hsum : ∀ k : ℤ, ¬ (5 : ℤ) ∣ k →
      ∑ s ∈ Finset.range 5, ee (k * (x + (s : ℝ) / 5)) = 0 := fun k hk => sum_five_ee k hk x
  have h1 := hsum 1 (by decide)
  have h2 := hsum 2 (by decide)
  have h3 := hsum 3 (by decide)
  have h4 := hsum 4 (by decide)
  have hm1 := hsum (-1) (by decide)
  have hm2 := hsum (-2) (by decide)
  have hm3 := hsum (-3) (by decide)
  have hm4 := hsum (-4) (by decide)
  push_cast at h1 h2 h3 h4 hm1 hm2 hm3 hm4
  apply Complex.ofReal_injective
  push_cast
  simp_rw [key]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  rw [h1, h2, h3, h4, hm1, hm2, hm3, hm4]
  norm_num

/-- **Five-point bound** (Cassels' three-point bound, base 5). -/
theorem five_point (x : ℝ) : ∑ s ∈ Finset.range 5, phiF (x + s / 5) ≤ 5 / 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range 5) (f := fun s : ℕ => phiF (x + s / 5))
  rw [phiF_sq_sum, Finset.card_range] at hcs
  have h0 : 0 ≤ ∑ s ∈ Finset.range 5, phiF (x + s / 5) :=
    Finset.sum_nonneg fun _ _ => phiF_nonneg _
  nlinarith

/-! ## Riesz majorants -/

open CantorLiouvilleAll

/-- The Riesz majorant at offset `v`, base 5. -/
noncomputable def HfF (free : ℕ → Bool) (v k : ℕ) (u : ℝ) : ℝ :=
  ∏ p ∈ posSet free v k, phiF (5 ^ v * u / 5 ^ (p + 1))

theorem HfF_nonneg (free : ℕ → Bool) (v k : ℕ) (u : ℝ) : 0 ≤ HfF free v k u :=
  Finset.prod_nonneg fun _ _ => phiF_nonneg _

theorem HfF_le_one (free : ℕ → Bool) (v k : ℕ) (u : ℝ) : HfF free v k u ≤ 1 :=
  Finset.prod_le_one (fun _ _ => phiF_nonneg _) fun _ _ => phiF_le_one _

theorem HfF_periodic (free : ℕ → Bool) (v k : ℕ) (u : ℝ) (s : ℤ) :
    HfF free v k (u + 5 ^ k * s) = HfF free v k u := by
  unfold HfF
  refine Finset.prod_congr rfl fun p hp => ?_
  simp only [posSet, Finset.mem_filter, Finset.mem_range] at hp
  have he : (5 : ℝ) ^ v * 5 ^ k = 5 ^ (p + 1) * 5 ^ (v + k - (p + 1)) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have : 5 ^ v * (u + 5 ^ k * s) / 5 ^ (p + 1) =
      5 ^ v * u / 5 ^ (p + 1) + ((s * 5 ^ (v + k - (p + 1)) : ℤ) : ℝ) := by
    have h5 : (5 : ℝ) ^ (p + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    linear_combination (s : ℝ) * he
  rw [this, phiF_add_int]

theorem HfF_succ (free : ℕ → Bool) (v k : ℕ) (hk : 1 ≤ k) (u : ℝ) :
    HfF free v (k + 1) u = HfF free v k u *
      (if free (v + k) = true then phiF (5 ^ v * u / 5 ^ (v + k + 1)) else 1) := by
  unfold HfF posSet
  rw [show v + (k + 1) = (v + k) + 1 by ring, Finset.range_add_one, Finset.filter_insert]
  by_cases hf : free (v + k) = true
  · rw [if_pos ⟨by omega, hf⟩, Finset.prod_insert (by simp), if_pos hf, mul_comm]
  · rw [if_neg (fun h => hf h.2), if_neg hf, mul_one]

theorem HfF_mod (free : ℕ → Bool) (v k n : ℕ) :
    HfF free v k ((n % 5 ^ k : ℕ) : ℝ) = HfF free v k n := by
  have := HfF_periodic free v k ((n % 5 ^ k : ℕ) : ℝ) ((n / 5 ^ k : ℕ) : ℤ)
  rw [← this]; congr 1
  have h := Nat.mod_add_div n (5 ^ k)
  have h' : ((n % 5 ^ k : ℕ) : ℝ) + ((5 ^ k * (n / 5 ^ k) : ℕ) : ℝ) = n := by
    rw [← Nat.cast_add, h]
  push_cast at h'
  rw [Int.cast_natCast]; linarith

/-- Residue bound from level `t`, base 5. -/
theorem residue_sum_fromF (free : ℕ → Bool) (v t : ℕ) (ht : 1 ≤ t) : ∀ n r : ℕ,
    ∑ w ∈ Finset.range (5 ^ n), HfF free v (t + n) ((5 ^ t * w + r : ℕ) : ℝ) ≤
      5 ^ n * (1 / 2 : ℝ) ^ (posSet free v (t + n)).card * 2 ^ (posSet free v t).card := by
  intro n
  induction n with
  | zero =>
    intro r
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, add_zero, one_mul]
    rw [← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow]
    exact HfF_le_one _ _ _ _
  | succ n ih =>
    intro r
    set k := t + n
    have hk : 1 ≤ k := by omega
    rw [show t + (n + 1) = k + 1 by omega, pow_succ, sum_range_mul_eq, Finset.sum_comm]
    have hstep : ∀ w ∈ Finset.range (5 ^ n),
        ∑ s ∈ Finset.range 5, HfF free v (k + 1) ((5 ^ t * (5 ^ n * s + w) + r : ℕ) : ℝ) ≤
        (if free (v + k) = true then 5 / 2 else 5) * HfF free v k ((5 ^ t * w + r : ℕ) : ℝ) := by
      intro w _
      have hrw : ∀ s : ℕ, ((5 ^ t * (5 ^ n * s + w) + r : ℕ) : ℝ) =
          ((5 ^ t * w + r : ℕ) : ℝ) + 5 ^ k * (s : ℤ) := by
        intro s; push_cast; simp only [k]; rw [pow_add]; ring
      have hper : ∀ s : ℕ, HfF free v k ((5 ^ t * (5 ^ n * s + w) + r : ℕ) : ℝ) =
          HfF free v k ((5 ^ t * w + r : ℕ) : ℝ) := by
        intro s; rw [hrw, HfF_periodic]
      simp_rw [HfF_succ free v k hk, hper, ← Finset.mul_sum]
      rw [mul_comm]
      gcongr
      · exact HfF_nonneg _ _ _ _
      by_cases hf : free (v + k) = true
      · simp only [hf, if_true]
        have := five_point (5 ^ v * ((5 ^ t * w + r : ℕ) : ℝ) / 5 ^ (v + k + 1))
        refine le_of_eq_of_le (Finset.sum_congr rfl fun s _ => ?_) this
        congr 1
        rw [hrw]
        push_cast
        field_simp
        ring
      · simp [hf]
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum, posSet_card_succ free v k hk]
    have := ih r
    by_cases hf : free (v + k) = true
    · simp only [hf, if_true]
      calc (5 / 2 : ℝ) * _ ≤ 5 / 2 * (5 ^ n * (1 / 2 : ℝ) ^ (posSet free v k).card *
            2 ^ (posSet free v t).card) := by gcongr
        _ = _ := by rw [pow_succ, pow_succ]; ring
    · simp only [hf, if_false, Bool.false_eq_true, add_zero]
      calc (5 : ℝ) * _ ≤ 5 * (5 ^ n * (1 / 2 : ℝ) ^ (posSet free v k).card *
            2 ^ (posSet free v t).card) := by gcongr
        _ = _ := by rw [pow_succ]; ring

/-! ## Arithmetic: bases coprime to 5 -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The 5-adic defect `t = v₅(b⁴ − 1)` of a base coprime to 5. -/
def tbF (b : ℕ) : ℕ := padicValNat 5 (b ^ 4 - 1)

theorem five_dvd_four_sub_one {b : ℕ} (h5 : ¬ 5 ∣ b) : 5 ∣ b ^ 4 - 1 := by
  have : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]

theorem padicValNat_four_pow_sub_oneF {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) {d : ℕ} (hd : d ≠ 0) :
    padicValNat 5 ((b ^ 4) ^ d - 1) = tbF b + padicValNat 5 d := by
  have := padicValNat.pow_sub_pow (p := 5) (x := b ^ 4) (y := 1) (by decide)
    (by have := Nat.pow_le_pow_left hb 4; norm_num at this; omega)
    (by simpa using five_dvd_four_sub_one h5)
    (fun h => h5 (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)) (n := d) hd
  simpa [tbF] using this

theorem padicValNat_pow_sub_one_leF {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) {d : ℕ} (hd : d ≠ 0) :
    padicValNat 5 (b ^ d - 1) ≤ tbF b + padicValNat 5 d := by
  have h4 : padicValNat 5 ((b ^ 4) ^ d - 1) = tbF b + padicValNat 5 d :=
    padicValNat_four_pow_sub_oneF hb h5 hd
  rw [← h4]
  have hne : (b ^ 4) ^ d - 1 ≠ 0 := by
    have : 2 ≤ (b ^ 4) ^ d := le_trans (by nlinarith [Nat.one_le_pow 3 b (by omega)])
      (Nat.le_self_pow hd _)
    omega
  rw [← padicValNat_dvd_iff_le hne]
  refine (pow_padicValNat_dvd).trans ?_
  have := Nat.sub_dvd_pow_sub_pow (x := b ^ d) (y := 1) (n := 4)
  rwa [one_pow, ← pow_mul, mul_comm, pow_mul] at this

theorem five_pow_tbF_lt {b : ℕ} (hb : 2 ≤ b) : 5 ^ tbF b < b ^ 4 := by
  have h16 : 16 ≤ b ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ b ^ 4 := Nat.pow_le_pow_left hb 4
  have hne : b ^ 4 - 1 ≠ 0 := by omega
  have h1 : 5 ^ tbF b ≤ b ^ 4 - 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  omega

theorem one_le_tbF {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) : 1 ≤ tbF b := by
  have h16 : 16 ≤ b ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ b ^ 4 := Nat.pow_le_pow_left hb 4
  have hne : b ^ 4 - 1 ≠ 0 := by omega
  exact one_le_padicValNat_of_dvd hne (five_dvd_four_sub_one h5)

theorem coprime_five_pow {x : ℕ} (hx : ¬ 5 ∣ x) (k : ℕ) : Nat.Coprime x (5 ^ k) :=
  Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hx).symm

theorem five_pow_dvd_four_pow_sub_one {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) {k d : ℕ} (hd : d ≠ 0) :
    5 ^ k ∣ (b ^ 4) ^ d - 1 ↔ k ≤ tbF b + padicValNat 5 d := by
  have hne : (b ^ 4) ^ d - 1 ≠ 0 := by
    have : 2 ≤ (b ^ 4) ^ d := le_trans (by nlinarith [Nat.one_le_pow 3 b (by omega)])
      (Nat.le_self_pow hd _)
    omega
  rw [padicValNat_dvd_iff_le hne, padicValNat_four_pow_sub_oneF hb h5 hd]

theorem four_pow_modEq_one {b : ℕ} (m : ℕ) : (b ^ 4) ^ m ≡ 1 [MOD 5 ^ tbF b] := by
  have h1 : b ^ 4 ≡ 1 [MOD 5 ^ tbF b] := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [tbF, Nat.modEq_one]
    refine ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb)).2 pow_padicValNat_dvd).symm
  simpa using h1.pow m

theorem orbit_sum_eqF (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (v n x : ℕ)
    (hx : ¬ 5 ∣ x) :
    ∑ m ∈ Finset.range (5 ^ n), HfF free v (tbF b + n) ((x * (b ^ 4) ^ m : ℕ) : ℝ) =
      ∑ w ∈ Finset.range (5 ^ n), HfF free v (tbF b + n) ((5 ^ tbF b * w + x % 5 ^ tbF b : ℕ) : ℝ) := by
  set t := tbF b
  set k := t + n
  set Q := 5 ^ k
  have hQ : Q = 5 ^ t * 5 ^ n := pow_add _ _ _
  have htQ : 5 ^ t ∣ Q := ⟨_, hQ⟩
  set φ : ℕ → ℕ := fun m => (x * (b ^ 4) ^ m % Q) / 5 ^ t
  have hmod : ∀ m, (x * (b ^ 4) ^ m % Q) % 5 ^ t = x % 5 ^ t := by
    intro m
    rw [Nat.mod_mod_of_dvd _ htQ]
    have := (four_pow_modEq_one (b := b) m).mul_left x
    rw [mul_one] at this
    exact this
  have hrec : ∀ m, x * (b ^ 4) ^ m % Q = 5 ^ t * φ m + x % 5 ^ t := by
    intro m; rw [← hmod m]; exact (Nat.div_add_mod _ _).symm
  have hmaps : ∀ m ∈ Finset.range (5 ^ n), φ m ∈ Finset.range (5 ^ n) := by
    intro m _
    simp only [Finset.mem_range, φ]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc _ < Q := Nat.mod_lt _ (by positivity)
      _ = _ := by rw [hQ, mul_comm]
  have hinj : Set.InjOn φ (Finset.range (5 ^ n) : Set ℕ) := by
    have key : ∀ m m', m < m' → m' < 5 ^ n → φ m ≠ φ m' := by
      intro m m' hmm' hm' heq
      have h1 : x * (b ^ 4) ^ m ≡ x * (b ^ 4) ^ m * (b ^ 4) ^ (m' - m) [MOD Q] := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmm'.le]
        unfold Nat.ModEq; rw [hrec, hrec, heq]
      have hcop : Nat.Coprime Q (x * (b ^ 4) ^ m) :=
        (Nat.Coprime.mul_left (coprime_five_pow hx k)
          (Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ (coprime_five_pow h5 k)))).symm
      have h2 : 1 ≡ (b ^ 4) ^ (m' - m) [MOD Q] :=
        Nat.ModEq.cancel_left_of_coprime hcop (by simpa using h1)
      have hd : m' - m ≠ 0 := by omega
      have h4 := (five_pow_dvd_four_pow_sub_one hb h5 hd).1
        ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by positivity))).1 h2)
      have h5' : 5 ^ padicValNat 5 (m' - m) ≤ m' - m := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
      have h6 : 5 ^ n ≤ 5 ^ padicValNat 5 (m' - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    intro m hm m' hm' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hm hm'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key m m' h hm' heq
    · exact key m' m h hm heq.symm
  refine Finset.sum_nbij φ hmaps hinj
    (Finset.surjOn_of_injOn_of_card_le _ hmaps hinj le_rfl) ?_
  intro m _
  rw [← hrec, HfF_mod]

/-- **Coset version of the partial-period sum, base 5.**  As `sum_Hf_le_b`, with `b⁴` in
place of `b²` (four interleaved sub-orbits). -/
theorem sum_HfF_le_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (v j c : ℕ)
    (hc : ¬ 5 ∣ c) (N : ℕ) :
    ∑ m ∈ Finset.range N, HfF free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤
      (N + 4 * 5 ^ j) * 2 ^ tbF b * (1 / 2 : ℝ) ^ (posSet free v (j + 1)).card := by
  set t := tbF b
  have ht := one_le_tbF hb h5
  set ck := (posSet free v (j + 1)).card
  have hck := posSet_card_le free v (j + 1)
  have hf0 : ∀ u, 0 ≤ HfF free v (j + 1) u := fun u => HfF_nonneg _ _ _ _
  by_cases hjt : j + 1 < t
  · have h1 : ∑ m ∈ Finset.range N, HfF free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤ N := by
      refine (Finset.sum_le_sum fun m _ => HfF_le_one free v (j + 1) _).trans ?_
      simp
    have h2 : (1 : ℝ) ≤ 2 ^ t * (1 / 2 : ℝ) ^ ck := by
      have : (1 / 2 : ℝ) ^ t ≤ (1 / 2 : ℝ) ^ ck :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have e : (2 : ℝ) ^ t * (1 / 2 : ℝ) ^ t = 1 := by rw [← mul_pow]; norm_num
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) t]
    have h3' : (0 : ℝ) ≤ 4 * 5 ^ j := by positivity
    rw [mul_assoc]
    nlinarith
  push Not at hjt
  obtain ⟨n, hn⟩ : ∃ n, j + 1 = t + n := ⟨j + 1 - t, by omega⟩
  set P := 5 ^ n
  set B : ℝ := (1 / 2 : ℝ) ^ ck * 2 ^ (posSet free v t).card
  have hB0 : 0 ≤ B := by positivity
  set g : ℕ → ℕ → ℝ := fun x m => HfF free v (j + 1) ((x * (b ^ 4) ^ m : ℕ) : ℝ)
  have hgK : ∀ x, ¬ 5 ∣ x → ∀ K, ∑ m ∈ Finset.range K, g x m ≤ (K + P) * B := by
    intro x hx K
    refine sum_periodic_le (g x) (fun m => hf0 _) P (by positivity) ?_ B ?_ K
    · intro m
      obtain ⟨s, hs⟩ := (five_pow_dvd_four_pow_sub_one hb h5 (k := j + 1) (d := P)
        (by positivity)).2 (by simp [P]; omega)
      have hP1 : 1 ≤ (b ^ 4) ^ P := Nat.one_le_pow _ _ (by positivity)
      have : x * (b ^ 4) ^ (m + P) = x * (b ^ 4) ^ m + 5 ^ (j + 1) * (x * (b ^ 4) ^ m * s) := by
        rw [pow_add, show (b ^ 4) ^ P = 5 ^ (j + 1) * s + 1 by omega]; ring
      simp only [g]
      rw [this]
      have := HfF_periodic free v (j + 1) ((x * (b ^ 4) ^ m : ℕ) : ℝ) ((x * (b ^ 4) ^ m * s : ℕ) : ℤ)
      rw [← this]; congr 1; push_cast; ring
    · simp only [g]
      rw [hn, orbit_sum_eqF free hb h5 v n x hx, ← hn]
      have := residue_sum_fromF free v t ht n (x % 5 ^ t)
      rw [← hn] at this
      refine this.trans (le_of_eq ?_)
      simp only [B, P]; push_cast; ring
  set N' := (N + 3) / 4
  have hNN : N ≤ 4 * N' := by omega
  have hsplit : ∑ m ∈ Finset.range N, HfF free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤
      ∑ r ∈ Finset.range 4, ∑ m ∈ Finset.range N', g (c * b ^ r) m := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNN)
      (fun m _ _ => hf0 _)).trans (le_of_eq ?_)
    rw [sum_range_mul_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [g]
    congr 1; push_cast; ring
  have hcb : ∀ r, ¬ 5 ∣ c * b ^ r := fun r h =>
    ((Nat.Prime.dvd_mul (by norm_num)).1 h).elim hc
      (fun h' => h5 (Nat.Prime.dvd_of_dvd_pow (by norm_num) h'))
  have hct := posSet_card_le free v t
  have hBle : B ≤ (1 / 2 : ℝ) ^ ck * 2 ^ (t - 1) := by
    simp only [B]; gcongr; norm_num
  have hPj : (P : ℝ) ≤ 5 ^ j := by
    have : P ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hN' : (4 * N' : ℝ) ≤ N + 3 := by
    have : 4 * N' ≤ N + 3 := by omega
    exact_mod_cast this
  have h5j : (1 : ℝ) ≤ 5 ^ j := one_le_pow₀ (by norm_num)
  have ht' : (2 : ℝ) ^ t = 2 ^ (t - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hsum4 : ∑ r ∈ Finset.range 4, ∑ m ∈ Finset.range N', g (c * b ^ r) m ≤
      ∑ r ∈ Finset.range 4, ((N' : ℝ) + P) * B :=
    Finset.sum_le_sum fun r _ => hgK _ (hcb r) N'
  refine hsplit.trans (hsum4.trans ?_)
  rw [Finset.sum_const, Finset.card_range, ht']
  have hX : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ ck * 2 ^ (t - 1) := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  calc (4 : ℕ) • (((N' : ℝ) + P) * B) = (4 * N' + 4 * P) * B := by rw [nsmul_eq_mul]; push_cast; ring
    _ ≤ (4 * N' + 4 * P) * ((1 / 2 : ℝ) ^ ck * 2 ^ (t - 1)) := by gcongr
    _ ≤ (N + 4 * 5 ^ j) * 2 * ((1 / 2 : ℝ) ^ ck * 2 ^ (t - 1)) := by
        gcongr; linarith
    _ = _ := by ring

/-- The Riesz majorant of `|μ̂(ξ)|` (`charFun_realF`). -/
noncomputable def BfF (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range M).filter (fun p => free p = true), phiF (ξ / 5 ^ (p + 1))

theorem BfF_nonneg (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : 0 ≤ BfF free M ξ :=
  Finset.prod_nonneg fun _ _ => phiF_nonneg _

theorem BfF_le_one (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : BfF free M ξ ≤ 1 :=
  Finset.prod_le_one (fun _ _ => phiF_nonneg _) fun _ _ => phiF_le_one _

theorem BfF_neg (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : BfF free M (-ξ) = BfF free M ξ := by
  unfold BfF
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [neg_div, phiF_neg]

theorem BfF_abs (free : ℕ → Bool) (M : ℕ) (ξ : ℝ) : BfF free M |ξ| = BfF free M ξ := by
  rcases abs_cases ξ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]; rw [BfF_neg]

theorem BfF_le_HfF (free : ℕ → Bool) (v k : ℕ) (u : ℝ) :
    BfF free (v + k) (5 ^ v * u) ≤ HfF free v k u := by
  unfold BfF HfF
  have hsub : posSet free v k ⊆ (Finset.range (v + k)).filter (fun p => free p = true) := by
    intro p hp; simp only [posSet, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ p ∈ (Finset.range (v + k)).filter (fun p => free p = true) \ posSet free v k,
      phiF (5 ^ v * u / 5 ^ (p + 1)) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => phiF_nonneg _) fun _ _ => phiF_le_one _
  have h2 : 0 ≤ ∏ p ∈ posSet free v k, phiF (5 ^ v * u / 5 ^ (p + 1)) :=
    Finset.prod_nonneg fun _ _ => phiF_nonneg _
  nlinarith

theorem good_shift_bF (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (M N : ℕ)
    (hMN : 5 ^ M ≤ N) (c : ℕ) (hc : c ≠ 0)
    (hv : padicValNat 5 c + 1 ≤ freeCount free M / 2) :
    ∑ m ∈ Finset.range N, BfF free M ((c * b ^ m : ℕ) : ℝ) ≤
      2 * N * 2 ^ tbF b * (1 / 2 : ℝ) ^ (freeCount free M / 2) := by
  obtain ⟨v, c', hc', hcc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc 5 (by norm_num)
  have hvv : padicValNat 5 c = v := by
    rw [hcc, padicValNat.mul (by positivity) (by rintro rfl; simp at hc'),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hc', add_zero]
  rw [hvv] at hv
  have hFM : freeCount free M ≤ M := by
    unfold freeCount; exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨j, hj⟩ : ∃ j, M = v + (j + 1) := ⟨M - v - 1, by omega⟩
  have hterm : ∀ m, BfF free M ((c * b ^ m : ℕ) : ℝ) ≤ HfF free v (j + 1) ((c' * b ^ m : ℕ) : ℝ) := by
    intro m
    have := BfF_le_HfF free v (j + 1) ((c' * b ^ m : ℕ) : ℝ)
    rw [← hj] at this
    refine le_of_eq_of_le ?_ this
    congr 1; rw [hcc]; push_cast; ring
  have hcard := freeCount_le free v (j + 1)
  rw [← hj] at hcard
  have hL : (4 * 5 ^ j : ℝ) ≤ N := by
    have : 4 * 5 ^ j ≤ 5 ^ M := by
      rw [hj, pow_add, pow_succ]; nlinarith [Nat.one_le_pow v 5 (by norm_num), Nat.one_le_pow j 5 (by norm_num)]
    exact_mod_cast this.trans hMN
  calc _ ≤ ∑ m ∈ Finset.range N, HfF free v (j + 1) ((c' * b ^ m : ℕ) : ℝ) :=
        Finset.sum_le_sum fun m _ => hterm m
    _ ≤ (N + 4 * 5 ^ j) * 2 ^ tbF b * (1 / 2 : ℝ) ^ (posSet free v (j + 1)).card :=
        sum_HfF_le_b free hb h5 v j c' hc' N
    _ ≤ (2 * N) * 2 ^ tbF b * (1 / 2 : ℝ) ^ (freeCount free M / 2) := by
        gcongr ?_ * _ * ?_
        · linarith
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem bad_count_bF {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (e W N : ℕ) :
    ((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 5 (b ^ m - 1))).card ≤
      N / 5 ^ (W - e - tbF b) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card ?_
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hm ⊢
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  have h1 := padicValNat_pow_sub_one_leF hb h5 (d := m) (by omega)
  exact (padicValNat_dvd_iff_le (by omega)).2 (by omega)

/-! ## The second moment -/

theorem secondMoment_expand_bF (free : ℕ → Bool) (b : ℕ) (h : ℤ) (M N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, BfF free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) := by
  have hG := measurable_ptF free
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * ptF free ω)) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * ptF free ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * ptF free ω)]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * ptF free ω) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  refine Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun m _ => charFun_realF M free _

theorem half_pow_le (W : ℕ) (F : ℕ) (hW : W = F / 2) :
    (1 / 2 : ℝ) ^ W ≤ 2 * Real.exp (-(Real.log 2 / 2) * F) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 / 2 : ℝ) ^ W = Real.exp (-(W * Real.log 2)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
      show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    ring_nf
  have hWF : (F : ℝ) ≤ 2 * W + 1 := by
    have : F ≤ 2 * W + 1 := by omega
    exact_mod_cast this
  rw [h1, show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],
    ← Real.exp_add, Real.exp_log (by norm_num)]
  apply Real.exp_le_exp.2
  nlinarith

theorem secondMoment_le_explicit_bF (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 ∂coinMeasure ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
        4 * (5 ^ (padicValNat 5 h.natAbs + tbF b) + 2 * (2 : ℝ) ^ tbF b) * (N : ℝ) ^ 2 *
          Real.exp (-(Real.log 2 / 2) * freeCount free (Nat.log 5 N / 2)) := by
  set e := padicValNat 5 h.natAbs
  set t := tbF b
  set M := Nat.log 5 N / 2
  set F := freeCount free M
  set W := F / 2
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hMN : 5 ^ M ≤ N :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
      (Nat.pow_log_le_self 5 (by omega))
  set G : ℕ → ℕ → ℝ := fun d m => BfF free M (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m)
  have hpair := pair_sum_le (fun n m => BfF free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) G
    (fun d m => BfF_nonneg _ _ _) (fun n => BfF_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← BfF_neg]; congr 1
      rw [show (b : ℝ) ^ m = (b : ℝ) ^ (m - n) * (b : ℝ) ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  set P := (1 / 2 : ℝ) ^ W
  set T := (2 : ℝ) ^ t
  have hT : 0 ≤ T := by positivity
  have hshift : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      (if W ≤ e + padicValNat 5 (b ^ d - 1) then (N : ℝ) else 0) + 2 * N * T * P := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd1 : 1 ≤ b ^ d - 1 := by
      have : 2 ≤ b ^ d := le_trans hb (Nat.le_self_pow (by omega) b)
      omega
    split_ifs with hbad
    · refine (Finset.sum_le_sum fun m _ => BfF_le_one free M _).trans ?_
      have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
      simp; linarith
    · rw [zero_add]
      set c := h.natAbs * (b ^ d - 1)
      have hc : c ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.2 hh) (by omega)
      have hv : padicValNat 5 c = e + padicValNat 5 (b ^ d - 1) :=
        padicValNat.mul (Int.natAbs_ne_zero.2 hh) (by omega)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_)
        (good_shift_bF free hb h5 M N hMN c hc (by omega))
      simp only [G]
      rw [← BfF_abs]
      congr 1
      have hd2 : (0 : ℝ) ≤ (b : ℝ) ^ d - 1 := by
        have : (1:ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ hb1; linarith
      simp only [c]
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 0 < b))]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (b : ℝ) ^ m),
        abs_of_nonneg hd2, Nat.cast_natAbs, Int.cast_abs]
  have hsumd : ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      N * ((N / 5 ^ (W - e - t) : ℕ) : ℝ) + N * (2 * N * T * P) := by
    refine (Finset.sum_le_sum hshift).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico]
    have hbc := bad_count_bF hb h5 e W N
    have : (((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 5 (b ^ m - 1))).card : ℝ) ≤
        ((N / 5 ^ (W - e - t) : ℕ) : ℝ) := by exact_mod_cast hbc
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
    nlinarith
  have hdiv : ((N / 5 ^ (W - e - t) : ℕ) : ℝ) ≤ N * 5 ^ (e + t) * P := by
    have h1 : (N / 5 ^ (W - e - t)) * 5 ^ W ≤ N * 5 ^ (e + t) := by
      calc (N / 5 ^ (W - e - t)) * 5 ^ W ≤ (N / 5 ^ (W - e - t)) * (5 ^ (W - e - t) * 5 ^ (e + t)) := by
            gcongr; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (N / 5 ^ (W - e - t)) * 5 ^ (W - e - t) * 5 ^ (e + t) := by ring
        _ ≤ N * 5 ^ (e + t) := by gcongr; exact Nat.div_mul_le_self _ _
    have h2 : ((N / 5 ^ (W - e - t) : ℕ) : ℝ) * 5 ^ W ≤ N * 5 ^ (e + t) := by exact_mod_cast h1
    have h3' : (1 / 2 : ℝ) ^ W * 5 ^ W = (5 / 2) ^ W := by rw [← mul_pow]; norm_num
    have h4 : (1 : ℝ) ≤ (5 / 2) ^ W := one_le_pow₀ (by norm_num)
    have h5' : (0 : ℝ) < 5 ^ W := by positivity
    rw [← mul_le_mul_iff_of_pos_right h5']
    calc _ ≤ (N : ℝ) * 5 ^ (e + t) := h2
      _ ≤ (N : ℝ) * 5 ^ (e + t) * (5 / 2) ^ W := le_mul_of_one_le_right (by positivity) h4
      _ = _ := by rw [mul_assoc _ ((1 / 2 : ℝ) ^ W), h3']
  have hexp := half_pow_le W F rfl
  have hNr : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = N * N ^ (1 : ℝ) by rw [Real.rpow_one]; ring, mul_assoc,
        ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN0 (by norm_num)
    nlinarith
  have hI := (secondMoment_expand_bF free b h M N).trans hpair
  set E := Real.exp (-(Real.log 2 / 2) * F)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hfin : ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 ∂coinMeasure ≤
      N + 2 * ((N : ℝ) ^ 2 * (5 ^ (e + t) + 2 * T) * P) := by
    have := mul_le_mul_of_nonneg_left hdiv hN0
    nlinarith
  have hK : (0 : ℝ) ≤ 5 ^ (e + t) + 2 * T := by positivity
  calc _ ≤ N + 2 * ((N : ℝ) ^ 2 * (5 ^ (e + t) + 2 * T) * P) := hfin
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + 2 * ((N : ℝ) ^ 2 * (5 ^ (e + t) + 2 * T) * (2 * E)) := by
        gcongr
    _ = _ := by simp only [T, E, F, M]; ring

/-- **Cassels second moment, base `b` coprime to 5**, for the base-5 coin points. -/
theorem secondMoment_le_bF (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h5 : ¬ 5 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ptF free ω)‖ ^ 2 ∂coinMeasure ≤
      16 * (b : ℝ) ^ 6 * |(h : ℝ)| * (N : ℝ) ^ 2 *
        (Real.exp (-(Real.log 2 / 2) * freeCount free (Nat.log 5 N / 2)) +
          (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine (secondMoment_le_explicit_bF free hb h5 h hh N hN).trans ?_
  set e := padicValNat 5 h.natAbs
  set t := tbF b
  set E := Real.exp (-(Real.log 2 / 2) * freeCount free (Nat.log 5 N / 2))
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR : 0 ≤ R := by positivity
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have he : (5 : ℝ) ^ e ≤ |(h : ℝ)| := by
    have : 5 ^ e ≤ h.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hh) pow_padicValNat_dvd
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast this
  have ht : (5 : ℝ) ^ t ≤ (b : ℝ) ^ 4 := by exact_mod_cast (five_pow_tbF_lt hb).le
  have hT : (2 : ℝ) ^ t ≤ 5 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := le_trans (one_le_pow₀ (by norm_num)) he
  have hb4 : (b : ℝ) ^ 4 ≤ (b : ℝ) ^ 6 := pow_le_pow_right₀ hb1 (by norm_num)
  have hb6 : (1 : ℝ) ≤ (b : ℝ) ^ 6 := one_le_pow₀ hb1
  have h5t : (0 : ℝ) ≤ 5 ^ t := by positivity
  have hK : 4 * ((5 : ℝ) ^ (e + t) + 2 * (2 : ℝ) ^ t) ≤ 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
    rw [pow_add]
    have : (5 : ℝ) ^ e * 5 ^ t ≤ |(h : ℝ)| * 5 ^ t := by gcongr
    have : |(h : ℝ)| * 5 ^ t ≤ |(h : ℝ)| * (b : ℝ) ^ 6 := by gcongr; linarith
    have : (1 : ℝ) * 5 ^ t ≤ |(h : ℝ)| * 5 ^ t := by gcongr
    nlinarith
  have h16 : (1 : ℝ) ≤ 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by nlinarith
  have := mul_le_mul_of_nonneg_right hK (mul_nonneg hN2 hE)
  have := mul_le_mul_of_nonneg_right h16 (mul_nonneg hN2 hR)
  nlinarith

end NormalNumbers.CantorFiveMoment
