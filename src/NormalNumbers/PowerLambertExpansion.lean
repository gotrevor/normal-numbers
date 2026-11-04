/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerDivisorCoefficients
import NormalNumbers.CastingOutLambert

/-!
# Lambert expansion for power-indexed terms

The double series over `(n,k)` has exponent `(n+1)^r (k+1)`.  Summing in `k`
produces the power-indexed Lambert series; grouping by the exponent counts
power divisors.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

/-- Double-series term for the `r`-power Lambert expansion. -/
noncomputable def powerLambertTerm (b r : ℕ) (x : ℕ × ℕ) : ℝ :=
  1 / (b : ℝ) ^ ((x.1 + 1) ^ r * (x.2 + 1))

lemma powerLambertTerm_nonneg (b r : ℕ) (x : ℕ × ℕ) :
    0 ≤ powerLambertTerm b r x := by
  unfold powerLambertTerm
  positivity

lemma summable_powerLambertTerm {b r : ℕ} (hb : 2 ≤ b) (hr : 1 ≤ r) :
    Summable (powerLambertTerm b r) := by
  refine Summable.of_nonneg_of_le (powerLambertTerm_nonneg b r) (fun x => ?_)
    (NormalNumbers.CastingOut.summable_divPowTerm hb)
  have hx : x.1 + 1 ≤ (x.1 + 1) ^ r := by
    exact le_self_pow (by omega) (by omega)
  have hexp : (x.1 + 1) * (x.2 + 1) ≤ (x.1 + 1) ^ r * (x.2 + 1) :=
    Nat.mul_le_mul_right _ hx
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  unfold powerLambertTerm NormalNumbers.CastingOut.divPowTerm
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ hb' (by exact_mod_cast hexp))

/-- Summing over `k` gives one Lambert term. -/
lemma tsum_powerLambertTerm_snd {b r : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ∑' k : ℕ, powerLambertTerm b r (n, k) =
      1 / ((b : ℝ) ^ ((n + 1) ^ r) - 1) := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold powerLambertTerm
  simp only
  have hbp : (1 : ℝ) < (b : ℝ) ^ ((n + 1) ^ r) := by
    apply one_lt_pow₀ (by linarith)
    have : 0 < (n + 1) ^ r := Nat.pow_pos (by omega)
    omega
  set q : ℝ := 1 / (b : ℝ) ^ ((n + 1) ^ r) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; exact hbp
  have hfun :
      (fun k : ℕ => 1 / (b : ℝ) ^ ((n + 1) ^ r * (k + 1))) =
        fun k => q * q ^ k := by
    funext k
    rw [hq, pow_mul, pow_succ', ← one_div_mul_one_div, one_div_pow]
  rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, hq]
  have hne : (b : ℝ) ^ ((n + 1) ^ r) - 1 ≠ 0 := by linarith
  field_simp

/-- Exponent used to partition the double series. -/
def powerLambertIndex (r : ℕ) (x : ℕ × ℕ) : ℕ :=
  (x.1 + 1) ^ r * (x.2 + 1)

/-- A fiber of the index map is in bijection with the roots of power divisors. -/
lemma tsum_powerLambertTerm_fiber {b r : ℕ} (_hb : 2 ≤ b) (hr : 1 ≤ r) (m : ℕ) :
    ∑' x : (powerLambertIndex r ⁻¹' {m} : Set (ℕ × ℕ)), powerLambertTerm b r x =
      (powerDivisorCount r m : ℝ) / (b : ℝ) ^ m := by
  classical
  rw [_root_.tsum_subtype]
  set s : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (m + 1) with hs
  have hsupp : ∀ x ∉ s,
      (powerLambertIndex r ⁻¹' {m}).indicator (powerLambertTerm b r) x = 0 := by
    intro x hx
    rw [Set.indicator_apply_eq_zero]
    intro hxm
    simp only [Set.mem_preimage, Set.mem_singleton_iff, powerLambertIndex] at hxm
    exact absurd (by
      rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      constructor
      · have hbase : x.1 + 1 ≤ (x.1 + 1) ^ r :=
          le_self_pow (by omega) (by omega)
        have hmul : (x.1 + 1) ^ r ≤ (x.1 + 1) ^ r * (x.2 + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have : x.1 + 1 ≤ m := hxm ▸ (le_trans hbase hmul)
        omega
      · have hpow : 1 ≤ (x.1 + 1) ^ r :=
          Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        have hmul : x.2 + 1 ≤ (x.1 + 1) ^ r * (x.2 + 1) :=
          Nat.le_mul_of_pos_left _ hpow
        have : x.2 + 1 ≤ m := hxm ▸ hmul
        omega) hx
  rw [tsum_eq_sum hsupp]
  have hfilter : ∀ x ∈ s,
      (powerLambertIndex r ⁻¹' {m}).indicator (powerLambertTerm b r) x =
        if powerLambertIndex r x = m then 1 / (b : ℝ) ^ m else 0 := by
    intro x _
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hxm : powerLambertIndex r x = m
    · rw [if_pos hxm, if_pos hxm]
      unfold powerLambertTerm powerLambertIndex at *
      rw [hxm]
    · rw [if_neg hxm, if_neg hxm]
  rw [Finset.sum_congr rfl hfilter, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_one_div]
  have hcard :
      (s.filter (fun x => powerLambertIndex r x = m)).card = powerDivisorCount r m := by
    unfold powerDivisorCount
    refine Finset.card_bij' (fun x _ => x.1 + 1)
      (fun d _ => (d - 1, m / d ^ r - 1)) ?_ ?_ ?_ ?_
    · intro x hx
      have hxm : (x.1 + 1) ^ r * (x.2 + 1) = m := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter]
      constructor
      · rw [Nat.mem_divisors]
        have hr0 : r ≠ 0 := by omega
        have hdvd : x.1 + 1 ∣ m :=
          dvd_trans (dvd_pow_self _ hr0) ⟨x.2 + 1, hxm.symm⟩
        exact ⟨hdvd, by
          intro hm
          rw [hm] at hxm
          have : 0 < (x.1 + 1) ^ r * (x.2 + 1) := by positivity
          omega⟩
      · rw [← hxm]
        exact dvd_mul_right _ _
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hdm⟩
      rw [Nat.mem_divisors] at hd
      obtain ⟨⟨k, hdk⟩, hm0⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_ne_zero (by
        intro hzero
        subst d
        exact hm0 (by simpa using hdk))
      have hpowpos : 0 < d ^ r := Nat.pow_pos hdpos
      have hquotpos : 0 < m / d ^ r := Nat.div_pos (by
        have hle : d ^ r ≤ m := Nat.le_of_dvd (by omega) hdm
        omega) hpowpos
      have hdiv : d ^ r * (m / d ^ r) = m := Nat.mul_div_cancel' hdm
      simp only [Finset.mem_filter, hs, Finset.mem_product, Finset.mem_range,
        powerLambertIndex]
      refine ⟨⟨by
        have hr0 : r ≠ 0 := by omega
        have hle : d ≤ m := Nat.le_trans (le_self_pow (by omega) hr0)
          (Nat.le_of_dvd (by omega) hdm)
        omega,
        by
          have hqle : m / d ^ r ≤ m := Nat.div_le_self _ _
          omega⟩, ?_⟩
      rw [Nat.sub_add_cancel hdpos, Nat.sub_add_cancel hquotpos, hdiv]
    · intro x hx
      have hxm : (x.1 + 1) ^ r * (x.2 + 1) = m := (Finset.mem_filter.mp hx).2
      have hquot : m / (x.1 + 1) ^ r = x.2 + 1 := by
        rw [← hxm, Nat.mul_div_cancel_left _ (by positivity)]
      ext <;> omega
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, _⟩
      rw [Nat.mem_divisors] at hd
      have hd0 : d ≠ 0 := by
        intro h; subst d; simp at hd
      omega
  rw [hcard]
  simp only [one_mul, div_eq_mul_inv]

/-- The power-indexed Lambert series equals its arithmetic coefficient series. -/
@[blueprint (title := "Perfect-power Lambert series equal power-divisor coefficient series")]
theorem powerLambert_eq_coefficientValue {b r : ℕ} (hb : 2 ≤ b) (hr : 1 ≤ r) :
    (∑' n : ℕ, 1 / ((b : ℝ) ^ ((n + 1) ^ r) - 1)) =
      coefficientValue (powerDivisorCount r) b := by
  classical
  let F : ℕ × ℕ → ℝ := powerLambertTerm b r
  have hsum : Summable F := summable_powerLambertTerm hb hr
  have h1 :
      (∑' n : ℕ, 1 / ((b : ℝ) ^ ((n + 1) ^ r) - 1)) = ∑' x : ℕ × ℕ, F x := by
    rw [hsum.tsum_prod' (fun n => hsum.prod_factor n)]
    exact (tsum_congr fun n => tsum_powerLambertTerm_snd hb n).symm
  have h2 : ∑' x : ℕ × ℕ, F x =
      ∑' m : ℕ, (powerDivisorCount r m : ℝ) / (b : ℝ) ^ m := by
    have h := (hsum.hasSum.tsum_fiberwise (powerLambertIndex r)).tsum_eq
    rw [← h]
    exact tsum_congr (tsum_powerLambertTerm_fiber hb hr)
  rw [h1, h2]
  rfl

end NormalNumbers.ArithmeticDisjunctivity
