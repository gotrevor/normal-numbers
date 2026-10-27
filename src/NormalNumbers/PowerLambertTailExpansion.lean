/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertDisjunctivity
import NormalNumbers.PowerLambertTailDefs

/-!
# Removing a finite head from a power Lambert series

The terms corresponding to roots `1, …, D` are rational.  Regrouping the
remaining double Lambert series by its exponent gives the tail power-divisor
coefficients.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

/-- Index the shifted-root Lambert double series by its exponent. -/
def tailPowerLambertIndex (r D : ℕ) (x : ℕ × ℕ) : ℕ :=
  (x.1 + D + 1) ^ r * (x.2 + 1)

/-- The Lambert term with its root shifted beyond the cutoff. -/
noncomputable def powerLambertTailTerm (b r D : ℕ) (x : ℕ × ℕ) : ℝ :=
  powerLambertTerm b r (x.1 + D, x.2)

/-- A fiber of the shifted-root index is counted by divisors above the cutoff. -/
lemma tsum_powerLambertTailTerm_fiber {b r D : ℕ} (_hb : 2 ≤ b) (hr : 1 ≤ r)
    (m : ℕ) :
    ∑' x : (tailPowerLambertIndex r D ⁻¹' {m} : Set (ℕ × ℕ)),
        powerLambertTailTerm b r D x.1 =
      (tailPowerDivisorCount r D m : ℝ) / (b : ℝ) ^ m := by
  classical
  rw [_root_.tsum_subtype]
  set s : Finset (ℕ × ℕ) := Finset.range (m + 1) ×ˢ Finset.range (m + 1) with hs
  have hsupp : ∀ x ∉ s,
      (tailPowerLambertIndex r D ⁻¹' {m}).indicator
        (powerLambertTailTerm b r D) x = 0 := by
    intro x hx
    rw [Set.indicator_apply_eq_zero]
    intro hxm
    simp only [Set.mem_preimage, Set.mem_singleton_iff, tailPowerLambertIndex] at hxm
    exact absurd (by
      rw [hs, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      constructor
      · have hbase : x.1 + D + 1 ≤ (x.1 + D + 1) ^ r :=
          le_self_pow (by omega) (by omega)
        have hmul : (x.1 + D + 1) ^ r ≤ (x.1 + D + 1) ^ r * (x.2 + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        omega
      · have hpow : 1 ≤ (x.1 + D + 1) ^ r := Nat.one_le_pow _ _ (by omega)
        have hmul : x.2 + 1 ≤ (x.1 + D + 1) ^ r * (x.2 + 1) :=
          Nat.le_mul_of_pos_left _ hpow
        omega) hx
  rw [tsum_eq_sum hsupp]
  have hfilter : ∀ x ∈ s,
      (tailPowerLambertIndex r D ⁻¹' {m}).indicator
        (powerLambertTailTerm b r D) x =
        if tailPowerLambertIndex r D x = m then 1 / (b : ℝ) ^ m else 0 := by
    intro x _
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hxm : tailPowerLambertIndex r D x = m
    · rw [if_pos hxm, if_pos hxm]
      unfold powerLambertTailTerm powerLambertTerm tailPowerLambertIndex at *
      rw [hxm]
    · rw [if_neg hxm, if_neg hxm]
  rw [Finset.sum_congr rfl hfilter, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_one_div]
  have hcard : (s.filter (fun x => tailPowerLambertIndex r D x = m)).card =
      tailPowerDivisorCount r D m := by
    unfold tailPowerDivisorCount
    refine Finset.card_bij' (fun x _ => x.1 + D + 1)
      (fun d _ => (d - (D + 1), m / d ^ r - 1)) ?_ ?_ ?_ ?_
    · intro x hx
      have hxm : (x.1 + D + 1) ^ r * (x.2 + 1) = m :=
        (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter]
      constructor
      · rw [Nat.mem_divisors]
        have hr0 : r ≠ 0 := by omega
        have hdvd : x.1 + D + 1 ∣ m :=
          dvd_trans (dvd_pow_self _ hr0) ⟨x.2 + 1, hxm.symm⟩
        exact ⟨hdvd, by
          intro hm
          rw [hm] at hxm
          have : 0 < (x.1 + D + 1) ^ r * (x.2 + 1) := by positivity
          omega⟩
      · constructor
        · omega
        · rw [← hxm]
          exact dvd_mul_right _ _
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hdcond⟩
      rw [Nat.mem_divisors] at hd
      obtain ⟨⟨k, hdk⟩, hm0⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_ne_zero (by
        intro hzero
        subst d
        exact hm0 (by simpa using hdk))
      have hpowpos : 0 < d ^ r := Nat.pow_pos hdpos
      have hquotpos : 0 < m / d ^ r := Nat.div_pos (by
        have hle : d ^ r ≤ m := Nat.le_of_dvd (by omega) hdcond.2
        omega) hpowpos
      have hdiv : d ^ r * (m / d ^ r) = m := Nat.mul_div_cancel' hdcond.2
      have hDle : D + 1 ≤ d := by omega
      simp only [Finset.mem_filter, hs, Finset.mem_product, Finset.mem_range,
        tailPowerLambertIndex]
      refine ⟨⟨by
        have hle : d ≤ m := Nat.le_trans (le_self_pow (by omega) (by omega))
          (Nat.le_of_dvd (by omega) hdcond.2)
        omega,
        by
          have hqle : m / d ^ r ≤ m := Nat.div_le_self _ _
          omega⟩, ?_⟩
      have hroot : d - (D + 1) + D + 1 = d := by omega
      rw [hroot, Nat.sub_add_cancel hquotpos, hdiv]
    · intro x hx
      have hxm : (x.1 + D + 1) ^ r * (x.2 + 1) = m :=
        (Finset.mem_filter.mp hx).2
      have hquot : m / (x.1 + D + 1) ^ r = x.2 + 1 := by
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

/-- The first eight power-Lambert terms form a rational head; the remaining
series is the Lambert coefficient value of the tail power-divisor counts. -/
@[blueprint (title := "A power Lambert constant differs rationally from its divisor tail value")]
theorem exists_rat_powerLambert_tail (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    ∃ q : ℚ, powerLambert b r = (q : ℝ) +
      coefficientValue (tailPowerDivisorCount r 8) b := by
  classical
  let F : ℕ × ℕ → ℝ := powerLambertTerm b r
  have hsum : Summable F := summable_powerLambertTerm hb (by omega)
  let row : ℕ → ℝ := fun n => ∑' k : ℕ, F (n, k)
  have hrowEq (n : ℕ) : row n =
      1 / ((b : ℝ) ^ ((n + 1) ^ r) - 1) := by
    simp only [row, F]
    exact tsum_powerLambertTerm_snd hb n
  have hgeo : Summable (fun n : ℕ => (1 / (b : ℝ)) ^ (n + 1)) := by
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have h := summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / (b : ℝ))
      (by rw [div_lt_one hbpos]; exact_mod_cast (by omega : 1 < b))
    exact h.comp_injective (fun n m hnm => by omega)
  have hrowsum : Summable row := by
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k =>
      powerLambertTerm_nonneg b r (n, k)) (fun n => ?_) (Summable.mul_left 2 hgeo)
    change row n ≤ 2 * (1 / (b : ℝ)) ^ (n + 1)
    rw [hrowEq n]
    have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have hExp : n + 1 ≤ (n + 1) ^ r := le_self_pow (by omega) (by omega)
    have hPow : (b : ℝ) ^ (n + 1) ≤ (b : ℝ) ^ ((n + 1) ^ r) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) hExp
    have hBase : (2 : ℝ) ≤ (b : ℝ) ^ (n + 1) := by
      calc (2 : ℝ) ≤ b := hbR
        _ ≤ (b : ℝ) ^ (n + 1) := le_self_pow₀ (by linarith) (by omega)
    have hDen : (b : ℝ) ^ (n + 1) ≤
        2 * ((b : ℝ) ^ ((n + 1) ^ r) - 1) := by nlinarith
    have hDen0 : (0 : ℝ) < (b : ℝ) ^ ((n + 1) ^ r) - 1 := by linarith
    rw [one_div_pow, div_le_iff₀ hDen0]
    field_simp
    nlinarith
  have hwhole : powerLambert b r = ∑' n : ℕ, row n := by
    unfold powerLambert
    exact tsum_congr fun n => (hrowEq n).symm
  have hsplit := Summable.sum_add_tsum_nat_add 8 hrowsum
  let G : ℕ × ℕ → ℝ := fun x => F (x.1 + 8, x.2)
  have hGsum : Summable G := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hsum
    · exact powerLambertTerm_nonneg b r (x.1 + 8, x.2)
    · have hbase : x.1 + 1 ≤ x.1 + 8 + 1 := by omega
      have hpow := Nat.pow_le_pow_left hbase r
      have hexp := Nat.mul_le_mul_right (x.2 + 1) hpow
      have hden : (b : ℝ) ^ ((x.1 + 1) ^ r * (x.2 + 1)) ≤
          (b : ℝ) ^ ((x.1 + 8 + 1) ^ r * (x.2 + 1)) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) hexp
      unfold G F powerLambertTerm
      exact one_div_le_one_div_of_le (by positivity) hden
  have htailRows : ∑' n : ℕ, row (n + 8) =
      coefficientValue (tailPowerDivisorCount r 8) b := by
    have hfiber := (hGsum.hasSum.tsum_fiberwise (tailPowerLambertIndex r 8)).tsum_eq
    calc
      ∑' n : ℕ, row (n + 8) = ∑' x : ℕ × ℕ, G x := by
        rw [hGsum.tsum_prod]
      _ = ∑' m : ℕ,
            ∑' x : (tailPowerLambertIndex r 8 ⁻¹' {m} : Set (ℕ × ℕ)), G x :=
          hfiber.symm
      _ = ∑' m : ℕ, (tailPowerDivisorCount r 8 m : ℝ) / (b : ℝ) ^ m :=
          tsum_congr fun m => by
            simpa [G, F, powerLambertTailTerm] using
              tsum_powerLambertTailTerm_fiber hb (by omega) m
      _ = coefficientValue (tailPowerDivisorCount r 8) b := rfl
  let q : ℚ := ∑ n ∈ Finset.range 8,
      (1 : ℚ) / ((b : ℚ) ^ ((n + 1) ^ r) - 1)
  have hhead : (∑ n ∈ Finset.range 8, row n) = (q : ℝ) := by
    calc
      (∑ n ∈ Finset.range 8, row n) =
          ∑ n ∈ Finset.range 8, 1 / ((b : ℝ) ^ ((n + 1) ^ r) - 1) :=
        Finset.sum_congr rfl (fun n _ => hrowEq n)
      _ = (q : ℝ) := by
        dsimp [q]
        push_cast
        rfl
  refine ⟨q, ?_⟩
  rw [hwhole, ← hsplit, hhead, htailRows]

end NormalNumbers.ArithmeticDisjunctivity
