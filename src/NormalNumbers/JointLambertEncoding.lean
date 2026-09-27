import Mathlib

/-!
# Separation of the finite characters used for simultaneous Lambert words

The new arithmetic target and paper proof are in
`papers/2026-09-26-joint-lambert-disjunctivity.md`.
This module proves the encoding mechanism, not the Lambert headline.
Distinct bases suffice; multiplicative independence is not required.
-/

open Filter
open scoped Topology BigOperators

namespace NormalNumbers.JointLambertEncoding

/-- After normalizing by the smallest denominator, its coefficient survives. -/
theorem normalized_character_tendsto (S : Finset ℕ) (h : ℕ → ℝ) (b₀ : ℕ)
    (hmem : b₀ ∈ S) (hpos : 0 < b₀) (hmin : ∀ b ∈ S, b₀ ≤ b) :
    Tendsto (fun r : ℕ => ∑ b ∈ S, h b * ((b₀ : ℝ) / b) ^ r)
      atTop (𝓝 (h b₀)) := by
  have hlim : ∀ b ∈ S, Tendsto (fun r : ℕ => h b * ((b₀ : ℝ) / b) ^ r)
      atTop (𝓝 (if b = b₀ then h b₀ else 0)) := by
    intro b hb
    by_cases he : b = b₀
    · subst b
      simpa [ne_of_gt hpos] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => h b₀) atTop (𝓝 (h b₀)))
    · have hlt : b₀ < b := lt_of_le_of_ne (hmin b hb) (Ne.symm he)
      have hbp : (0 : ℝ) < b := by exact_mod_cast (lt_trans hpos hlt)
      have hratio : (b₀ : ℝ) / b < 1 := (div_lt_one hbp).2 (by exact_mod_cast hlt)
      simpa [he] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (b₀ : ℝ) / b)
          hratio).const_mul (h b)
  simpa [hmem] using tendsto_finset_sum S hlim

/-- A nonzero coefficient at the smallest base prevents persistent cancellation. -/
theorem character_eventually_ne_zero (S : Finset ℕ) (h : ℕ → ℝ) (b₀ : ℕ)
    (hmem : b₀ ∈ S) (hpos : 0 < b₀) (hmin : ∀ b ∈ S, b₀ ≤ b)
    (hne : h b₀ ≠ 0) :
    ∀ᶠ r : ℕ in atTop, (∑ b ∈ S, h b / (b : ℝ) ^ r) ≠ 0 := by
  have ht := normalized_character_tendsto S h b₀ hmem hpos hmin
  filter_upwards [ht.eventually_ne hne] with r hr
  intro hz
  apply hr
  calc
    (∑ b ∈ S, h b * ((b₀ : ℝ) / b) ^ r)
        = (b₀ : ℝ) ^ r * (∑ b ∈ S, h b / (b : ℝ) ^ r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          rw [div_pow]
          ring
    _ = 0 := by rw [hz, mul_zero]

/-- Unnormalized characters tend to zero in every base at least two. -/
theorem character_tendsto_zero (S : Finset ℕ) (h : ℕ → ℝ)
    (hb : ∀ b ∈ S, 2 ≤ b) :
    Tendsto (fun r : ℕ => ∑ b ∈ S, h b / (b : ℝ) ^ r) atTop (𝓝 0) := by
  have hlim : ∀ b ∈ S, Tendsto (fun r : ℕ => h b / (b : ℝ) ^ r) atTop (𝓝 0) := by
    intro b hmem
    have hbp : (1 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) (hb b hmem))
    have hr := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0 : ℝ) ≤ 1 / b) ((div_lt_one (by linarith)).2 hbp)
    simpa [div_pow, div_eq_mul_inv] using hr.const_mul (h b)
  simpa using tendsto_finset_sum S hlim

/-- In particular the even divisor-count lattice has no fixed nonzero character
resonance at all sufficiently deep positions.  The smallest supported base is
supplied explicitly; zero coefficients can be removed before applying this lemma. -/
theorem even_character_eventually_nonintegral (S : Finset ℕ) (h : ℕ → ℝ) (b₀ : ℕ)
    (hmem : b₀ ∈ S) (hb : ∀ b ∈ S, 2 ≤ b) (hmin : ∀ b ∈ S, b₀ ≤ b)
    (hne : h b₀ ≠ 0) :
    ∀ᶠ r : ℕ in atTop, ∀ z : ℤ, 2 * (∑ b ∈ S, h b / (b : ℝ) ^ r) ≠ z := by
  have hzero := character_eventually_ne_zero S h b₀ hmem (by have := hb b₀ hmem; omega) hmin hne
  have ht := (character_tendsto_zero S h hb).const_mul 2
  have hsmall : ∀ᶠ r : ℕ in atTop, |2 * (∑ b ∈ S, h b / (b : ℝ) ^ r)| < 1 := by
    have ht' : Tendsto (fun r : ℕ => |2 * (∑ b ∈ S, h b / (b : ℝ) ^ r)|)
        atTop (𝓝 (0 : ℝ)) := by simpa using ht.abs
    exact ht'.eventually_lt_const (by norm_num)
  filter_upwards [hzero, hsmall] with r hr hs
  intro z hz
  have hzsmall : |(z : ℝ)| < 1 := by rwa [hz] at hs
  have hz0 : z = 0 := by
    have hlo : (-1 : ℝ) < z := (abs_lt.mp hzsmall).1
    have hhi : (z : ℝ) < 1 := (abs_lt.mp hzsmall).2
    have hlo' : (-1 : ℤ) < z := by exact_mod_cast hlo
    have hhi' : z < (1 : ℤ) := by exact_mod_cast hhi
    omega
  rw [hz0, Int.cast_zero] at hz
  exact hr (by linarith)

/-- Hand-computed encoding witness: binary word 0 and quaternary word 3
at the same position, using divisor count 58 and survivor offset 2. -/
theorem dependent_base_anchor :
    (58 : ℕ) % 2 ^ 3 = 2 ∧ (58 : ℕ) % 4 ^ 3 = 58 := by decide

end NormalNumbers.JointLambertEncoding
