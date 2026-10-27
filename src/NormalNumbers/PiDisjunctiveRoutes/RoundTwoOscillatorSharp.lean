/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.RoundTwoOscillator

/-!
# Oscillator pilot: degree five is sharp for the word `[1]`

The quintic `quinticControl` has residual `x*(x-2)^4 + 1/4 > 0` on `[0,4]` and
rejects both `x = 3` and `x = 4`.  In `[3,4]` the only `[1]`-avoiders (for the
canonical binary expansion `digitOf`) are `3` and `4`, so this quintic is a
word-`[1]` certificate; the quartic quadrature obstruction shows no certificate
has degree `≤ 4`.  This is a calibration of the certificate family, not a digit
fact about pi.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots

open Polynomial

lemma realPoly_quinticControl : realPoly quinticControl =
    X ^ 5 - 8 * X ^ 4 + 4 * X ^ 3 + 64 * X ^ 2 - 8 * X - C (511 / 4 : ℝ) := by
  simp [realPoly, quinticControl, Polynomial.map_sub, Polynomial.map_add]

theorem quinticEndpointControl : QuinticEndpointControl := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [realPoly_quinticControl]
    simp [derivative_mul]
    have h : 0 ≤ t * (t - 2) ^ 4 := mul_nonneg ht.1 (by positivity)
    nlinarith [h]
  · rw [realPoly_quinticControl]; simp; norm_num
  · rw [realPoly_quinticControl]; simp; norm_num

/-- If every binary digit of `y ∈ [0,1)` is `0`, then `y = 0`. -/
lemma eq_zero_of_digitOf_two_eq_zero {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1)
    (hd : ∀ i, digitOf 2 y i = 0) : y = 0 := by
  have key : ∀ i : ℕ, y * 2 ^ i < 1 := by
    intro i
    induction i with
    | zero => simpa using h1
    | succ i ih =>
      have hpos : 0 ≤ y * 2 ^ (i + 1) := by positivity
      have hlt : y * 2 ^ (i + 1) < 2 := by rw [pow_succ]; nlinarith
      have hfl0 : 0 ≤ ⌊y * 2 ^ (i + 1)⌋ := Int.floor_nonneg.mpr hpos
      have hfl2 : ⌊y * 2 ^ (i + 1)⌋ < 2 := Int.floor_lt.mpr (by exact_mod_cast hlt)
      have hdi := hd i
      simp only [digitOf, Nat.cast_ofNat] at hdi
      have hfl : ⌊y * 2 ^ (i + 1)⌋ = 0 := by
        rcases (by omega : ⌊y * 2 ^ (i + 1)⌋ = 0 ∨ ⌊y * 2 ^ (i + 1)⌋ = 1) with h | h
        · exact h
        · rw [h] at hdi; simp at hdi
      have := Int.floor_eq_zero_iff.mp hfl
      exact this.2
  by_contra hne
  have hy : 0 < y := lt_of_le_of_ne h0 (Ne.symm hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / y) (by norm_num : (1 : ℝ) < 2)
  have := key n
  rw [div_lt_iff₀ hy] at hn
  linarith

theorem wordOneAvoidanceClassification : WordOneAvoidanceClassification := by
  intro x hx
  constructor
  · intro hav
    have hd : ∀ i, digitOf 2 (Int.fract x) i = 0 := by
      intro i
      have hlt : digitOf 2 (Int.fract x) i < 2 := by
        unfold digitOf; exact Nat.mod_lt _ (by norm_num)
      by_contra hne
      apply hav i
      intro j hj
      simp at hj
      subst hj
      simp
      omega
    have hf := eq_zero_of_digitOf_two_eq_zero (Int.fract_nonneg x) (Int.fract_lt_one x) hd
    rw [Int.fract_eq_iff] at hf
    obtain ⟨-, -, z, hz⟩ := hf
    have hz' : x = z := by linarith
    have h3 : (3 : ℝ) ≤ z := hz' ▸ hx.1
    have h4 : (z : ℝ) ≤ 4 := hz' ▸ hx.2
    have h3' : 3 ≤ z := by exact_mod_cast h3
    have h4' : z ≤ 4 := by exact_mod_cast h4
    rcases (by omega : z = 3 ∨ z = 4) with h | h
    · left; rw [hz', h]; norm_num
    · right; rw [hz', h]; norm_num
  · rintro (rfl | rfl) n hocc
    · have := hocc 0 (by simp)
      norm_num [digitOf] at this
    · have := hocc 0 (by simp)
      norm_num [digitOf] at this

theorem quinticWordOneCertificate : QuinticWordOneCertificate := by
  obtain ⟨hpos, h3, h4⟩ := quinticEndpointControl
  refine ⟨hpos, ?_⟩
  intro x hx hav
  rcases (wordOneAvoidanceClassification x hx).mp hav with rfl | rfl
  · exact h3.le
  · exact h4.le

lemma natDegree_quinticControl : quinticControl.natDegree = 5 := by
  unfold quinticControl
  compute_degree!

/-- A word-`[1]` certificate must have degree at least five. -/
theorem five_le_natDegree_of_wordOne {P : Polynomial ℚ}
    (hP : WordOscillatorCertificate [1] P) : 5 ≤ P.natDegree := by
  by_contra h
  push Not at h
  obtain ⟨hpos, hcert⟩ := hP
  have h3 := hcert 3 ⟨le_rfl, by norm_num⟩
    ((wordOneAvoidanceClassification 3 ⟨le_rfl, by norm_num⟩).mpr (Or.inl rfl))
  have h4 := hcert 4 ⟨by norm_num, le_rfl⟩
    ((wordOneAvoidanceClassification 4 ⟨by norm_num, le_rfl⟩).mpr (Or.inr rfl))
  exact not_quartic_endpoint_certificate ⟨P, by omega, hpos, h3, h4⟩

@[blueprint (title := "Degree five is the sharp oscillator threshold for word one (proved)")]
theorem minimumDegreeWordOne : MinimumDegreeWordOne :=
  ⟨⟨quinticControl, natDegree_quinticControl, quinticWordOneCertificate⟩,
    fun _ hP => five_le_natDegree_of_wordOne hP⟩

end NormalNumbers.PiDisjunctiveRoutes.RoundTwo.Pilots
