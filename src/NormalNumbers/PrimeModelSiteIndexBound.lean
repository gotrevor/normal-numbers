import NormalNumbers.PrimeModelPhaseAlgebra

/-!
# The contracting site index is bounded by `log₄|h|`

`PrimeModelPhaseAlgebra.exists_site_re_nonpos` produces *some* site `j₀ : Fin k` with
`Re (zPhase h k j₀) ≤ 0`, and Theorem A's leg E5 collects its phase contraction from the
`S`-primes below `y_{j₀}`.  The `∃` hides a fact that is **route-decisive** for the schedule:
the site it returns is `Nat.find hex - 1`, where `hex` is the `NontrivialWindow` witness set,
and `Nat.find hex ≤ log₄|h| + 1` because `|h| / 4^j ∈ (0,1)` — hence not an integer — as soon
as `4^j > |h|`.

So for a **fixed** `h` the contracting site is a **bounded** index, uniformly in `N`.  On a
schedule `y_j = N^{a_N 2^{-j}}` this means `y_{j₀} ≥ y_{c(h)} = N^{a_N 2^{-c(h)}}` is a
*near-top* cutoff: the root chain from `y_{j₀}` up to `N` has length
`c(h) + log₂(1/a_N) = c(h) + 2 log₂ u_N`, which is `O(log u_N)` — **not** the `≍ L₃N` halvings
that the bottom cutoff `yBot N` costs.  That is exactly what makes Astra §8 (8.6) legitimate:
the mass above the contracting cutoff is `o(1)`, so `J_N` may be tied to the **full** mass
`S_P(N)` rather than to the mass below the bottom cutoff.

This file proves the bound; wiring it through Theorem A's `∃ j₀` is the next step.
-/

open Finset

namespace NormalNumbers.PrimeModel.PhaseAlgebra

open NormalNumbers.G4 NormalNumbers.G4Sparse

/-- If `4^j > |h|` and `h ≠ 0` then `h / 4^j` is not an integer. -/
theorem not_int_div_pow_of_lt {h : ℤ} (hh : h ≠ 0) {j : ℕ} (hlt : |(h : ℝ)| < (4 : ℝ) ^ j) :
    ¬ (∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j = m) := by
  rintro ⟨m, hm⟩
  have hpow : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
  have hmabs : |(m : ℝ)| < 1 := by
    rw [← hm, abs_div, abs_of_pos hpow, div_lt_one hpow]
    exact hlt
  have hm0 : m = 0 := by
    by_contra hc
    have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega : m ≠ 0)
    linarith
  subst hm0
  have hz : (h : ℝ) = 0 := by
    have := hm
    field_simp at this
    exact_mod_cast this
  exact hh (by exact_mod_cast hz)

/-- **The site bound.**  The site produced by `exists_site_re_nonpos` has index at most
`Nat.log 4 |h|`: for a fixed window shift `h` it does not move with `N`. -/
theorem exists_site_re_nonpos_le (k : ℕ) (h : ℤ) (hntw : NontrivialWindow k h) :
    ∃ j : Fin k, (j : ℕ) ≤ Nat.log 4 h.natAbs ∧ (zPhase h k j).re ≤ 0 := by
  classical
  have hex : ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ ¬ (∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ j = m) := hntw
  -- `h ≠ 0`, since `0 / 4^j = 0` is an integer
  have hh : h ≠ 0 := by
    rintro rfl
    obtain ⟨j, -, -, hj⟩ := hex
    exact hj ⟨0, by simp⟩
  obtain ⟨hj1, hjk, hjP⟩ := Nat.find_spec hex
  set j₀ := Nat.find hex with hj₀
  -- `j₀ ≤ log₄|h| + 1`
  have hstar : j₀ ≤ Nat.log 4 h.natAbs + 1 := by
    set J : ℕ := Nat.log 4 h.natAbs + 1 with hJ
    rcases le_total J k with hJk | hJk
    · refine Nat.find_le ⟨by omega, hJk, ?_⟩
      refine not_int_div_pow_of_lt hh ?_
      have hltN : h.natAbs < 4 ^ J := Nat.lt_pow_succ_log_self (by norm_num) _
      have hltZ : |h| < (4 : ℤ) ^ J := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hltN
      rw [← Int.cast_abs]
      exact_mod_cast hltZ
    · omega
  -- the construction of `exists_site_re_nonpos`, with the index recorded
  have hphase_re : ∀ x : ℝ, (ePhase x).re = Real.cos (2 * Real.pi * x) := by
    intro x
    have hx : ePhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      unfold ePhase; congr 1; push_cast; ring
    rw [hx, Complex.exp_ofReal_mul_I_re]
  have hpred : ∃ m : ℤ, (h : ℝ) / (4 : ℝ) ^ (j₀ - 1) = m := by
    rcases eq_or_lt_of_le hj1 with heq | hlt
    · have h0 : j₀ - 1 = 0 := by omega
      rw [h0]
      exact ⟨h, by norm_num⟩
    · have hlt' : j₀ - 1 < j₀ := by omega
      have hmin := Nat.find_min hex hlt'
      push Not at hmin
      exact hmin (by omega) (by omega)
  obtain ⟨m, hm⟩ := hpred
  have hsucc : j₀ - 1 + 1 = j₀ := by omega
  have h4 : (h : ℝ) / (4 : ℝ) ^ j₀ = (m : ℝ) / 4 := by
    rw [← hsucc, pow_succ, ← div_div, hm]
  have hm4 : ¬ ((4 : ℤ) ∣ m) := by
    rintro ⟨q, rfl⟩
    refine hjP ⟨q, ?_⟩
    rw [h4]
    push_cast
    ring_nf
  have hmm : (m : ℝ) = ((m % 4 : ℤ) : ℝ) + 4 * ((m / 4 : ℤ) : ℝ) := by
    have hz : m = m % 4 + 4 * (m / 4) := by omega
    exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) hz
  have hr : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
    have h0 : m % 4 ≠ 0 := fun hc => hm4 (Int.dvd_of_emod_eq_zero hc)
    have h1 : 0 ≤ m % 4 := Int.emod_nonneg m (by norm_num)
    have h2 : m % 4 < 4 := Int.emod_lt_of_pos m (by norm_num)
    omega
  refine ⟨⟨j₀ - 1, by omega⟩, by simpa using by omega, ?_⟩
  have hz : zPhase h k ⟨j₀ - 1, by omega⟩ = ePhase (((m % 4 : ℤ) : ℝ) / 4) := by
    rw [zPhase]
    simp only [hsucc]
    rw [h4]
    have hsplit : (m : ℝ) / 4 = ((m % 4 : ℤ) : ℝ) / 4 + ((m / 4 : ℤ) : ℤ) := by
      rw [hmm]; ring
    rw [hsplit, ePhase_add_int]
  rw [hz, hphase_re]
  rcases hr with hr1 | hr2 | hr3
  · rw [hr1, show (2 * Real.pi * (((1 : ℤ) : ℝ) / 4)) = Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
  · rw [hr2, show (2 * Real.pi * (((2 : ℤ) : ℝ) / 4)) = Real.pi by push_cast; ring, Real.cos_pi]
    norm_num
  · rw [hr3, show (2 * Real.pi * (((3 : ℤ) : ℝ) / 4)) = Real.pi + Real.pi / 2 by push_cast; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi, Real.cos_pi]
    norm_num

end NormalNumbers.PrimeModel.PhaseAlgebra
