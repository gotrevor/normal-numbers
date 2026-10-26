/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.PrimeReservoirStep

/-!
# Route 2: the reservoir is a ×16 orbit of a partial BBP-type sum

Combining `bbpPrimeReservoir_succ` with `bbpReservoirExit_mod_one`, the reservoir is,
modulo 1, exactly `16ⁿ · ρₙ` where `ρₙ` is a partial sum of a prime-indexed series with
`O(1/k)` numerators.  So the reservoir carries no arithmetic beyond the digits of the
limit constant `ρ`.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

/-- Kick of the reservoir at step `k`, after the exit collapse. -/
noncomputable def reservoirKick (k : ℕ) : ℝ :=
  -(if Nat.Prime (4 * k + 1) then 64 / (4 * (k : ℝ) + 1) else 0) + bbpReservoirEntry k

/-- Partial sums of the reservoir constant `ρ = Σ kick_k / 16^{k+1}`. -/
noncomputable def reservoirConstPartial (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, reservoirKick k / 16 ^ (k + 1)

/-- Exact: `Rₙ ≡ 16ⁿ ρₙ (mod 1)`. -/
theorem bbpPrimeReservoir_eq_orbit (n : ℕ) :
    ∃ z : ℤ, bbpPrimeReservoir n = z + 16 ^ n * reservoirConstPartial n := by
  induction n with
  | zero => exact ⟨0, by simp [bbpPrimeReservoir, reservoirConstPartial]⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := bbpReservoirExit_mod_one n
    refine ⟨16 * z - w, ?_⟩
    rw [bbpPrimeReservoir_succ, hz, hw, reservoirConstPartial, reservoirConstPartial,
      Finset.sum_range_succ, reservoirKick]
    have h : (16 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end NormalNumbers.PiDisjunctiveRoutes
