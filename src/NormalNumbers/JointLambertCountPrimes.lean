/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertRescaledPrimes

/-!
# Prime supply at EVERY chosen height

`exists_rescaled_prime_supply` ties the prime-search endpoint to the schedule
`X = 2^(4k¹²)`, which is what made the qualitative proof unconditional but destroys the
counting efficiency: the height is exponential in the killed-window parameter.  The
counting argument of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` §1 and §3 needs the same
conclusion at a *caller-chosen* large height `X`, with the schedule-specific feasibility
test supplied as a hypothesis rather than baked in.

`exists_prime_supply_every_height` is that theorem.  It keeps `AGP`'s quantifier order —
the excised conductor `P` is produced *before* the modulus `B` and the residue `u` — and
carries exactly two schedule-dependent side conditions, both checkable by the caller:

* `(B : ℝ) ^ 3 ≤ X`, which places `B` inside the proved distribution level `⌊X^{1/3}⌋`;
* `C · B · log X · exp(-(η/2)√log X) ≤ 2/5`, the relative error budget.

Neither is an opaque assumption about primes: they are inequalities in `B` and `X` alone,
and §3 of the note discharges them for `B = jointB` at `k = ⌈4 log₂ log X⌉`.
-/

namespace NormalNumbers.JointLambert

open Finset Filter

/-- **Prime supply at every sufficiently large chosen height.**  Read
`exists_pointwise_exponential_distribution` at a caller-chosen `X`, against PNT's
`π(X) ≥ (9/10) X / log X`, to get

  `π(X; B, u) ≥ X / (2 φ(B) log X)`

for every modulus `B ≤ X^{1/3}` coprime to the single excised conductor `P`, every reduced
residue `u`, whenever the error budget holds.  This is §1 of the quantitative note: no AGP
and no uniformity in the base is needed, because the bases are fixed. -/
theorem exists_prime_supply_every_height :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∃ P : ℕ, (P = 1 ∨ P.Prime) ∧
        ∀ B u : ℕ, 1 ≤ B → (B : ℝ) ^ 3 ≤ (X : ℝ) → Nat.Coprime u B → Nat.Coprime B P →
          C * (B : ℝ) * Real.log (X : ℝ)
              * Real.exp (-(η / 2) * Real.sqrt (Real.log (X : ℝ))) ≤ 2 / 5 →
          (X : ℝ) / (2 * (B.totient : ℝ) * Real.log (X : ℝ))
            ≤ (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℝ) := by
  classical
  obtain ⟨η, C, hη, hη4, hC, hdist⟩ := exists_pointwise_exponential_distribution
  obtain ⟨x0, hx0⟩ := eventually_atTop.1
    (hdist.and (Erdos446.eventually_primeCounting_tenth_bounds.and (eventually_ge_atTop 3)))
  refine ⟨η, C, hη, hC, max x0 3, fun X hX => ?_⟩
  have hXx0 : x0 ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨hdistX, hpiX, -⟩ := hx0 X hXx0
  obtain ⟨P, hPcut, hPprime, hPbound⟩ := hdistX
  refine ⟨P, hPprime, fun B u hB1 hBcube hcopuB hcopBP herr => ?_⟩
  -- `B` is inside the distribution level `⌊X^{1/3}⌋`
  have hBlevel : B ≤ Erdos4.FGKMT.powerDistributionLevel X := by
    refine Nat.le_floor ?_
    by_contra hcon
    push_neg at hcon
    have hcube : BoundedGaps.Maynard.vaughanCubeRoot X ^ 3 < (B : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hcon (BoundedGaps.Maynard.vaughanCubeRoot_nonneg X) (by norm_num)
    rw [BoundedGaps.Maynard.vaughanCubeRoot_cube] at hcube
    linarith
  have hkey := hPbound B u hB1 hBlevel hcopBP hcopuB
  set φ : ℝ := (B.totient : ℝ) with hφ
  set Λ : ℝ := Real.log ((X : ℕ) : ℝ) with hΛ
  have hφ0 : 0 < φ := by
    have h : 0 < B.totient := Nat.totient_pos.mpr (by omega)
    rw [hφ]; exact_mod_cast h
  have hXR : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := by omega
    exact_mod_cast this
  have hΛpos : 0 < Λ := by
    rw [hΛ]
    refine Real.log_pos ?_
    have : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
    linarith
  set E : ℝ := C * ((X : ℝ) * Real.exp (-(η / 2) * Real.sqrt Λ)) with hE
  -- the error is small relative to the main term
  have hEsmall : E * (φ * Λ) ≤ (2 / 5) * (X : ℝ) := by
    have hφB : φ ≤ (B : ℝ) := by rw [hφ]; exact_mod_cast Nat.totient_le B
    set w : ℝ := Real.exp (-(η / 2) * Real.sqrt Λ) with hw
    have hwpos : (0 : ℝ) < w := Real.exp_pos _
    have hprod : C * φ * Λ * w ≤ C * (B : ℝ) * Λ * w := by
      have : C * φ * Λ ≤ C * (B : ℝ) * Λ := by
        have := mul_le_mul_of_nonneg_left hφB hC.le
        nlinarith [hΛpos.le]
      exact mul_le_mul_of_nonneg_right this hwpos.le
    calc E * (φ * Λ) = (X : ℝ) * (C * φ * Λ * w) := by rw [hE, hw]; ring
      _ ≤ (X : ℝ) * (C * (B : ℝ) * Λ * w) := mul_le_mul_of_nonneg_left hprod hXR.le
      _ ≤ (X : ℝ) * (2 / 5) := mul_le_mul_of_nonneg_left (by rw [hw] at herr ⊢; exact herr) hXR.le
      _ = 2 / 5 * (X : ℝ) := by ring
  -- the main term
  have hbridge : (BoundedGaps.Maynard.primeCountTotal X : ℝ) = (X.primeCounting : ℝ) := rfl
  have hπ : (9 / 10 : ℝ) * ((X : ℝ) / Λ) ≤ (BoundedGaps.Maynard.primeCountTotal X : ℝ) := by
    rw [hbridge]; exact hpiX.1
  have hlow : (BoundedGaps.Maynard.primeCountTotal X : ℝ) / φ - E
      ≤ (BoundedGaps.Maynard.primeCountUpTo X B (u % B) : ℝ) := by
    have habs := abs_le.1 hkey
    linarith [habs.1]
  rw [← agpCount_eq_primeCountUpTo] at hlow
  set N : ℝ := ((((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℕ) : ℝ)
    with hN
  rw [div_le_iff₀ (by positivity)]
  have m1 : (BoundedGaps.Maynard.primeCountTotal X : ℝ) * Λ - E * (φ * Λ) ≤ N * (φ * Λ) := by
    have h := mul_le_mul_of_nonneg_right hlow (show (0 : ℝ) ≤ φ * Λ by positivity)
    calc (BoundedGaps.Maynard.primeCountTotal X : ℝ) * Λ - E * (φ * Λ)
        = ((BoundedGaps.Maynard.primeCountTotal X : ℝ) / φ - E) * (φ * Λ) := by field_simp
      _ ≤ N * (φ * Λ) := h
  have m2 : (9 / 10 : ℝ) * (X : ℝ) ≤ (BoundedGaps.Maynard.primeCountTotal X : ℝ) * Λ := by
    have h := mul_le_mul_of_nonneg_right hπ hΛpos.le
    calc (9 / 10 : ℝ) * (X : ℝ) = (9 / 10 * ((X : ℝ) / Λ)) * Λ := by field_simp
      _ ≤ _ := h
  have hexpand : N * (2 * φ * Λ) = 2 * (N * (φ * Λ)) := by ring
  linarith

end NormalNumbers.JointLambert
