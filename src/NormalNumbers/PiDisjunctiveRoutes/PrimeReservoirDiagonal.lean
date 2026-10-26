/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.PrimeReservoir

/-!
# Route 2: diagonal support node

The transfer `pi_disjunctive_of_primeReservoirSupport` only ever uses squares
centred on the diagonal `x = y`.  This file freezes that weaker node and both edges.
-/

namespace NormalNumbers.PiDisjunctiveRoutes

open Set

/-- Node: reservoir and residual are simultaneously near any common value `t < 1/2`,
arbitrarily late.  Confidence in truth: 70% (same evidence as the premise).
Costume audit: (a) neither the sink nor normality of π is known to imply it, since the
split R + S is not a function of π's digits; (b) it implies the sink
(`pi_disjunctive_of_reservoirDiagonalSupport`) and is implied by the premise
(`reservoirDiagonalSupport_of_support`); the converse to the premise is not known
(off-diagonal rectangles are not reached).  Corner `t = 0`: a square at the origin,
nonvacuous.  Probe `scripts/pi_route2_joint.py` (N = 1500): every 8×8 cell hit, but a
composite-denominator control is equally uniform, so the numerics do not single out
the prime mechanism. -/
def PiReservoirDiagonalSupport : Prop :=
  ∀ t ε : ℝ, 0 ≤ t → t < 1 / 2 → 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    Int.fract (bbpPrimeReservoir n) ∈ Ioo (t - ε) (t + ε) ∧
    Int.fract (bbpResidual n) ∈ Ioo (t - ε) (t + ε)

theorem reservoirDiagonalSupport_of_support (h : PiPrimeReservoirSupport) :
    PiReservoirDiagonalSupport := by
  intro t ε ht ht2 hε N
  obtain ⟨n, hn, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ :=
    h (max 0 (t - ε)) (min 1 (t + ε)) (max 0 (t - ε)) (min 1 (t + ε))
      (le_max_left _ _) (by apply max_lt <;> apply lt_min <;> linarith) (min_le_left _ _)
      (le_max_left _ _) (by apply max_lt <;> apply lt_min <;> linarith) (min_le_left _ _) N
  exact ⟨n, hn, ⟨lt_of_le_of_lt (le_max_right _ _) h1, lt_of_lt_of_le h2 (min_le_right _ _)⟩,
    ⟨lt_of_le_of_lt (le_max_right _ _) h3, lt_of_lt_of_le h4 (min_le_right _ _)⟩⟩

theorem pi_disjunctive_of_reservoirDiagonalSupport (hπ : PiBBP)
    (h : PiReservoirDiagonalSupport) : IsDisjunctive 16 Real.pi := by
  intro a c ha hac hc
  set e := (c - a) / 8 with he
  have he0 : 0 < e := by rw [he]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (32 / (3 * e))
  obtain ⟨n, hNn, ⟨hP1, hP2⟩, ⟨hR1, hR2⟩⟩ :=
    h (a / 2 + 3 * e / 2) (e / 2) (by linarith) (by rw [he]; linarith) (by linarith) N
  have hT0 := piTail_ge hπ n
  have hT1 := piTail_le hπ n
  have hn : (32 / (3 * e) : ℝ) < n := lt_of_lt_of_le hN (by exact_mod_cast hNn)
  have hsmall : 64 / (3 * (8 * (n : ℝ) + 1) ^ 2) < 2 * e := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 32 / (3 * e) * (3 * e) = 32 := by field_simp
    have h2 : (n : ℝ) * (3 * e) > 32 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hpos : (0 : ℝ) < 3 / (16 * ((n : ℝ) + 1) ^ 2) := by positivity
  refine ⟨n, ?_⟩
  have hsplit : Real.pi * (16 : ℝ) ^ n =
      ((⌊bbpPrimeReservoir n⌋ + ⌊bbpResidual n⌋ : ℤ) : ℝ) +
        (Int.fract (bbpPrimeReservoir n) + Int.fract (bbpResidual n) +
          16 ^ n * piTail n) := by
    have := bbp_split n
    push_cast
    rw [Int.fract, Int.fract, piTail]
    linarith [this, show Real.pi * 16 ^ n = 16 ^ n * Real.pi by ring,
      show (16 : ℝ) ^ n * (Real.pi - piPartial n) = 16 ^ n * Real.pi - 16 ^ n * piPartial n
        by ring]
  have hfr : orbit 16 Real.pi n = Int.fract (bbpPrimeReservoir n) +
      Int.fract (bbpResidual n) + 16 ^ n * piTail n := by
    rw [orbit, Int.fract_eq_iff]
    refine ⟨by linarith, by rw [he] at *; linarith,
      ⌊bbpPrimeReservoir n⌋ + ⌊bbpResidual n⌋, ?_⟩
    push_cast at hsplit ⊢
    linarith
  rw [hfr]
  constructor <;> [linarith; (rw [he] at *; linarith)]

end NormalNumbers.PiDisjunctiveRoutes
