/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PiDisjunctiveRoutes.ReservoirCutoffSix

/-! # Vanishing versus nonvanishing of the cutoff-six exits

`exit_six_not_eventually_small` gives only a `p^{-2/3}` lower bound, which
tends to zero; it decides neither alternative below.  We isolate a
sufficient arithmetic statement (`CubicRootEscape`) about the specific
cube root `2^((p+31)/6)` of `1024` modulo primes `p ≡ 89 (mod 120)`, and
prove it implies nonvanishing.  This is a reformulation of a sufficient
condition, not a proof; the finite census is evidence only.
-/

namespace NormalNumbers.PiDisjunctiveRoutes.CutoffSix

open CutoffReview Filter

/-- Distance to the nearest integer. -/
noncomputable def dZ (x : ℝ) : ℝ := |x - round x|

/-- Vanishing alternative: `‖E₆(n)‖ℤ → 0`. -/
def ExitSixVanishing : Prop :=
  Tendsto (fun n => dZ (rationalExit 6 n : ℝ)) atTop (nhds 0)

/-- Nonvanishing alternative. -/
def ExitSixNonvanishing : Prop :=
  ∃ ε > 0, ∀ N, ∃ n ≥ N, ε ≤ dZ (rationalExit 6 n : ℝ)

theorem not_vanishing_of_nonvanishing (h : ExitSixNonvanishing) :
    ¬ ExitSixVanishing := by
  obtain ⟨ε, hε, h⟩ := h
  intro hv
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hv) ε hε
  obtain ⟨n, hn, hle⟩ := h N
  have := hN n hn
  simp only [Real.dist_eq, sub_zero, dZ, abs_abs] at this
  exact absurd hle (not_le.2 (by simpa [dZ] using this))

/-- **Open arithmetic node (sufficient for nonvanishing).**  The cube root
`A_p = 2^(20m+18)` of `1024` modulo `p = 120m+89` stays a positive
proportion away from `0 mod p` infinitely often.  Heuristic: `A_p/p` should
be equidistributed (Artin/Hooley-type statement about `2^((p+31)/6) mod p`);
no proof mechanism is known.  Confidence true: ~95%; provability now: low. -/
def CubicRootEscape : Prop :=
  ∃ ε > 0, ∀ N, ∃ m ≥ N, Nat.Prime (120*m+89) ∧
    ε ≤ dZ (((2:ℚ)^(20*m+18) / (120*m+89) : ℚ) : ℝ)

theorem nonvanishing_of_cubicRootEscape (h : CubicRootEscape) :
    ExitSixNonvanishing := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun N => ?_⟩
  obtain ⟨m, hm, hp, hle⟩ := h N
  exact ⟨20*m+14, by omega, by rwa [rationalExit_six_eq m hp]⟩

end NormalNumbers.PiDisjunctiveRoutes.CutoffSix
