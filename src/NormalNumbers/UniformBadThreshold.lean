/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBad

/-!
# The optimal exponent in Bugeaud 10.36

`UniformBad.bugeaud_10_36` answers Bugeaud's Problem 10.36 with exponent `24`: some `ξ` has
`‖bⁿξ‖ > b^{−24}` for every base `b ≥ 2` and every `n ≥ 0`.  This file asks for the **optimal**
exponent

  `c⋆ = inf {c : some ξ has ‖bⁿξ‖ > b^{−c} for all b ≥ 2, n ≥ 0}`   (`cStar`).

Known before this file: `log₂ 3 ≤ c⋆ ≤ 24` (`UniformBad.not_uniformBad_of_third_le`,
`UniformBad.exists_uniformBad_allBases_24`).  As far as the 2026-10-03 freshness audit in
`UniformBad` found, no paper states any uniform exponent, so any located value of `c⋆` is new.

## Headlines (frozen 2026-10-06)

* `twelve_fifths_le_cStar : 12/5 ≤ c⋆` (believed 85%).
* `cStar_le_four : c⋆ ≤ 4` (believed 55%).

## Evidence (Ren, host probe 2026-10-06, exact interval propagation in floating point)

Survivors of the finite system `‖bⁿξ‖ > b^{−c}`, `b ≤ B`, `n ≤ N`, bisected in `c`:
* `B = 3, N = 14`; `B = 5, N = 10`; `B = 8, N = 8`: the system empties exactly below
  `c = log₂ 5 ≈ 2.3219`; the last survivors sit at `1/5` and `3/10` (`‖2ⁿ/5‖ ≥ 1/5`).
  Both are rational, so the bases `5` and `10` kill them.
* `B = 16, N = 6`: the system empties below `c ≈ 2.4403` (survivors near `0.30098`).
* At `c = 3` the survivor measure is `.030` (`B = 3, N = 12`), `.062` (`B = 6, N = 8`), `.135`
  (`B = 12, N = 5`), so the finite systems are far from empty.
So `c⋆` plausibly lies in `[2.44, 3]`.  A lower bound is a finite certificate (a cover of
`[0, 1]` by intervals, each excluded by one `(b, n)`); an upper bound needs an infinite
construction (small bases tracked explicitly, large bases by the `UniformBad` potential engine,
whose stage sum `Σ_b b^{−c/2}` converges for `c > 2`).

## Difficulty check

* **Proved implications.**  `admissible_mono`, `admissible_24`, `bddBelow_admissible`,
  `cStar_le_24`, `logb_two_three_le_cStar` (below).
* **Unproved premises.**  The two headlines.
* **Mechanisms.**  Lower: an exact rational interval certificate over bases `2..16`, checked by
  `decide`/`norm_num`.  Upper: split the bases at `B₀`; for `b ≤ B₀` an explicit nested-interval
  (or automaton) construction keeping `‖bⁿξ‖ > b^{−c}`; for `b > B₀` the stage potential of
  `UniformBad.exists_avoid_of_stagePotential`, whose tail `Σ_{b > B₀} b^{−c/2}` is small.  The
  difficulty is the joint control of the small bases, which are multiplicatively independent.
* **Known-false siblings.**  Rational `ξ` are never admissible (`b = q`, `n = 1`), so the
  rational survivors `1/5`, `3/10` of the small-base systems must be excluded by larger bases.
  Any mechanism that only uses bases `2, 3` cannot beat `log₂ 5`.
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

/-- `c` is **admissible** for Bugeaud 10.36: some `ξ` has `‖bⁿξ‖ > b^{−c}` for every base `b ≥ 2`
and every `n ≥ 0`. -/
def Admissible (c : ℝ) : Prop :=
  ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ∀ n : ℕ, (b : ℝ) ^ (-c) < dnear ((b : ℝ) ^ n * ξ)

/-- The optimal Bugeaud 10.36 exponent `c⋆ = inf {c : Admissible c}`. -/
noncomputable def cStar : ℝ := sInf {c : ℝ | Admissible c}

/-- A larger exponent is easier. -/
theorem admissible_mono {c c' : ℝ} (h : c ≤ c') (hc : Admissible c) : Admissible c' := by
  obtain ⟨ξ, hξ⟩ := hc
  refine ⟨ξ, fun b hb n => lt_of_le_of_lt ?_ (hξ b hb n)⟩
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  exact Real.rpow_le_rpow_of_exponent_le hb1 (neg_le_neg h)

/-- The repo's answer to 10.36: `24` is admissible. -/
theorem admissible_24 : Admissible 24 := by
  obtain ⟨ξ, -, h⟩ := UniformBad.exists_uniformBad_allBases_24
  exact ⟨ξ, h⟩

/-- No exponent `c` with `2^{−c} ≥ 1/3` is admissible (base 2, `n = 0, 1`). -/
theorem not_admissible_of_third_le {c : ℝ} (hc : (1 : ℝ) / 3 ≤ (2 : ℝ) ^ (-c)) :
    ¬ Admissible c :=
  UniformBad.not_uniformBad_of_third_le hc

theorem bddBelow_admissible : BddBelow {c : ℝ | Admissible c} := by
  refine ⟨1, fun c hc => ?_⟩
  by_contra h
  exact UniformBad.not_uniformBad_of_le_one (le_of_lt (not_le.1 h)) hc

theorem cStar_le_24 : cStar ≤ 24 :=
  csInf_le bddBelow_admissible admissible_24

/-- The old lower bound `log₂ 3 ≤ c⋆`. -/
theorem logb_two_three_le_cStar : Real.logb 2 3 ≤ cStar := by
  refine le_csInf ⟨24, admissible_24⟩ fun c hc => ?_
  by_contra h
  refine not_admissible_of_third_le ?_ hc
  have h2 : (2 : ℝ) ^ (-c) = ((2 : ℝ) ^ c)⁻¹ := Real.rpow_neg (by norm_num) c
  have h3 : (2 : ℝ) ^ c < 3 := by
    rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 3)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (not_le.1 h)
  rw [h2, one_div]
  exact inv_anti₀ (by positivity) h3.le

/-- **Headline (lower bound, frozen 2026-10-06).**  Believed 85%.  `c⋆ ≥ 12/5`, beating the
base-2 bound `log₂ 3 ≈ 1.585` and the two-base bound `log₂ 5 ≈ 2.322`.

English proof sketch.  By `admissible_mono` it suffices that `12/5` itself is not admissible.  The
bases `2, …, 16` with `n ≤ 6` already exclude every `ξ ∈ [0, 1]` at `c = 12/5` (host probe: that
system empties below `c ≈ 2.44`).  Certify by a finite cover of `[0, 1]` by rational intervals,
each lying inside one forbidden window `(k − δ_b, k + δ_b)/bⁿ` with a rational `δ_b ≤ b^{−12/5}`. -/
theorem twelve_fifths_le_cStar : (12 : ℝ) / 5 ≤ cStar := by
  sorry

/-- **Headline (upper bound, frozen 2026-10-06).**  Believed 55%.  `c⋆ ≤ 4`, improving `24`.

English proof sketch.  Split the bases at `B₀`.  Bases `b > B₀` go to the stage potential of
`UniformBad.exists_avoid_of_stagePotential` with obstacle radius `b^{−n−4}`; their stage sum
`Σ_{b > B₀} b^{−2}·(levels per stage)` is small once `B₀` is large.  Bases `b ≤ B₀` are handled
inside the same nested-window game by an explicit choice of child windows, using that at `c = 4`
the small-base forbidden windows have relative size `≤ 2^{−4}` and the host probe leaves positive
survivor measure (`.135` at `c = 3` with `b ≤ 12`). -/
theorem cStar_le_four : cStar ≤ 4 := by
  sorry

/-- **Stretch node.**  Believed 35%.  `c⋆ ≤ 3`. -/
def CStarLeThree : Prop := cStar ≤ 3

end NormalNumbers.UniformBadThreshold
