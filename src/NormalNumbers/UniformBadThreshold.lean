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

* `twelve_fifths_le_cStar : 12/5 ≤ c⋆` — **proved** (25-window certificate, bases 2, 3, 5, 10).
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

/-! ## Lower bounds by finite certificates

A window `(b, n, k, δ)` is the closed interval `[(k − δ)/bⁿ, (k + δ)/bⁿ]`, on which
`‖bⁿξ‖ ≤ δ`.  A chain of windows covering `[0, 1)` with `δ_b ≤ b^{−p/q}` refutes `Admissible (p/q)`.
The certificates are produced by exact-rational greedy covering
(`scripts/uniformbad_cstar_cover.py`). -/

open NormalNumbers.UniformBad (dnear_le_abs_sub)


abbrev Win := ℕ × ℕ × ℕ × ℚ

def Win.lo (w : Win) : ℚ := ((w.2.2.1 : ℚ) - w.2.2.2) / (w.1 : ℚ) ^ w.2.1
def Win.hi (w : Win) : ℚ := ((w.2.2.1 : ℚ) + w.2.2.2) / (w.1 : ℚ) ^ w.2.1

def coversFrom : ℚ → List Win → Bool
  | a, [] => decide (1 ≤ a)
  | a, w :: t => decide (w.lo ≤ a) && coversFrom w.hi t

theorem exists_win_of_coversFrom : ∀ (l : List Win) (a : ℚ), coversFrom a l = true →
    ∀ x : ℝ, (a : ℝ) ≤ x → x < 1 → ∃ w ∈ l, (w.lo : ℝ) ≤ x ∧ x ≤ w.hi
  | [], a, h, x, hax, hx1 => by
    simp only [coversFrom, decide_eq_true_eq] at h
    exact absurd (lt_of_le_of_lt ((by exact_mod_cast h : (1:ℝ) ≤ a).trans hax) hx1) (lt_irrefl _)
  | w :: t, a, h, x, hax, hx1 => by
    simp only [coversFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hxw : x ≤ w.hi
    · exact ⟨w, List.mem_cons_self .., ((by exact_mod_cast h.1 : (w.lo:ℝ) ≤ a)).trans hax, hxw⟩
    · obtain ⟨v, hv, hv'⟩ := exists_win_of_coversFrom t _ h.2 x (not_le.1 hxw).le hx1
      exact ⟨v, List.mem_cons_of_mem _ hv, hv'⟩

theorem abs_sub_le_of_mem_win (w : Win) (hb : 1 ≤ w.1) (x : ℝ) (h1 : (w.lo : ℝ) ≤ x)
    (h2 : x ≤ w.hi) : |(w.1 : ℝ) ^ w.2.1 * x - w.2.2.1| ≤ w.2.2.2 := by
  obtain ⟨b, n, k, d⟩ := w
  simp only [Win.lo, Win.hi] at h1 h2 ⊢
  push_cast at h1 h2
  have hs : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hs] at h1
  rw [le_div_iff₀ hs] at h2
  rw [abs_le]; constructor <;> nlinarith

theorem le_rpow_of_pow (p q : ℕ) (hq : q ≠ 0) (b : ℕ) (hb : 1 ≤ b) (d : ℚ)
    (h : d ^ q * (b : ℚ) ^ p ≤ 1) : (d : ℝ) ≤ (b : ℝ) ^ (-(p : ℝ) / q) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hr : 0 < (b : ℝ) ^ (-(p : ℝ) / q) := Real.rpow_pos_of_pos hb0 _
  have h5 : ((b : ℝ) ^ (-(p : ℝ) / q)) ^ q = ((b : ℝ) ^ p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_natCast, ← Real.rpow_neg hb0.le]
    congr 1; field_simp
  have hd' : (d : ℝ) ^ q * (b : ℝ) ^ p ≤ 1 := by exact_mod_cast h
  by_contra hc
  have := pow_lt_pow_left₀ (not_le.1 hc) hr.le hq
  rw [h5] at this
  have hb12 : (0:ℝ) < (b : ℝ) ^ p := by positivity
  have := mul_lt_mul_of_pos_right this hb12
  rw [inv_mul_cancel₀ hb12.ne'] at this
  linarith

def winOK (p q : ℕ) (w : Win) : Bool :=
  decide (2 ≤ w.1) && decide (0 ≤ w.2.2.2) && decide (w.2.2.2 ^ q * (w.1 : ℚ) ^ p ≤ 1)

theorem not_admissible_of_cert (p q : ℕ) (hq : q ≠ 0) (l : List Win)
    (hc : coversFrom 0 l = true) (hok : l.all (winOK p q) = true) : ¬ Admissible ((p : ℝ) / q) := by
  rintro ⟨ξ, hξ⟩
  set x := ξ - ⌊ξ⌋ with hx
  obtain ⟨w, hw, h1, h2⟩ := exists_win_of_coversFrom l 0 hc x (by simp [hx])
    (by rw [hx]; linarith [Int.lt_floor_add_one ξ])
  have hw' := List.all_eq_true.1 hok w hw
  simp only [winOK, Bool.and_eq_true, decide_eq_true_eq] at hw'
  obtain ⟨⟨hb, hd⟩, hp⟩ := hw'
  have habs := abs_sub_le_of_mem_win w (by omega) x h1 h2
  have hlt := hξ w.1 hb w.2.1
  have key : dnear ((w.1 : ℝ) ^ w.2.1 * ξ) ≤ w.2.2.2 := by
    refine (dnear_le_abs_sub _ ((w.2.2.1 : ℤ) + (w.1 : ℤ) ^ w.2.1 * ⌊ξ⌋)).trans ?_
    have e : (w.1 : ℝ) ^ w.2.1 * ξ - (((w.2.2.1 : ℤ) + (w.1 : ℤ) ^ w.2.1 * ⌊ξ⌋ : ℤ) : ℝ) =
        (w.1 : ℝ) ^ w.2.1 * x - w.2.2.1 := by push_cast; rw [hx]; ring
    rw [e]; exact habs
  have := le_rpow_of_pow p q hq w.1 (by omega) _ hp
  rw [neg_div] at this
  linarith

def cert125 : List Win :=
  [(2, 0, 0, 947/5000), (2, 4, 3, 947/5000), (5, 1, 1, 21/1000), (2, 2, 1, 947/5000), (2, 6, 19, 947/5000), (10, 1, 3, 39/10000), (3, 5, 73, 143/2000), (2, 4, 5, 947/5000), (3, 1, 1, 143/2000), (2, 3, 3, 947/5000), (5, 1, 2, 21/1000), (2, 5, 13, 947/5000), (2, 1, 1, 947/5000), (2, 5, 19, 947/5000), (5, 1, 3, 21/1000), (2, 3, 5, 947/5000), (3, 1, 2, 143/2000), (2, 4, 11, 947/5000), (3, 5, 170, 143/2000), (10, 1, 7, 39/10000), (2, 6, 45, 947/5000), (2, 2, 3, 947/5000), (5, 1, 4, 21/1000), (2, 4, 13, 947/5000), (2, 0, 1, 947/5000)]

theorem not_admissible_twelve_fifths : ¬ Admissible (12 / 5) := by
  have := not_admissible_of_cert 12 5 (by norm_num) cert125 (by decide +kernel) (by decide +kernel)
  norm_num at this ⊢; exact this

theorem le_cStar_of_not_admissible {c : ℝ} (h : ¬ Admissible c) : c ≤ cStar := by
  refine le_csInf ⟨24, admissible_24⟩ fun c' hc' => ?_
  by_contra hlt
  exact h (admissible_mono (not_le.1 hlt).le hc')

/-- **Headline (lower bound, frozen 2026-10-06).**  Proved by `cert125`.  `c⋆ ≥ 12/5`, beating the
base-2 bound `log₂ 3 ≈ 1.585` and the two-base bound `log₂ 5 ≈ 2.322`.

English proof sketch.  By `admissible_mono` it suffices that `12/5` itself is not admissible.  The
bases `2, …, 16` with `n ≤ 6` already exclude every `ξ ∈ [0, 1]` at `c = 12/5` (host probe: that
system empties below `c ≈ 2.44`).  Certify by a finite cover of `[0, 1]` by rational intervals,
each lying inside one forbidden window `(k − δ_b, k + δ_b)/bⁿ` with a rational `δ_b ≤ b^{−12/5}`. -/
theorem twelve_fifths_le_cStar : (12 : ℝ) / 5 ≤ cStar :=
  le_cStar_of_not_admissible not_admissible_twelve_fifths

/-- **Headline (upper bound, frozen 2026-10-06).**  Believed 55%.  `c⋆ ≤ 4`, improving `24`.

English proof sketch.  Split the bases at `B₀`.  Bases `b > B₀` go to the stage potential of
`UniformBad.exists_avoid_of_stagePotential` with obstacle radius `b^{−n−4}`; their stage sum
`Σ_{b > B₀} b^{−2}·(levels per stage)` is small once `B₀` is large.  Bases `b ≤ B₀` are handled
inside the same nested-window game by an explicit choice of child windows, using that at `c = 4`
the small-base forbidden windows have relative size `≤ 2^{−4}` and the host probe leaves positive
survivor measure (`.135` at `c = 3` with `b ≤ 12`).

Route (2026-10-07, `UniformBadRoute`): the base-charging engines stall below `c ≈ 7`, so the bases
`2, 3, 5, 6, 7` must be exact; the proof is to come from `cStar_le_of_treeCore` with the nodes
`SmallBaseTreeCore 4 {2,3,5,6,7}` and `TreeEngineSuffices`, perfect powers being free
(`admissible_iff_nonPerfectPow`). -/
theorem cStar_le_four : cStar ≤ 4 := by
  sorry

/-- **Stretch node.**  Believed 35%.  `c⋆ ≤ 3`. -/
def CStarLeThree : Prop := cStar ≤ 3

end NormalNumbers.UniformBadThreshold
