/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Clock

/-!
# The compact-fiber substitute: bounded distortion (Route A, node 1)

`VandeheyS7Clock` reduced Vandehey §7 Problem 1 to `SampledUniformCount q r₀ ℓ`, and identified
it as the only place where the lost `ℤ[φ]` finiteness must be replaced.  This file supplies the
*mechanism* of the replacement, in the kernel.

## Why distortion and not compactness

The attack map's original Route A said "state space = a compact window in `PGL₂(ℝ)`".  The
2026-08-24 probe **refuted** that phrasing (correction 2): the raw post-emission state set is
unbounded in the PROVED integer case too — a state straddling `1/c` at depth `ε` has entries
`≈ √(D/ε)` — and `2x` climbs exactly the way `φ` does.  What is bounded on both sides is the
**distortion**: exactly `log 4` for every integer control, saturating `≈ 2.5` for every `ℤ[φ]`
map.  So the window lemma must be stated for distortion, and this file is where that choice is
made to pay.

## What is proved here

For a state `s` acting as the Möbius map `x ↦ (a x + b)/(c x + d)` with `c ≥ 0 < d` and positive
determinant — the shape every post-emission Raney state has, over **any** ring —

    distortion s := (c + d) / d ≥ 1                               (`one_le_distortion`)

and the **comparability theorem** (`mob_ratio_comparable`): for `0 ≤ u ≤ v ≤ 1`,

    (v − u) / distortion s  ≤  (M v − M u) / (M 1 − M 0)  ≤  (v − u) · distortion s .

This is exactly the rôle the finite state set played in Vandehey §5–§6.  With finitely many states
one gets an exact constant per state and takes a max; with bounded distortion one gets **uniform
two-sided comparability with a single constant**, which is all the Riemann squeeze of his `f_j^±`
approximants ever consumes.  `uniform_comparable_of_bddDistortion` states that consequence along
a whole sequence of states: a uniform distortion bound gives uniform comparison constants, with
no finiteness anywhere.

So the open obligation is now narrowed to the *hypothesis* `BddDistortion`, i.e. Route A's window
lemma: the post-emission states of the `φ`-machine have uniformly bounded distortion.  That is
the next thing to build (it needs the `φ`-transducer as a Lean object), and the 2026-08-24 probe
measured it holding, with the warning that the integer descent of Vandehey's Lemma 2.1 does NOT
port and a different proof is needed (correction 1).

## Guard rule

Content locator: `distortion_id` — the identity map has distortion `1` and the comparability
theorem degenerates to an equality, so the content is entirely in the bound on `c/d`.  Degenerate
case: `distortion` is unbounded over the full state set (`not_bddAbove_distortion`), so
`BddDistortion` is a genuine restriction and not a theorem of the ambient setting.
-/

namespace NormalNumbers.VandeheyS7

open Filter

/-- A Möbius state in the shape every post-emission Raney state has: nonnegative lower row,
positive `d`, nonzero determinant (either sign: Raney states have `det = ±D`), and a nonnegative upper row so that the family is closed under composition
(`VandeheyS7Cocycle`).  Nothing here is about `ℤ`, `ℤ[φ]` or any ring — that is the
point. -/
structure MobState where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  ha : 0 ≤ a
  hb : 0 ≤ b
  hc : 0 ≤ c
  hd : 0 < d
  hdet : a * d - b * c ≠ 0

namespace MobState

/-- The Möbius action on `[0,1]`. -/
noncomputable def mob (s : MobState) (x : ℝ) : ℝ := (s.a * x + s.b) / (s.c * x + s.d)

/-- The denominator is positive on `[0,1]`. -/
theorem den_pos (s : MobState) {x : ℝ} (hx : 0 ≤ x) : 0 < s.c * x + s.d :=
  add_pos_of_nonneg_of_pos (mul_nonneg s.hc hx) s.hd

/-- **The distortion of the state on `[0,1]`**: the ratio of the largest to the smallest value of
the denominator, which is the square root of the ratio of the largest to the smallest derivative.
This is the quantity the 2026-08-24 probe found bounded on both sides of the ℤ / ℤ[φ] divide. -/
noncomputable def distortion (s : MobState) : ℝ := (s.c + s.d) / s.d

theorem one_le_distortion (s : MobState) : 1 ≤ s.distortion := by
  rw [distortion, le_div_iff₀ s.hd]
  linarith [s.hc]

theorem distortion_pos (s : MobState) : 0 < s.distortion :=
  lt_of_lt_of_le zero_lt_one s.one_le_distortion

/-- The denominator is squeezed between `d` and `c + d` on `[0,1]`. -/
theorem den_le (s : MobState) {x : ℝ} (hx : x ≤ 1) : s.c * x + s.d ≤ s.c + s.d := by
  nlinarith [s.hc]

theorem le_den (s : MobState) {x : ℝ} (hx : 0 ≤ x) : s.d ≤ s.c * x + s.d := by
  nlinarith [s.hc]

/-- The increment formula: the determinant over the two denominators. -/
theorem mob_sub (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    s.mob v - s.mob u
      = (s.a * s.d - s.b * s.c) * (v - u) / ((s.c * v + s.d) * (s.c * u + s.d)) := by
  have hpu := s.den_pos hu
  have hpv := s.den_pos hv
  have h1 : s.c * v + s.d ≠ 0 := hpv.ne'
  have h2 : s.c * u + s.d ≠ 0 := hpu.ne'
  simp only [mob]
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  ring

/-- The image of the whole interval is nondegenerate.  Its orientation is the sign of the
determinant, which the comparability ratio below is insensitive to. -/
theorem mob_one_sub_mob_zero_ne (s : MobState) : s.mob 1 - s.mob 0 ≠ 0 := by
  rw [s.mob_sub (by norm_num) (by norm_num)]
  have h0 := s.den_pos (le_refl (0:ℝ))
  have h1 := s.den_pos (zero_le_one)
  have : (0:ℝ) < (s.c * 1 + s.d) * (s.c * 0 + s.d) := mul_pos h1 h0
  refine div_ne_zero ?_ this.ne'
  simpa using s.hdet

/-! ## The comparability theorem -/

/-- **Bounded distortion ⇒ two-sided comparability of relative lengths.**  For `0 ≤ u ≤ v ≤ 1`,
the relative length of `[u,v]`'s image inside the image of `[0,1]` is within a factor
`distortion s` of `v − u`, in both directions.

This is the exact rôle the finite state set played in Vandehey §5–§6: there one takes a maximum
over finitely many states, here one constant covers the whole family.  No ring, no determinant
size, no finiteness. -/
theorem mob_ratio_comparable (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (v - u) / s.distortion ≤ (s.mob v - s.mob u) / (s.mob 1 - s.mob 0) ∧
      (s.mob v - s.mob u) / (s.mob 1 - s.mob 0) ≤ (v - u) * s.distortion := by
  have hu' : (0:ℝ) ≤ u := hu
  have hv' : (0:ℝ) ≤ v := le_trans hu huv
  have hpu := s.den_pos hu'
  have hpv := s.den_pos hv'
  have hp0 := s.den_pos (le_refl (0:ℝ))
  have hp1 := s.den_pos (zero_le_one)
  have hdenom : s.mob 1 - s.mob 0 ≠ 0 := s.mob_one_sub_mob_zero_ne
  -- the ratio, computed
  have hratio : (s.mob v - s.mob u) / (s.mob 1 - s.mob 0)
      = (v - u) * ((s.c + s.d) * s.d) / ((s.c * v + s.d) * (s.c * u + s.d)) := by
    rw [s.mob_sub hu' hv', s.mob_sub (le_refl (0:ℝ)) (zero_le_one)]
    have hd0 : s.c * (0:ℝ) + s.d = s.d := by ring
    have hd1 : s.c * (1:ℝ) + s.d = s.c + s.d := by ring
    rw [hd0, hd1]
    have hne : s.a * s.d - s.b * s.c ≠ 0 := s.hdet
    field_simp
    ring
  have hvu : 0 ≤ v - u := by linarith
  have hcd : 0 < s.c + s.d := by linarith [s.hc, s.hd]
  have hub : (s.c * v + s.d) * (s.c * u + s.d) ≤ (s.c + s.d) * (s.c + s.d) :=
    mul_le_mul (s.den_le hv) (s.den_le (le_trans huv hv)) hpu.le hcd.le
  have hlb : s.d * s.d ≤ (s.c * v + s.d) * (s.c * u + s.d) :=
    mul_le_mul (s.le_den hv') (s.le_den hu') s.hd.le hpv.le
  refine ⟨?_, ?_⟩
  · rw [hratio, distortion, div_div_eq_mul_div,
      div_le_div_iff₀ hcd (mul_pos hpv hpu)]
    nlinarith [mul_nonneg hvu s.hd.le, s.hd, hcd]
  · rw [hratio, distortion, ← mul_div_assoc,
      div_le_div_iff₀ (mul_pos hpv hpu) s.hd]
    nlinarith [mul_nonneg hvu hcd.le, s.hd]

/-! ## Content locator and degenerate case (guard rule) -/

/-- The identity state.  Distortion `1`; the comparability theorem degenerates to an equality, so
all the content is in the bound on `c / d`. -/
noncomputable def idState : MobState :=
  ⟨1, 0, 0, 1, zero_le_one, le_refl 0, le_refl 0, one_pos, by norm_num⟩

theorem distortion_id : idState.distortion = 1 := by
  simp [distortion, idState]

/-- Distortion is genuinely unbounded over the ambient family, so a uniform bound on it is a real
hypothesis about the machine and not a theorem of the setting. -/
theorem not_bddAbove_distortion :
    ¬ BddAbove (Set.range (fun s : MobState => s.distortion)) := by
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt K
  have hmem : (⟨1, 0, (n : ℝ), 1, zero_le_one, le_refl 0, Nat.cast_nonneg n, one_pos, by norm_num⟩ :
      MobState).distortion ∈ Set.range (fun s : MobState => s.distortion) := ⟨_, rfl⟩
  have := hK hmem
  simp only [distortion] at this
  rw [div_one] at this
  linarith

end MobState

/-! ## The named window hypothesis and its payoff -/

/-- **Route A's window lemma, as a named hypothesis.**  The post-emission states of the machine
have uniformly bounded distortion.  OPEN; the `φ`-transducer must be built before it can be
attacked, and the integer descent of Vandehey's Lemma 2.1 does not port (correction 1 of
2026-08-24).  Measured to hold, saturating `≈ 2.5`, by both 2026-08 probes. -/
def BddDistortion (s : ℕ → MobState) : Prop :=
  ∃ K : ℝ, ∀ n, (s n).distortion ≤ K

/-- **The payoff.**  A uniform distortion bound gives uniform, two-sided comparison constants
along the whole state sequence — the finite-state maximum of Vandehey §5–§6, with the finiteness
removed.  `1 ≤ K` comes for free, so the constant is usable on both sides. -/
theorem uniform_comparable_of_bddDistortion {s : ℕ → MobState} (h : BddDistortion s) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (n : ℕ) {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 →
      (v - u) / K ≤ ((s n).mob v - (s n).mob u) / ((s n).mob 1 - (s n).mob 0) ∧
        ((s n).mob v - (s n).mob u) / ((s n).mob 1 - (s n).mob 0) ≤ (v - u) * K := by
  obtain ⟨K, hK⟩ := h
  refine ⟨max 1 K, le_max_left _ _, fun n u v hu huv hv => ?_⟩
  obtain ⟨hlo, hhi⟩ := (s n).mob_ratio_comparable hu huv hv
  have hKn : (s n).distortion ≤ max 1 K := le_trans (hK n) (le_max_right _ _)
  have hvu : 0 ≤ v - u := by linarith
  have hdpos := (s n).distortion_pos
  have hmpos : (0:ℝ) < max 1 K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  constructor
  · refine le_trans ?_ hlo
    gcongr
  · exact le_trans hhi (by nlinarith)

section Audit

#print axioms MobState.mob_ratio_comparable
#print axioms MobState.not_bddAbove_distortion
#print axioms uniform_comparable_of_bddDistortion

end Audit

end NormalNumbers.VandeheyS7
