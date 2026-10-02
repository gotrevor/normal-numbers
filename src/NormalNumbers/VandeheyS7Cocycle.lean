/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Distortion

/-!
# Distortion is an exact cocycle (Route A, node 1, mechanism)

`VandeheyS7Distortion` showed that a uniform distortion bound is a full substitute for
Vandehey's finite state set.  The obligation left open there is the window lemma
`BddDistortion`: the post-emission states of the `φ`-machine have uniformly bounded distortion.
Correction 1 of 2026-08-24 warns that Vandehey's Lemma 2.1 is an INTEGER DESCENT — over the dense
ring `ℤ[φ]` there is nothing to descend on — so the proof must be new.  This file supplies the
mechanism the new proof will run on.

## The identity

For a state `s` and a point `x`, write `den s x = s.c * x + s.d`.  The composite state `s ∘ t`
has

    den (s ∘ t) x = den t x * den s (t x)                          (`den_comp`)

**exactly** — no inequality, no constant.  Denominators are a cocycle over the action.  Hence the
two-point distortion `distOn s u v = den s v / den s u` is exactly multiplicative:

    distOn (s ∘ t) u v = distOn t u v * distOn s (t u) (t v)       (`distOn_comp`)

and the distortion of a composite factorises into the inner map's distortion times the OUTER
map's distortion **measured on the inner map's image**.

## Why that is the window lemma's mechanism

The post-emission state of the `φ`-machine is `A_out⁻¹ · M₀ · A_{a₁} ⋯ A_{aₙ}`.  The right-hand
factor is a composition of Gauss inverse branches, whose distortion is the classical Rényi
constant — this is exactly the measured "`log 4` for every integer control".  The left-hand
factor is the drifting `ℤ[φ]` part, and it is the one with no finiteness certificate.  But
`distOn_comp` says the drifting factor is only ever evaluated on the inner image, and

    distOn s u v ≤ 1 + (v − u) * distortion s                      (`distOn_le_one_add`)

so its contribution tends to `1` as that image shrinks.  Combining,

    distortion (s ∘ t) ≤ distortion t * (1 + |t([0,1])| * distortion s)   (`distortion_comp_le`)

which is the inductive step a window bound needs: the inner Gauss factor supplies a bound that
does not grow, and the outer factor's unbounded entries enter only through a term that the
shrinking image kills.  This is the structural reason the probes measured the `ℤ[φ]` distortion
saturating (`≈ 2.5`) rather than drifting, even while the conjugate place ran to `10^644`.

**What is still open**: the quantitative loop — that the emission rule keeps `|t([0,1])|` small
enough, often enough, for the product to stay bounded.  That needs the emission rule, i.e. the
`φ`-transducer as a Lean object, and is the next node.

## Guard rule

Content locator: `distOn_self` (`distOn s u u = 1`) and `comp_idState`.  Degenerate case: the
factorisation is an equality, so no slack is hidden in it; `distortion_comp_le` is the only
inequality and it is proved from the equality plus `distOn_le_one_add`.
-/

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- The denominator of the state's Möbius map. -/
noncomputable def den (s : MobState) (x : ℝ) : ℝ := s.c * x + s.d

theorem den_pos' (s : MobState) {x : ℝ} (hx : 0 ≤ x) : 0 < s.den x := s.den_pos hx

/-- **Composition**: the matrix product, `s ∘ t`.  The family is closed under it — that is what
the nonnegativity fields are for. -/
noncomputable def comp (s t : MobState) : MobState where
  a := s.a * t.a + s.b * t.c
  b := s.a * t.b + s.b * t.d
  c := s.c * t.a + s.d * t.c
  d := s.c * t.b + s.d * t.d
  ha := add_nonneg (mul_nonneg s.ha t.ha) (mul_nonneg s.hb t.hc)
  hb := add_nonneg (mul_nonneg s.ha t.hb) (mul_nonneg s.hb t.hd.le)
  hc := add_nonneg (mul_nonneg s.hc t.ha) (mul_nonneg s.hd.le t.hc)
  hd := add_pos_of_nonneg_of_pos (mul_nonneg s.hc t.hb) (mul_pos s.hd t.hd)
  hdet := by
    have hid : (s.a * t.a + s.b * t.c) * (s.c * t.b + s.d * t.d)
        - (s.a * t.b + s.b * t.d) * (s.c * t.a + s.d * t.c)
        = (s.a * s.d - s.b * s.c) * (t.a * t.d - t.b * t.c) := by ring
    rw [hid]
    exact mul_ne_zero s.hdet t.hdet

@[simp] theorem comp_a (s t : MobState) : (s.comp t).a = s.a * t.a + s.b * t.c := rfl
@[simp] theorem comp_b (s t : MobState) : (s.comp t).b = s.a * t.b + s.b * t.d := rfl
@[simp] theorem comp_c (s t : MobState) : (s.comp t).c = s.c * t.a + s.d * t.c := rfl
@[simp] theorem comp_d (s t : MobState) : (s.comp t).d = s.c * t.b + s.d * t.d := rfl

/-- **The cocycle identity for denominators.**  Exact; no constant, no inequality. -/
theorem den_comp (s t : MobState) {x : ℝ} (hx : 0 ≤ x) :
    (s.comp t).den x = t.den x * s.den (t.mob x) := by
  have ht : 0 < t.c * x + t.d := t.den_pos hx
  simp only [den, mob, comp_c, comp_d]
  field_simp
  ring

/-- Composition of states is composition of maps. -/
theorem mob_comp (s t : MobState) {x : ℝ} (hx : 0 ≤ x) :
    (s.comp t).mob x = s.mob (t.mob x) := by
  have ht : 0 < t.c * x + t.d := t.den_pos hx
  simp only [mob, comp_a, comp_b, comp_c, comp_d]
  rw [div_eq_div_iff (by
      have := (s.comp t).den_pos hx; simpa [den] using this.ne')
    (by
      have : 0 < s.c * ((t.a * x + t.b) / (t.c * x + t.d)) + s.d := by
        refine add_pos_of_nonneg_of_pos (mul_nonneg s.hc ?_) s.hd
        exact div_nonneg (add_nonneg (mul_nonneg t.ha hx) t.hb) ht.le
      exact this.ne')]
  field_simp
  ring

/-! ## The two-point distortion -/

/-- The distortion of `s` measured on `[u, v]`: the ratio of the denominators at the endpoints.
`distortion s = distOn s 0 1`. -/
noncomputable def distOn (s : MobState) (u v : ℝ) : ℝ := s.den v / s.den u

@[simp] theorem distOn_self (s : MobState) (u : ℝ) (hu : 0 ≤ u) : s.distOn u u = 1 :=
  div_self (s.den_pos' hu).ne'

theorem distortion_eq_distOn (s : MobState) : s.distortion = s.distOn 0 1 := by
  simp [distortion, distOn, den]

theorem distOn_pos (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 < s.distOn u v :=
  div_pos (s.den_pos' hv) (s.den_pos' hu)

/-- **Distortion is an exact cocycle.**  The composite's distortion on `[u,v]` is the inner
map's distortion on `[u,v]` times the outer map's distortion on the image `[t u, t v]`. -/
theorem distOn_comp (s t : MobState) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (s.comp t).distOn u v = t.distOn u v * s.distOn (t.mob u) (t.mob v) := by
  have hdu : 0 < t.den u := t.den_pos' hu
  have hdv : 0 < t.den v := t.den_pos' hv
  have hmu : 0 ≤ t.mob u := by
    rw [mob]
    exact div_nonneg (add_nonneg (mul_nonneg t.ha hu) t.hb) (t.den_pos hu).le
  have hmv : 0 ≤ t.mob v := by
    rw [mob]
    exact div_nonneg (add_nonneg (mul_nonneg t.ha hv) t.hb) (t.den_pos hv).le
  have hsu : 0 < s.den (t.mob u) := s.den_pos' hmu
  simp only [distOn, den_comp s t hu, den_comp s t hv]
  field_simp

/-- **The outer factor's contribution is `1 + O(length)`.**  On a short interval, a state's
distortion is close to `1`, with its own distortion as the coefficient.  No upper bound on `v`
is needed, so the estimate is available at every stage of the composition. -/
theorem distOn_le_one_add (s : MobState) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    s.distOn u v ≤ 1 + (v - u) * s.distortion := by
  have hdu : 0 < s.den u := s.den_pos' hu
  have hvu : 0 ≤ v - u := by linarith
  rw [distOn, div_le_iff₀ hdu, distortion]
  simp only [den]
  have hd : 0 < s.d := s.hd
  have hle : s.d ≤ s.c * u + s.d := s.le_den hu
  have hexp : (1 + (v - u) * ((s.c + s.d) / s.d)) * (s.c * u + s.d)
      = (s.c * u + s.d) + (v - u) * ((s.c + s.d) * (s.c * u + s.d) / s.d) := by
    field_simp
  rw [hexp]
  have hkey : s.c * (v - u) ≤ (v - u) * ((s.c + s.d) * (s.c * u + s.d) / s.d) := by
    rcases eq_or_lt_of_le hvu with h | h
    · simp [← h]
    · rw [mul_comm (s.c) (v - u)]
      refine mul_le_mul_of_nonneg_left ?_ hvu
      rw [le_div_iff₀ hd]
      nlinarith [s.hc, hle, hd]
  linarith [hkey]

/-- **The inductive step a window bound runs on.**  The composite's distortion is the inner
map's, times a factor that the shrinking inner image drives to `1`. -/
theorem distortion_comp_le (s t : MobState) (h0 : t.mob 0 ≤ t.mob 1) :
    (s.comp t).distortion ≤ t.distortion * (1 + (t.mob 1 - t.mob 0) * s.distortion) := by
  have hm0 : 0 ≤ t.mob 0 := by
    rw [mob]; exact div_nonneg (by simpa using t.hb) (t.den_pos' (le_refl 0)).le
  rw [distortion_eq_distOn, distOn_comp s t (le_refl 0) zero_le_one,
    ← distortion_eq_distOn]
  exact mul_le_mul_of_nonneg_left (s.distOn_le_one_add hm0 h0) t.distortion_pos.le

end MobState

/-! ## Content locator (guard rule) -/

theorem comp_idState (s : MobState) : s.comp MobState.idState = s := by
  cases s
  simp [MobState.comp, MobState.idState]

section Audit

#print axioms MobState.den_comp
#print axioms MobState.distOn_comp
#print axioms MobState.distortion_comp_le

end Audit

end NormalNumbers.VandeheyS7
