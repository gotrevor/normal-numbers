/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-GW: the greedy run's width ledger — reading costs, emitting pays

S7-GR built the greedy transducer (flush after every read).  This module prices its two moves
exactly, which is what turns the lap-91 probe's picture (`slack = log(1/width)` stays bounded, for
the greedy run but not for the throttled one) into arithmetic.

* `width_emit_ge` — **an emission of the digit `b` multiplies the width by at least `b²`**:
  `EmitStep t b u → b² · width t ≤ width u`.  The emission's four endpoint inequalities read off the
  `EmitStep` equations directly (`t.d = u.b + b·u.d` with `u.b ≥ 0`, and the same at `1`), so this
  is exact bookkeeping, no estimates.
* `width_flushState_ge` — hence **the flush never narrows**: `width t ≤ width (flushState t)`.
* `width_comp_readMap_ge` — **a read of the digit `a` costs at most a factor
  `a·(a+1)·(r + 2 + 1/r)`**, where `r = denRatio t` is the state's distortion coordinate:
  `width t / (a·(a+1)·(r + 2 + 1/r)) ≤ width (t.comp (readMap a))`.
* `width_grunState_succ_ge` — the greedy run's recursion: the width at time `n+1` is at least the
  width at time `n` divided by that factor at the digit just read.

So along the greedy run `slack` is a walk that **gains at most `log(a·(a+1)·(r+2+1/r))` per read and
loses `2 log b` per emitted digit** — and the flush keeps emitting until the state is reduced.  The
probe says the walk stays bounded; the outstanding obligation is the frequency statement, and S7-SS
already identifies it: a reduced state's endpoint lies in `straddleSet (width)`, whose measure is
`≍ √width` (S7-SM), so the width debt for the GREEDY run is exactly *the run's endpoint rarely
lands near a cylinder boundary*.  That is a joint-equidistribution statement about
`(state, input point)`, i.e. the same wall as fact (δ) — but now in a shape with a `√η` target
instead of a refuted hypothesis.

## Guard rule

**Content locator.**  Both ledger bounds come from `width_eq` (`width = |det| / (d·(c+d))`) plus the
structural inequalities of `MapState`; the read bound's only inequality is
`S + (a−1)D ≤ a(S+D)` and `S + aD ≤ (a+1)(S+D)` with `S = c+d`, `D = d`.

**Degenerate cases.**  `a = 1`: the read costs at most `2(r+2+1/r)`.  `b = 1`: the emission is free
(factor `1`), which is why bursts of `1`s neither gain nor lose.  A non-emittable `t` has
`flushState t = t` and the flush bound is an equality.
-/
import NormalNumbers.VandeheyS7Greedy

namespace NormalNumbers.VandeheyS7

open Set NormalNumbers

namespace MapState

/-! ## Emitting pays -/

/-- **An emission of the digit `b` multiplies the width by at least `b²`.** -/
theorem width_emit_ge {t : MapState} {b : ℕ} {u : MapState} (h : EmitStep t b u) :
    ((b : ℝ)) ^ 2 * t.width ≤ u.width := by
  obtain ⟨hb, hc, hd, hcc, hdd⟩ := h
  have hbR : (1:ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0:ℝ) < (b : ℝ) := by linarith
  -- the determinants agree in absolute value
  have hdet : |u.det| = |t.det| := by
    have : t.det = - u.det := by
      simp only [det]
      rw [hcc, hdd, hc, hd]
      ring
    rw [this, abs_neg]
  have hud : (0:ℝ) < u.d := u.hd
  have hucd : (0:ℝ) < u.c + u.d := u.hcd
  have htb : (0:ℝ) < t.b := by rw [← hd]; exact hud
  have htab : (0:ℝ) < t.a + t.b := by rw [← hc, ← hd]; exact hucd
  have htd : (0:ℝ) < t.d := t.hd
  have htcd : (0:ℝ) < t.c + t.d := t.hcd
  -- the endpoint inequalities, read off the `EmitStep` equations
  have h1 : (b : ℝ) * t.b ≤ t.d := by
    rw [hdd, hd]
    linarith [u.hb0]
  have h2 : (b : ℝ) * (t.a + t.b) ≤ t.c + t.d := by
    have hsum : t.c + t.d = (u.a + u.b) + (b : ℝ) * (u.c + u.d) := by rw [hcc, hdd]; ring
    rw [hsum, ← hc, ← hd]
    linarith [u.hab0]
  have hwu : u.width = |t.det| / (t.b * (t.a + t.b)) := by
    rw [width_eq, hdet, hc, hd]
  have hwt : t.width = |t.det| / (t.d * (t.c + t.d)) := t.width_eq
  have hdenom : (b : ℝ) ^ 2 * (t.b * (t.a + t.b)) ≤ t.d * (t.c + t.d) := by
    have := mul_le_mul h1 h2 (by positivity) htd.le
    nlinarith
  have hdetpos : (0:ℝ) < |t.det| := abs_pos.mpr t.hdet
  rw [hwu, hwt, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The flush never narrows.** -/
theorem width_flushState_ge (t : MapState) : t.width ≤ (flushState t).width := by
  have key : ∀ n : ℕ, ∀ s : MapState, s.width ≤ (stepFst^[n] s).width := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ k ih =>
        intro s
        rw [Function.iterate_succ_apply]
        refine le_trans ?_ (ih (stepFst s))
        by_cases h : Emittable s
        · obtain ⟨b, hemit, -⟩ := step_emitStep h
          have hb : (1:ℝ) ≤ (b : ℕ) := by exact_mod_cast hemit.1
          have hle := width_emit_ge hemit
          have hsq : (1:ℝ) ≤ ((b : ℕ) : ℝ) ^ 2 := by nlinarith
          have hw0 : (0:ℝ) < s.width := width_pos s
          have : s.width ≤ ((b : ℕ) : ℝ) ^ 2 * s.width := by nlinarith
          exact le_trans this (by simpa [stepFst] using hle)
        · rw [stepFst, step_of_not_emittable h]
  exact key (flushLen t) t

/-! ## Reading costs -/

/-- **A read of the digit `a` costs at most the factor `a·(a+1)·(r + 2 + 1/r)`.** -/
theorem width_comp_readMap_ge (t : MapState) {a : ℝ} (ha : 1 ≤ a) :
    t.width / (a * (a + 1) * (t.denRatio + 2 + 1 / t.denRatio))
      ≤ (t.comp (readMap a ha)).width := by
  have ha0 : (0:ℝ) < a := by linarith
  have htd : (0:ℝ) < t.d := t.hd
  have htcd : (0:ℝ) < t.c + t.d := t.hcd
  set D : ℝ := t.d with hD
  set S : ℝ := t.c + t.d with hS
  have hr : t.denRatio = S / D := by rw [denRatio, hS, hD]
  have hrpos : (0:ℝ) < t.denRatio := t.denRatio_pos
  -- the composite's denominators
  have hcomp_d : (t.comp (readMap a ha)).d = S + (a - 1) * D := by
    show t.c * 1 + t.d * a = S + (a - 1) * D
    rw [hS, hD]; ring
  have hcomp_cd : (t.comp (readMap a ha)).c + (t.comp (readMap a ha)).d = S + a * D := by
    show (t.c * 0 + t.d * 1) + (t.c * 1 + t.d * a) = S + a * D
    rw [hS, hD]; ring
  have hcomp_det : |(t.comp (readMap a ha)).det| = |t.det| := by
    have hd : (t.comp (readMap a ha)).det = - t.det := by
      simp only [det]
      show (t.a * 0 + t.b * 1) * (t.c * 1 + t.d * a) - (t.a * 1 + t.b * a) * (t.c * 0 + t.d * 1)
        = -(t.a * t.d - t.b * t.c)
      ring
    rw [hd, abs_neg]
  have hdpos : (0:ℝ) < S + (a - 1) * D := by
    have := (t.comp (readMap a ha)).hd
    rw [hcomp_d] at this; exact this
  have hcdpos : (0:ℝ) < S + a * D := by
    have := (t.comp (readMap a ha)).hcd
    rw [hcomp_cd] at this; exact this
  have hwc : (t.comp (readMap a ha)).width = |t.det| / ((S + (a - 1) * D) * (S + a * D)) := by
    rw [width_eq, hcomp_det]
    rw [show (t.comp (readMap a ha)).d * ((t.comp (readMap a ha)).c + (t.comp (readMap a ha)).d)
        = (S + (a - 1) * D) * (S + a * D) from by rw [hcomp_d] at *; rw [← hcomp_cd, hcomp_d]]
  have hwt : t.width = |t.det| / (D * S) := by rw [width_eq, hD, hS]
  have hdetpos : (0:ℝ) < |t.det| := abs_pos.mpr t.hdet
  -- the two elementary bounds
  have hb1 : S + (a - 1) * D ≤ a * (S + D) := by nlinarith
  have hb2 : S + a * D ≤ (a + 1) * (S + D) := by nlinarith
  have hfac : (0:ℝ) < t.denRatio + 2 + 1 / t.denRatio := by positivity
  have hkey : (S + D) ^ 2 = (D * S) * (t.denRatio + 2 + 1 / t.denRatio) := by
    rw [hr]
    field_simp
    ring
  rw [hwc, hwt, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : (S + (a - 1) * D) * (S + a * D) ≤ (a * (a + 1)) * (S + D) ^ 2 := by
    have h1 : (0:ℝ) < S + D := by linarith
    calc (S + (a - 1) * D) * (S + a * D) ≤ (a * (S + D)) * ((a + 1) * (S + D)) :=
          mul_le_mul hb1 hb2 hcdpos.le (by positivity)
      _ = (a * (a + 1)) * (S + D) ^ 2 := by ring
  rw [hkey] at hprod
  nlinarith

/-- **The greedy run's width recursion.** -/
theorem width_grunState_succ_ge (Φ : MapState) (x : ℝ) (n : ℕ) :
    (grunState Φ x n).width
        / (((inDigit x n : ℕ) : ℝ) * (((inDigit x n : ℕ) : ℝ) + 1)
          * ((grunState Φ x n).denRatio + 2 + 1 / (grunState Φ x n).denRatio))
      ≤ (grunState Φ x (n + 1)).width := by
  have hread := width_comp_readMap_ge (grunState Φ x n) (one_le_inDigit_real x n)
  have hflush := width_flushState_ge ((grunState Φ x n).comp (readAt x n))
  have hstate : grunState Φ x (n + 1)
      = flushState ((grunState Φ x n).comp (readAt x n)) := rfl
  rw [hstate]
  refine le_trans ?_ hflush
  simpa [readAt] using hread

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.width_emit_ge
#print axioms NormalNumbers.VandeheyS7.MapState.width_flushState_ge
#print axioms NormalNumbers.VandeheyS7.MapState.width_comp_readMap_ge
#print axioms NormalNumbers.VandeheyS7.MapState.width_grunState_succ_ge

end Audit
