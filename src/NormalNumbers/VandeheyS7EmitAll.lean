/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-EA: the transducer cannot stall forever

The three previous modules assemble.  A state that has read a long input word without emitting is
`s ∘ cylMap w` with `|w|` large; S7-CM makes its width at most `lipConst s · (1/4)^(|w|/2)`, and
S7-EE2 turns "narrower than the orbit point's distance to its two cylinder walls" into an emission.
The orbit point is irrational, so that distance is **positive** — this is the whole use of
irrationality, and directive fact (β) is exactly the statement that it would be zero for a rational
`1/k`.

* `digit_unique` — the open cylinders `(1/(a+1), 1/a)` are pairwise disjoint, so the digit of `p`
  is unique and the narrowness hypothesis of `exists_emit_of_width` has only one instance to meet.
* `exists_emit_of_width_lt` — the single-`ε` form: `width < min(p − 1/(a+1), 1/a − p)` emits.
* `exists_emit_eventually` — **S7-EA**: along any sequence of input words of unbounded length whose
  composite state always carries the same irrational value `p`, all but finitely many of the states
  emit.

This is `StatePin.clockUnbounded` in its dynamical form: the clock of the transducer is unbounded
because the state cannot stay un-emittable, and the reason is that the image orbit point is
irrational, not that any width floor holds.
-/
import NormalNumbers.VandeheyS7CylMap

namespace NormalNumbers.VandeheyS7

open Set Filter

/-- The open cylinders are pairwise disjoint: the digit of `p` is unique. -/
theorem digit_unique {p : ℝ} {a a' : ℕ} (ha : 1 ≤ a) (ha' : 1 ≤ a')
    (h : p ∈ Ioo (1 / ((a : ℝ) + 1)) (1 / (a : ℝ)))
    (h' : p ∈ Ioo (1 / ((a' : ℝ) + 1)) (1 / (a' : ℝ))) : a = a' := by
  by_contra hne
  have ha0 : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha0' : (0:ℝ) < (a' : ℝ) := by exact_mod_cast ha'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hle : (a : ℝ) + 1 ≤ (a' : ℝ) := by exact_mod_cast hlt
    have h1 : 1 / (a' : ℝ) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) hle
    linarith [h.1, h'.2]
  · have hle : (a' : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hlt
    have h1 : 1 / (a : ℝ) ≤ 1 / ((a' : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) hle
    linarith [h'.1, h.2]

namespace MapState

/-- **The single-`ε` emission criterion.** -/
theorem exists_emit_of_width_lt (t : MapState) {z₀ : ℝ} (hz₀ : z₀ ∈ Icc (0:ℝ) 1)
    (hp : t.mob z₀ ∈ Ioo (0:ℝ) 1) (hirr : Irrational (t.mob z₀))
    {a : ℕ} (ha : 1 ≤ a) (hmem : t.mob z₀ ∈ Ioo (1 / ((a : ℝ) + 1)) (1 / (a : ℝ)))
    (hw : t.width < min (t.mob z₀ - 1 / ((a : ℝ) + 1)) (1 / (a : ℝ) - t.mob z₀)) :
    ∃ (b : ℕ) (hb : 1 ≤ b) (u : MapState),
      (readMap (b : ℝ) (by exact_mod_cast hb)).comp u = t := by
  refine t.exists_emit_of_width hz₀ hp hirr ?_
  intro a' ha' hmem'
  rwa [digit_unique ha ha' hmem hmem'] at hw

/-- **S7-EA.**  A transducer reading longer and longer input words, whose composite state keeps
carrying the same irrational value, emits for all but finitely many of them. -/
theorem exists_emit_eventually (s : MapState) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (hirr : Irrational p) {v : ℕ → List ℕ} (hv : ∀ n, ∀ e ∈ v n, 1 ≤ e)
    (hlen : Tendsto (fun n => (v n).length) atTop atTop)
    {z : ℕ → ℝ} (hz : ∀ n, z n ∈ Icc (0:ℝ) 1)
    (hval : ∀ n, (s.comp (cylMap (v n))).mob (z n) = p) :
    ∀ᶠ n in atTop, ∃ (b : ℕ) (hb : 1 ≤ b) (u : MapState),
      (readMap (b : ℝ) (by exact_mod_cast hb)).comp u = s.comp (cylMap (v n)) := by
  obtain ⟨a, ha, hmem⟩ := exists_digit_of_irrational hp hirr
  set ε : ℝ := min (p - 1 / ((a : ℝ) + 1)) (1 / (a : ℝ) - p) with hε
  have hεpos : 0 < ε := lt_min (by linarith [hmem.1]) (by linarith [hmem.2])
  -- the widths tend to zero
  have hwtend : Tendsto (fun n => (s.comp (cylMap (v n))).width) atTop (nhds 0) := by
    refine squeeze_zero (fun n => (s.comp (cylMap (v n))).width_nonneg)
      (fun n => width_comp_le' s (cylMap (v n))) ?_
    have := tendsto_width_cylMap hv hlen
    simpa using this.const_mul s.lipConst
  filter_upwards [hwtend.eventually (eventually_lt_nhds hεpos)] with n hn
  have hz₀ := hz n
  have hvalue := hval n
  refine exists_emit_of_width_lt (s.comp (cylMap (v n))) hz₀ (by rw [hvalue]; exact hp)
    (by rw [hvalue]; exact hirr) ha (by rw [hvalue]; exact hmem) ?_
  rw [hvalue]
  exact hn

end MapState

section Audit

#print axioms digit_unique
#print axioms MapState.exists_emit_of_width_lt
#print axioms MapState.exists_emit_eventually

end Audit

end NormalNumbers.VandeheyS7
