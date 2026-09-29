/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-LD: the LAG, and the exact two-sided width ledger it rides on

`MeanSlack` — `Σ_{m<q} slack m ≤ A·q`, with `slack m = log d_{m+2} − log √(|det Φ|/6)` — is one
of the two remaining inputs of the §7 front.  This module builds the elementary ledger it needs,
and names the combinatorial object that actually governs it.

## The lag

Every input step reads exactly one digit and emits **at most one** (`runWord_length_le_one`), so

    lag Φ x n := n − runClock Φ x n

is **monotone non-decreasing** (`lag_mono`) and counts the stalls: `lag n` is the number of
`k < n` with `runWord Φ x k = []` (`lag_eq_card_stalls`).  That monotonicity is the structural
fact the slack walk inherits: the machine can never repay a stall, because it has no spare
emission slot to repay it with.

## The two-sided ledger

`width_eq` gives `width s = |det s| / (d·(c+d))`, and both factors move monotonically:

* **reading never widens, and divides the width by at least the digit**
  (`width_comp_readMap_le`, `width_comp_readMap_le_div`): with `r = readMap a`,
  `(s·r).d = s.c + a·s.d` and `(s·r).c = s.d`, so `d·(c+d)` is multiplied by at least `a`, while
  `|det|` is unchanged (`det_readMap = −1`).
* **emitting never narrows, and multiplies the width by at most `(b+1)²`**
  (`width_le_width_of_emitStep`, `width_emitStep_le`): an `EmitStep t b u` has `u.d = t.b ≤ t.d`
  and `u.c + u.d = t.a + t.b ≤ t.c + t.d`, and conversely `t.d ≤ (b+1)·u.d`,
  `t.c + t.d ≤ (b+1)·(u.c + u.d)` from `u.b ≤ u.d` and `u.a + u.b ≤ u.c + u.d`.

So along the run `log (1/width)` is a walk with increments `≥ log a` on a read and
`≥ −2 log (b+1)` on an emit, reflected above by `width ≤ 1`.  This is the scalar walk `MeanSlack`
is a statement about (`slack ≍ ½ log (1/width)` via `width_eq` and the `denRatio` band).

## Why this is the right next object

`MeanSlack` asks for `(1/q)·Σ_{m<q} slack m = O(1)`, i.e. for the walk to have a **bounded mean**,
not merely to be linear-clock (`ClockLinear`, already a consequence).  Because `lag` is monotone,
a run that stalls infinitely often has `lag n → ∞`, and the walk it drives cannot have a bounded
mean unless the stalls are summably rare.  So the honest reading of `MeanSlack` is:

    MeanSlack  ⟺  the run's stalls are rare enough that the accumulated lag stays `O(1)` on
                   average — a statement about how often `runState`'s image STRADDLES a
                   cylinder endpoint.

That is the arithmetic of `Φ` (directive fact (α)'s second escape hatch), and for `Φ = idMap`
it is trivially true (no stall ever), which is the content locator below.

## Guard rule

Content locator: `lag_idMap_eq_zero`-style triviality is not available without the run's emission
analysis, so the locator used here is `width_comp_readMap_le_div` at `a = 1`, where it degenerates
to `width_comp_readMap_le` — all the quantitative content is in `a ≥ 2`.  Degenerate cases:
`lag 0 = 0`; and `width_emitStep_le` at `b = 1` gives the factor `4`, never `1`, because a state
can sit at either end of `I₁`.
-/
import NormalNumbers.VandeheyS7Box
import NormalNumbers.VandeheyS7RunOrbit

namespace NormalNumbers.VandeheyS7

open Finset

namespace MapState

variable {Φ : MapState} {x : ℝ}

/-! ## The lag -/

lemma runClock_le_self (Φ : MapState) (x : ℝ) (n : ℕ) : runClock Φ x n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [runClock_succ]
      have := runWord_length_le_one Φ x n
      omega

/-- **The lag**: input digits read minus output digits emitted. -/
noncomputable def lag (Φ : MapState) (x : ℝ) (n : ℕ) : ℕ := n - runClock Φ x n

@[simp] lemma lag_zero (Φ : MapState) (x : ℝ) : lag Φ x 0 = 0 := by simp [lag]

lemma lag_succ (Φ : MapState) (x : ℝ) (n : ℕ) :
    lag Φ x (n + 1) = lag Φ x n + (if runWord Φ x n = [] then 1 else 0) := by
  have hle := runClock_le_self Φ x n
  have hlen := runWord_length_le_one Φ x n
  rw [lag, lag, runClock_succ]
  by_cases h : runWord Φ x n = []
  · rw [if_pos h, h]; simp; omega
  · rw [if_neg h]
    have : (runWord Φ x n).length = 1 := by
      rcases Nat.lt_or_ge (runWord Φ x n).length 1 with h1 | h1
      · exact absurd (List.eq_nil_of_length_eq_zero (by omega)) h
      · omega
    rw [this]; omega

/-- **The lag is monotone.**  One read, at most one emission: a stall can never be repaid. -/
lemma lag_mono (Φ : MapState) (x : ℝ) : Monotone (lag Φ x) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [lag_succ]; omega

/-- The lag counts the stalls. -/
theorem lag_eq_card_stalls (Φ : MapState) (x : ℝ) (n : ℕ) :
    lag Φ x n = ((range n).filter (fun k => runWord Φ x k = [])).card := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [lag_succ, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases h : runWord Φ x n = []
      · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      · rw [if_neg h, if_neg h]; simp

/-! ## The read step: never widens -/

/-- **Reading divides the width by at least the digit.**  No hypothesis beyond `1 ≤ a`. -/
theorem width_comp_readMap_le_div (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).width ≤ s.width / a := by
  have hd : 0 < s.d := s.hd
  have hh : 0 < s.c + s.d := s.hcd
  have hapos : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  set r := readMap a ha with hr
  have hnd : (s.comp r).d = s.c + s.d * a := comp_readMap_d s ha
  have hnc : (s.comp r).c = s.d := comp_readMap_c s ha
  have hnh : (s.comp r).c + (s.comp r).d = s.c + s.d * (a + 1) := by rw [hnc, hnd]; ring
  have hndpos : 0 < (s.comp r).d := (s.comp r).hd
  have hnhpos : 0 < (s.comp r).c + (s.comp r).d := (s.comp r).hcd
  have hdet : |(s.comp r).det| = |s.det| := by
    rw [det_comp, hr, det_readMap, abs_mul]; simp
  -- the product of the two positive coordinates grows by at least `a`
  have hprod : a * (s.d * (s.c + s.d)) ≤ (s.comp r).d * ((s.comp r).c + (s.comp r).d) := by
    rw [hnc, hnd]
    nlinarith [hd, hh, hapos, ha, mul_nonneg (sub_nonneg.mpr ha) hd.le]
  rw [width_eq, width_eq, hdet, div_div]
  refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
  calc s.d * (s.c + s.d) * a = a * (s.d * (s.c + s.d)) := by ring
    _ ≤ (s.comp r).d * ((s.comp r).c + (s.comp r).d) := hprod

/-- **Reading never widens.** -/
theorem width_comp_readMap_le (s : MapState) {a : ℝ} (ha : 1 ≤ a) :
    (s.comp (readMap a ha)).width ≤ s.width := by
  refine le_trans (width_comp_readMap_le_div s ha) ?_
  have hapos : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  rw [div_le_iff₀ hapos]
  nlinarith [s.width_nonneg, ha]

/-! ## The emission step: never narrows, by a controlled factor -/

/-- **Emitting never narrows.**  `u.d = t.b ≤ t.d` and `u.c + u.d = t.a + t.b ≤ t.c + t.d`, while
the absolute determinant is unchanged. -/
theorem width_le_width_of_emitStep {t : MapState} {b : ℕ} {u : MapState}
    (h : EmitStep t b u) : t.width ≤ u.width := by
  obtain ⟨hb, h1, h2, h3, h4⟩ := h
  have hud : u.d = t.b := h2
  have huh : u.c + u.d = t.a + t.b := by rw [h1, h2]
  have hdet : |u.det| = |t.det| := by
    have hb1 : (1:ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have heq := (emitStep_iff hb).1 ⟨hb, h1, h2, h3, h4⟩
    have : t.det = (readMap (b:ℝ) hb1).det * u.det := by rw [← det_comp, heq]
    rw [this, det_readMap, abs_mul]; simp
  have hle1 : u.d ≤ t.d := by rw [hud]; exact t.hbd
  have hle2 : u.c + u.d ≤ t.c + t.d := by rw [huh]; exact t.habcd
  rw [width_eq, width_eq, hdet]
  refine div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos u.hd u.hcd) ?_
  exact mul_le_mul hle1 hle2 (le_of_lt u.hcd) t.hd.le

/-- **Emitting widens by at most `(b+1)²`.**  From `u.b ≤ u.d` and `u.a + u.b ≤ u.c + u.d`. -/
theorem width_emitStep_le {t : MapState} {b : ℕ} {u : MapState}
    (h : EmitStep t b u) : u.width ≤ ((b : ℝ) + 1) ^ 2 * t.width := by
  obtain ⟨hb, h1, h2, h3, h4⟩ := h
  have hb1 : (1:ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hdet : |u.det| = |t.det| := by
    have heq := (emitStep_iff hb).1 ⟨hb, h1, h2, h3, h4⟩
    have : t.det = (readMap (b:ℝ) hb1).det * u.det := by rw [← det_comp, heq]
    rw [this, det_readMap, abs_mul]; simp
  have hbd : t.d ≤ ((b:ℝ) + 1) * u.d := by
    rw [h4]; nlinarith [u.hbd, u.hd]
  have hbh : t.c + t.d ≤ ((b:ℝ) + 1) * (u.c + u.d) := by
    have : t.c + t.d = (u.a + u.b) + (b:ℝ) * (u.c + u.d) := by rw [h3, h4]; ring
    rw [this]; nlinarith [u.habcd, u.hcd]
  have hu : 0 < u.d * (u.c + u.d) := mul_pos u.hd u.hcd
  have ht' : 0 < t.d * (t.c + t.d) := mul_pos t.hd t.hcd
  have hprod := mul_le_mul hbd hbh t.hcd.le
    (mul_nonneg (by positivity : (0:ℝ) ≤ (b:ℝ) + 1) u.hd.le)
  have hkey : t.d * (t.c + t.d) ≤ ((b : ℝ) + 1) ^ 2 * (u.d * (u.c + u.d)) :=
    le_trans hprod (le_of_eq (by ring))
  rw [width_eq, width_eq, hdet, div_le_iff₀ hu]
  have hrw : ((b : ℝ) + 1) ^ 2 * (|t.det| / (t.d * (t.c + t.d))) * (u.d * (u.c + u.d))
      = |t.det| * (((b : ℝ) + 1) ^ 2 * (u.d * (u.c + u.d)) / (t.d * (t.c + t.d))) := by
    field_simp
  rw [hrw]
  have h1 : (1:ℝ) ≤ ((b : ℝ) + 1) ^ 2 * (u.d * (u.c + u.d)) / (t.d * (t.c + t.d)) :=
    (one_le_div ht').mpr hkey
  nlinarith [abs_nonneg t.det]

end MapState

section Audit

#print axioms MapState.lag_mono
#print axioms MapState.lag_eq_card_stalls
#print axioms MapState.width_comp_readMap_le_div
#print axioms MapState.width_le_width_of_emitStep
#print axioms MapState.width_emitStep_le

end Audit

end NormalNumbers.VandeheyS7
