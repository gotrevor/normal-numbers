/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SS: a stall IS a straddle — the bridge from the run to `straddleSet`

S7-SM computed `volume (straddleSet w) ≍ √w`.  This module supplies the missing half: the machine
stalls **exactly** when its image straddles, so the stall times of the run are the times at which
one explicit orbit quantity lands in `straddleSet (width)`.

`straddle_of_not_emittable`: if `t` cannot emit and its image does not touch `0`, then the left
endpoint `lo = min (t.mob 0) (t.mob 1)` satisfies

    lo ≤ 1/a  <  lo + width t      with   a = ⌊1/lo⌋ ≥ 1,

i.e. `lo ∈ straddleSet (width t)`.  The proof is the contrapositive of `exists_emit`: `a = ⌊1/lo⌋`
is the *only* candidate digit, because `1/(a+1) < lo ≤ 1/a`; if the image also ended below `1/a` it
would lie in `I_a` and the emission would fire.

`stall_straddles` transports this to the run: at any stall time (`runWord Φ x n = []`) the
post-read state `runState Φ x n · readAt x n` is non-emittable, so its left endpoint straddles.

## What remains for the `MeanSlack` verdict

With S7-SM this says: a stall at time `n` forces one orbit point into a set of measure `≍ √wₙ`.
Turning that into a *frequency* is a CF-normality statement about a finite union of intervals —
`straddleSet w` restricted to depth `≤ K` is exactly `K` intervals — and that is the next step.

## Guard rule

Content locator: at `width t = 0` the conclusion is `lo ≤ 1/a < lo`, impossible — so the lemma
silently contains "a non-emittable state has positive width", which is true because `t.det ≠ 0`.
Degenerate case: `lo = 0` is excluded by hypothesis and is the genuine boundary case (the image
touching `0` means every digit is a candidate, and the machine really can stall forever there).
-/
import NormalNumbers.VandeheyS7StraddleMass
import NormalNumbers.VandeheyS7Run
import NormalNumbers.VandeheyS7Box

namespace NormalNumbers.VandeheyS7

open Set

namespace MapState

/-- **A stall is a straddle.**  A non-emittable state whose image avoids `0` has its left endpoint
in `straddleSet` at the scale of its own width. -/
theorem straddle_of_not_emittable {t : MapState} (hne : ¬ Emittable t)
    (hpos : 0 < min (t.mob 0) (t.mob 1)) :
    min (t.mob 0) (t.mob 1) ∈ straddleSet t.width := by
  set lo : ℝ := min (t.mob 0) (t.mob 1) with hlo
  set hi : ℝ := max (t.mob 0) (t.mob 1) with hhi
  have h0 : t.mob 0 ∈ Icc (0:ℝ) 1 := t.mapsTo ⟨le_refl 0, zero_le_one⟩
  have h1 : t.mob 1 ∈ Icc (0:ℝ) 1 := t.mapsTo ⟨zero_le_one, le_refl 1⟩
  have hlo1 : lo ≤ 1 := le_trans (min_le_left _ _) h0.2
  have hwidth : t.width = hi - lo := by
    rw [width, hhi, hlo, max_sub_min_eq_abs, abs_sub_comm]
  -- the only candidate digit
  set a : ℕ := ⌊1 / lo⌋₊ with ha
  have hinv1 : (1:ℝ) ≤ 1 / lo := by
    rw [le_div_iff₀ hpos]; linarith
  have ha1 : 1 ≤ a := Nat.le_floor (by exact_mod_cast hinv1)
  have hapos : (0:ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hfl : (a : ℝ) ≤ 1 / lo := Nat.floor_le (by positivity)
  have hfu : 1 / lo < (a : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (1 / lo)
    rwa [ha]
  have hleft : lo ≤ 1 / (a : ℝ) := by
    have h := (le_div_iff₀ hpos).mp hfl
    rw [le_div_iff₀ hapos]
    nlinarith [h]
  have hright : 1 / ((a : ℝ) + 1) < lo := by
    have h := (div_lt_iff₀ hpos).mp hfu
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < (a:ℝ) + 1)]
    nlinarith [h]
  refine ⟨a, ha1, hleft, ?_⟩
  rw [hwidth]
  by_contra hcon
  push_neg at hcon
  -- both endpoints lie in `[1/(a+1), 1/a]`, so the emission fires
  have hhi_le : hi ≤ 1 / (a : ℝ) := by linarith
  have hb0 : 1 / ((a:ℝ) + 1) ≤ t.mob 0 := le_trans hright.le (min_le_left _ _)
  have hb1 : 1 / ((a:ℝ) + 1) ≤ t.mob 1 := le_trans hright.le (min_le_right _ _)
  have hc0 : t.mob 0 ≤ 1 / (a : ℝ) := le_trans (le_max_left _ _) hhi_le
  have hc1 : t.mob 1 ≤ 1 / (a : ℝ) := le_trans (le_max_right _ _) hhi_le
  have haR : (1:ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  obtain ⟨u, hu⟩ := exists_emit t haR hb0 hc0 hb1 hc1
  exact hne ⟨a, u, (emitStep_iff ha1).2 hu⟩

/-- **The run form.**  At a stall time the post-read state straddles. -/
theorem stall_straddles (Φ : MapState) (x : ℝ) {n : ℕ} (hstall : runWord Φ x n = [])
    (hpos : 0 < min (((runState Φ x n).comp (readAt x n)).mob 0)
      (((runState Φ x n).comp (readAt x n)).mob 1)) :
    min (((runState Φ x n).comp (readAt x n)).mob 0)
        (((runState Φ x n).comp (readAt x n)).mob 1)
      ∈ straddleSet ((runState Φ x n).comp (readAt x n)).width := by
  refine straddle_of_not_emittable ?_ hpos
  intro hem
  obtain ⟨b, -, hb⟩ := step_emitStep hem
  rw [runWord, hb] at hstall
  exact (List.cons_ne_nil b []) hstall

/-- **The converse: a strict straddle blocks the emission.**  If some `1/k` lies strictly inside
the image then no digit can be emitted — because between `1/(b+1)` and `1/b` there is no other
reciprocal at all.  With `straddle_of_not_emittable` this characterises the stall times up to the
boundary case `lo = 1/(b+1)`. -/
theorem not_emittable_of_strict_straddle {t : MapState} {k : ℕ} (hk : 1 ≤ k)
    (hlo : min (t.mob 0) (t.mob 1) < 1 / (k : ℝ))
    (hhi : 1 / (k : ℝ) < max (t.mob 0) (t.mob 1)) :
    ¬ Emittable t := by
  rintro ⟨b, u, hem⟩
  have hb : 1 ≤ b := hem.1
  have hbR : (1:ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0:ℝ) < (b : ℝ) := by linarith
  have heq := (emitStep_iff hb).1 hem
  -- the image of `t` lies in the cylinder `I_b`
  have hmob : ∀ z : ℝ, z ∈ Set.Icc (0:ℝ) 1 →
      1 / ((b : ℝ) + 1) ≤ t.mob z ∧ t.mob z ≤ 1 / (b : ℝ) := by
    intro z hz
    have hcomp : t.mob z = (readMap (b : ℝ) hbR).mob (u.mob z) := by
      rw [← heq, mob_comp _ _ hz]
    have huz : u.mob z ∈ Set.Icc (0:ℝ) 1 := u.mapsTo hz
    rw [hcomp, readMap_mob]
    exact ⟨one_div_le_one_div_of_le (by linarith [huz.1]) (by linarith [huz.2]),
      one_div_le_one_div_of_le hbpos (by linarith [huz.1])⟩
  have h0 := hmob 0 ⟨le_refl 0, zero_le_one⟩
  have h1 := hmob 1 ⟨zero_le_one, le_refl 1⟩
  have hlo' : 1 / ((b : ℝ) + 1) ≤ min (t.mob 0) (t.mob 1) := le_min h0.1 h1.1
  have hhi' : max (t.mob 0) (t.mob 1) ≤ 1 / (b : ℝ) := max_le h0.2 h1.2
  -- so `1/(b+1) < 1/k < 1/b`, i.e. `b < k < b + 1`
  have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have einv : ∀ r q : ℝ, 0 < r → 0 < q → 1 / r < 1 / q → q < r := by
    intro r q hr hq h
    by_contra hc
    push_neg at hc
    exact absurd (one_div_le_one_div_of_le hr hc) (not_le.mpr h)
  have hgt : (b : ℝ) < (k : ℝ) := einv _ _ hkpos hbpos (by linarith)
  have hlt : (k : ℝ) < (b : ℝ) + 1 :=
    einv _ _ (by linarith) hkpos (by linarith)
  have hb' : b < k := by exact_mod_cast hgt
  have hk' : k < b + 1 := by exact_mod_cast hlt
  omega


end MapState

section Audit

#print axioms MapState.straddle_of_not_emittable
#print axioms MapState.stall_straddles
#print axioms MapState.not_emittable_of_strict_straddle

end Audit

end NormalNumbers.VandeheyS7
