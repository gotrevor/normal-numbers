/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-CX: what the crux SAYS — the block sets are the output's own digits

The §7 front is `BlockAverageBound` for the sets `mapBlockSet (runState Φ x n) w j`.  This module
proves, in the kernel, what membership in those sets means:

    Gⁿx ∈ mapBlockSet (runState Φ x n) w j   ⟺   G^(N n + j) y ∈ I_w ,      y = Φ.mob x ,

with `N = runClock` (`mem_mapBlockSet_iff`).  The proof is `runValue_spec` (S7-RO): the state
applied to the input orbit point IS the output orbit point at clock time `N n`.

## Why record this

Two reasons, both about honesty of the audit surface.

1. **It shows the crux is a faithful restatement of the goal, not a weakening.**  The hypothesis
   `BlockAverageBound` is literally an upper bound on the frequency with which the OUTPUT's digit
   string reads `w` — i.e. the conclusion `IsCFNormal (Φ.mob x)` in upper-bound, clock-reparametrised
   form.  Any route that claims to prove it must produce real information about `y`; there is no
   soft reformulation left to find.  Directive fact (α) is the same statement seen from the input
   side, and S7-CN's rigidity is the same statement seen on the state.
2. **It gives the front a state-free reading.**  Once `ClockLinear` converts the `n`-average into a
   `k`-average (S7-CP, a theorem), the front's content is exactly
   `limsup_k (1/k)·#{i < k : G^i y ∈ I_w} ≤ C·γ(I_w)` — so future work may be phrased about `y`
   directly, with the state appearing only through the clock.

## Guard rule

Content locator: at `j = 0` and `w = [a]` the statement is "the state's value has first digit `a`",
which is `cfDigit_mob_eq_emitDigit` — so all the content is in the clock bookkeeping.  Degenerate
case: `w = []` makes `cfCylinder w` all of `(0,1)`, and both sides reduce to `Gⁿx ∈ (0,1)`.
-/
import NormalNumbers.VandeheyS7RunPin

namespace NormalNumbers.VandeheyS7

open Set Filter NormalNumbers

namespace MapState

/-- **The crux, decoded.**  The block set at input time `n` is the event that the OUTPUT orbit,
`j` steps after the clock time `N n`, lies in the cylinder `I_w`. -/
theorem mem_mapBlockSet_iff (Φ : MapState) {x : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : Φ.mob x ∈ Set.Ioo (0:ℝ) 1) (hyirr : Irrational (Φ.mob x)) (n j : ℕ) (w : List ℕ) :
    gaussMap^[n] x ∈ mapBlockSet (runState Φ x n) w j
      ↔ gaussMap^[runClock Φ x n + j] (Φ.mob x) ∈ cfCylinder w := by
  obtain ⟨hmem, -, hval⟩ := runValue_spec Φ hx hy hyirr n
  have hsplit : gaussMap^[runClock Φ x n + j] (Φ.mob x)
      = gaussMap^[j] (runValue Φ x n) := by
    rw [Nat.add_comm, Function.iterate_add_apply, hval]
  constructor
  · rintro ⟨hpre, -⟩
    obtain ⟨hcyl, -⟩ := hpre
    rw [hsplit]
    exact hcyl
  · intro h
    refine ⟨⟨?_, ?_⟩, hx n⟩
    · rw [hsplit] at h; exact h
    · exact hmem

end MapState

section Audit

#print axioms MapState.mem_mapBlockSet_iff

end Audit

end NormalNumbers.VandeheyS7
