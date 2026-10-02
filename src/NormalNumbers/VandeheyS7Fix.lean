/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Clock2

/-!
# S7-F: the width floor is a fixed-point problem, and the coefficient is the whole of it

Lap 70 reduced `ImageTight` to `StateClock`, whose only non-bookkeeping content is the **width
floor**: the states must have image width `≥ η`.  This module prices that floor honestly.

## Where the floor comes from, and why it loops

A reduced state's image contains a reciprocal `1/k`; `width_ge_of_mem_of_far` (lap 49) turns "the
current output point is `η`-far from that reciprocal" into "the image is `η` wide".  So the floor
fails exactly at the times the image orbit visits `nearInv η`.  And lap 48's
`blockCount_nearInv_le` bounds that visit count **unconditionally** — but by

    freq(nearInv (1/(2(T+1)³)))  ≤  3 · freq(cellSet [] (T+1))  +  o(1) ,

i.e. by three times the very tail-cell frequency `ImageTight` is about.  The chain
`StateClock → AnchoredPullback → ImageTight` therefore closes into a loop

    x  ≤  b  +  λ x ,        x = tail frequency,  λ = 3 (the multiplicity of lap 48's
                             "a large digit within three steps"),  b = the anchored bound `2K/(Tη)`.

## What this module proves

* `le_div_of_self_le_add` — if `0 ≤ λ < 1`, the loop **closes**: `x ≤ b/(1−λ)`.  So the entire
  remaining obligation is the size of the coefficient, not the shape of the argument.
* `no_bound_of_one_le_coeff` — if `1 ≤ λ` it does not close, and not for a fixable reason: for
  every bound `M` there is an `x > M` satisfying the inequality.  A witness, not a failure to find
  a proof.

## The consequence for the route

The width floor cannot be bought from lap 48's three-step argument as it stands (`λ = 3`).  Two
attacks remain, and they are the honest lap-72 choices:

1. **Shrink `λ`.**  The `3` is the multiplicity of the map "bad time `↦` the time within three
   steps that carries the large digit".  If bad times can be charged *injectively* to tail-cell
   times, `λ = 1`, which is still not `< 1` — so this attack must also gain a factor from the
   *scale separation* (the floor `η` and the threshold `T` are free), i.e. it needs a rate:
   exactly lap 49's `TailRate`.
2. **Find a width floor not routed through the image.**  The state's width is an arithmetic
   quantity — for the additive instance, `1/(‖·‖² )` of the `ℤ[φ]` denominator entry
   (`VandeheyS7Lattice`) — so a lower bound on it is a *height* statement about `SL₂(ℤ[φ])` points,
   not an ergodic one.  This is directive fact (γ) again, and it is the attack that does not loop.

## Guard rule

Content locator: `no_bound_of_one_le_coeff` at `λ = 1` already fails, so the obstruction is not an
artefact of the specific `3`.  Degenerate case: `b = 0` with `λ < 1` forces `x ≤ 0`, i.e. a perfect
floor would give a perfect tail bound — the loop is genuinely a contraction statement.
-/

namespace NormalNumbers.VandeheyS7

/-- **The loop closes when the coefficient contracts.** -/
theorem le_div_of_self_le_add {x b lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hb : 0 ≤ b) (h : x ≤ b + lam * x) : x ≤ b / (1 - lam) := by
  have h1 : (0:ℝ) < 1 - lam := by linarith
  rw [le_div_iff₀ h1]
  nlinarith [h]

/-- **And it does not close otherwise.**  For `λ ≥ 1` the inequality bounds nothing: a witness
above every proposed bound. -/
theorem no_bound_of_one_le_coeff {b lam : ℝ} (hlam : 1 ≤ lam) (hb : 0 ≤ b) (M : ℝ) :
    ∃ x : ℝ, M < x ∧ x ≤ b + lam * x := by
  refine ⟨max (M + 1) 0, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  have h0 : 0 ≤ max (M + 1) 0 := le_max_right _ _
  nlinarith [h0, hlam, hb]

/-- The tail-cell bootstrap, as it currently stands: coefficient `3`, hence no bound. -/
theorem tailBootstrap_coeff_three_gives_no_bound {b : ℝ} (hb : 0 ≤ b) (M : ℝ) :
    ∃ x : ℝ, M < x ∧ x ≤ b + 3 * x :=
  no_bound_of_one_le_coeff (by norm_num) hb M

section Audit

#print axioms le_div_of_self_le_add
#print axioms no_bound_of_one_le_coeff
#print axioms tailBootstrap_coeff_three_gives_no_bound

end Audit

end NormalNumbers.VandeheyS7
