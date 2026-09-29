/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Branch

/-!
# The burst penalty is bounded by a CONSTANT, not by the burst length

`VandeheyS7Branch` reduced the window lemma to what emission does: reading lands the state in
`c ≤ d` for free (distortion `≤ 2`), emission swaps the rows, and the question is whether the
swapped ratio stays bounded.  The obvious estimate loses a factor per emitted digit, so a burst
of `k` emissions with no intervening read would cost `2^k` — and Vandehey's Lemma 2.2, which
bounded bursts, was measured NOT to port (`burst ≤ C + log(1+a)/Lévy`, unbounded, tracking
`0.843·ln a`).  That is the shape of the problem this file dissolves.

## The exact identity

A burst of `k` emissions is a single left-multiplication by `B⁻¹` where `B = A_{e₁}⋯A_{e_k}` is
the emitted word's matrix, whose columns are the continuants `(p_{k−1}, q_{k−1})` and
`(p_k, q_k)`.  The post-burst denominator row is `(P·c − Q·a, P·d − Q·b)` with
`(P, Q) = (p_{k−1}, q_{k−1})`, and then (`distortion_pullback`)

    distortion_after  =  distortion_before · (β − M 1) / (β − M 0),     β := P / Q ,

**exactly**, for any `P, Q` at all.  So the entire burst costs one factor: the ratio of the
distances from the two image endpoints to the convergent `β = p_{k−1}/q_{k−1}`.

## Why that factor is at most 2, whatever the burst length

The burst emits `e₁, …, e_k`, so the image interval `M([0,1])` lies inside the cylinder
`C = [e₁, …, e_k]`, whose endpoints are `p_k/q_k` and `(p_k + p_{k−1})/(q_k + q_{k−1})`.  The
convergent `β` lies outside `C`, and its distances to the two endpoints of `C` are

    far  = |β − p_k/q_k|                       = 1 / (q_{k−1} q_k) ,
    near = |β − (p_k+p_{k−1})/(q_k+q_{k−1})|   = 1 / (q_{k−1} (q_k + q_{k−1})) ,

so `far / near = (q_k + q_{k−1}) / q_k ≤ 2`, because `q_{k−1} ≤ q_k` for continuants of digits
`≥ 1`.  Both image endpoints lie in `C`, so their distances to `β` are between `near` and `far`,
and the penalty ratio is therefore in `[1/2, 2]` — **uniformly in `k`** (`burst_ratio_le`).

**This is the replacement for the lost Lemma 2.2.**  It does not bound the burst length at all;
it observes that the whole burst is one pullback, whose cost is controlled by the geometry of the
cylinder the burst is reading, not by how many digits that cylinder specifies.  Combined with the
free bound `distortion ≤ 2` after any read, it gives a window bound of `4` along the run.

## What is still owed

The continuant facts `far / near = (q_k + q_{k−1})/q_k` and `q_{k−1} ≤ q_k`, and the bookkeeping
that the emitted word's matrix really is the continuant matrix.  Those are standard and
self-contained; `burst_ratio_le` is stated so that they plug straight in as the hypothesis
`hfar : v − β ≤ 2 * (u − β)`.  This is the next node.

## Guard rule

Content locator: `distortion_pullback` at `P = 1, Q = 0` is the identity pullback and the factor
is `1`.  Degenerate case: the identity is an equality with no hypotheses beyond nonvanishing of
the new denominator, so nothing is hidden in it; `burst_ratio_le` is the only inequality.
-/

namespace NormalNumbers.VandeheyS7

namespace MobState

/-- **The pullback identity.**  Left-multiplying a state by the inverse of a matrix with
first column `(P, Q)` replaces the denominator row `(c, d)` by `(P·c − Q·a, P·d − Q·b)`, and the
distortion is multiplied by the ratio of the distances from the image endpoints to `β = P/Q`.
Exact; `P` and `Q` are arbitrary. -/
theorem distortion_pullback (s : MobState) (P Q : ℝ) (hQ : Q ≠ 0)
    (h0 : P * s.d - Q * s.b ≠ 0) (h1 : P * (s.c + s.d) - Q * (s.a + s.b) ≠ 0) :
    (P * (s.c + s.d) - Q * (s.a + s.b)) / (P * s.d - Q * s.b)
      = s.distortion * ((P / Q - s.mob 1) / (P / Q - s.mob 0)) := by
  have hd : s.d ≠ 0 := s.hd.ne'
  have hcd : s.c + s.d ≠ 0 := by
    have : 0 < s.c + s.d := by linarith [s.hc, s.hd]
    exact this.ne'
  have hm0 : s.mob 0 = s.b / s.d := by simp [mob]
  have hm1 : s.mob 1 = (s.a + s.b) / (s.c + s.d) := by
    simp [mob]
  rw [hm0, hm1, distortion]
  field_simp

/-- Content locator: the trivial pullback `(P, Q) = (1, 0)` is excluded by `hQ`, so here is the
honest degenerate check — with `Q = 0` the left side is literally the distortion. -/
theorem distortion_pullback_zero (s : MobState) :
    ((1 : ℝ) * (s.c + s.d) - 0 * (s.a + s.b)) / ((1 : ℝ) * s.d - 0 * s.b) = s.distortion := by
  simp [distortion]

/-- **The burst penalty, bounded uniformly in the burst length.**  If the image interval
`[l, r]` sits inside `[u, v]`, `β` lies strictly to the left of all of it, and the far distance
is at most twice the near distance, then the penalty factor is at most `2`.

The hypothesis `hfar` is the continuant fact `(q_k + q_{k−1})/q_k ≤ 2`: the burst length `k` does
not appear. -/
theorem burst_ratio_le {β u v l r : ℝ} (hβ : β < u) (hul : u ≤ l) (_hlr : l ≤ r) (hrv : r ≤ v)
    (hfar : v - β ≤ 2 * (u - β)) : (r - β) / (l - β) ≤ 2 := by
  have hu0 : 0 < u - β := by linarith
  have hl0 : 0 < l - β := by linarith
  rw [div_le_iff₀ hl0]
  linarith

/-- The penalty never collapses the distortion either: it is at least `1`, needing only that the
image interval is nondegenerate and to the right of `β`.  (No `far/near` hypothesis is used —
worth recording, since it shows the whole content of the bound is on the upper side.) -/
theorem one_le_burst_ratio {β u l r : ℝ} (hβ : β < u) (hul : u ≤ l) (hlr : l ≤ r) :
    1 ≤ (r - β) / (l - β) := by
  have hl0 : 0 < l - β := by linarith
  rw [le_div_iff₀ hl0]
  linarith

/-- **The window bound, conditional on the geometric input.**  A state whose distortion is at
most `2` (which reading gives for free) and whose image endpoints sit in a cylinder whose
convergent satisfies the `far ≤ 2·near` inequality has post-burst distortion at most `4` —
regardless of how many digits the burst emitted. -/
theorem distortion_pullback_le (s : MobState) (P Q : ℝ) (hQ : Q ≠ 0)
    (h0 : P * s.d - Q * s.b ≠ 0) (h1 : P * (s.c + s.d) - Q * (s.a + s.b) ≠ 0)
    (hD : s.distortion ≤ 2) {u v : ℝ} (hβ : P / Q < u)
    (hul : u ≤ s.mob 1) (hlr : s.mob 1 ≤ s.mob 0) (hrv : s.mob 0 ≤ v)
    (hfar : v - P / Q ≤ 2 * (u - P / Q)) :
    (P * (s.c + s.d) - Q * (s.a + s.b)) / (P * s.d - Q * s.b) ≤ 4 := by
  rw [distortion_pullback s P Q hQ h0 h1]
  have hratio : (s.mob 0 - P / Q) / (s.mob 1 - P / Q) ≤ 2 :=
    burst_ratio_le hβ hul hlr hrv hfar
  have hrw : (P / Q - s.mob 1) / (P / Q - s.mob 0)
      = (s.mob 1 - P / Q) / (s.mob 0 - P / Q) := by
    rw [← neg_sub (P / Q) (s.mob 1), ← neg_sub (P / Q) (s.mob 0), neg_div_neg_eq]
  have hu0 : 0 < s.mob 1 - P / Q := by linarith
  have hv0 : 0 < s.mob 0 - P / Q := by linarith
  have hle2 : (s.mob 1 - P / Q) / (s.mob 0 - P / Q) ≤ 2 := by
    rw [div_le_iff₀ hv0]
    have : s.mob 1 ≤ s.mob 0 := hlr
    linarith
  have hpos : 0 ≤ (s.mob 1 - P / Q) / (s.mob 0 - P / Q) := le_of_lt (div_pos hu0 hv0)
  rw [hrw]
  nlinarith [s.distortion_pos]

end MobState

/-! ## The named geometric input -/

/-- **What is left of the window lemma.**  At every burst, the emitted word's convergent `β` is
far enough outside the cylinder that the far/near distance ratio is at most `2`.  This is the
continuant identity `(q_k + q_{k−1})/q_k ≤ 2` and carries no dependence on the burst length; it
is the replacement for Vandehey's Lemma 2.2, which does NOT port. -/
def ConvergentGap (β u v : ℕ → ℝ) : Prop :=
  ∀ n, β n < u n ∧ u n ≤ v n ∧ v n - β n ≤ 2 * (u n - β n)

/-- Content locator: the condition is satisfiable — a cylinder of the golden-ratio type, with
`β` at distance exactly the cylinder's own length below it, meets it with equality. -/
theorem convergentGap_const : ConvergentGap (fun _ => 0) (fun _ => 1) (fun _ => 2) :=
  fun _ => ⟨zero_lt_one, one_le_two, by norm_num⟩

section Audit

#print axioms MobState.distortion_pullback
#print axioms MobState.burst_ratio_le
#print axioms MobState.distortion_pullback_le

end Audit

end NormalNumbers.VandeheyS7
