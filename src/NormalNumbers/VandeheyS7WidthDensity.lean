/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WQ: the crux and the width debt are incompatible — a dichotomy

Route A's architecture (S7-BF/S7-RV/S7-IM) consumes two statements about a run:

* `BlockForgetRun w` — the crux, a Cesàro comparison summed over the **wide** times
  (`¬ width < η`);
* `WidthAfford Φ x` — for every tolerance `δ` some width floor `η` makes the **narrow** times have
  frequency at most `δ`.

This module records, in the kernel, that the two pull in opposite directions: if the wide times of
a run have density zero (for every floor `η`), then

* `crux_sum_le_of_wide_sparse` — the crux's sum for that run is automatically `≤ ε·p`: the
  hypothesis has NO content on that run; and
* `not_widthAfford_of_wide_sparse` — `WidthAfford Φ x` is FALSE for that run.

So on a run with sparse wide times route A's chain cannot be applied at all (its second hypothesis
fails), while its first hypothesis is vacuously true there.  Non-vacuity of the crux and
satisfiability of the width debt are the same requirement: a positive density of wide times.

## Why this matters (the lap-91 probe)

An exact-arithmetic simulation of the transducer for `Φ : z ↦ z/φ` (entries in `ℤ[φ]`, exact
`ℚ(√5)` sign tests for the emission test; the emitted word was verified digit-for-digit against the
true continued fraction of `x/φ` to 120 digits) shows:

* the clock deficit **stops**: `7` stalls in the first `18000` reads, so `runClock p = p − 7`
  eventually — the crux at `[]` (S7-CO) is measured GREEN, and emphatically;
* `log (1/width)` of the run's state behaves like a **mean-zero random walk of size ≍ √n**
  (hundreds of nats at `n ≈ 10⁴`, non-monotone), not like a bounded sequence.  For the rational map
  `z ↦ (z+1)/3` — Vandehey's Thm 1.1 case, where the state set is finite — it stays bounded.

A null-recurrent walk spends density zero of its time in any bounded set, so the wide times of the
golden run have density zero: exactly the hypothesis of this module.  That refutes the SHAPE of
both scalar debts (`WidthAfford`, and `MeanSlack`'s `Σ slack ≤ A·q`, since `slack ≍ √m` sums to
`≍ q^{3/2}`), and it says the reason the golden transducer keeps perfect time is not that its
states are wide but that they are NARROW — a narrow image cannot straddle a cylinder boundary
often, and straddling is what a stall is (S7-SS).

## Guard rule

**Content locator.**  Both proofs are counting; the content is the statement.  Nothing here claims
the density hypothesis holds for a particular `(Φ, x)` — that is the probe's reading, recorded as
such, and the theorems are stated as implications from it.

**Degenerate cases.**  `p = 0` is handled by the eventually-filters.  `δ ≥ 1` makes `WidthAfford`
trivially satisfiable, so `not_widthAfford_of_wide_sparse` uses `δ = 1/2`.
-/
import NormalNumbers.VandeheyS7BlockForget

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- The wide times of a run, at floor `η`, have density zero. -/
def WideSparse (Φ : MapState) (x : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    Tendsto (fun p => (((range p).filter fun m => ¬ (runState Φ x m).width < η).card : ℝ)
      / (p : ℝ)) atTop (nhds 0)

/-- **The crux is vacuous on a run with sparse wide times.**  Its sum is `≤ ε·p` eventually, for
every block length and every word, with no comparison of block averages used at all. -/
theorem crux_sum_le_of_wide_sparse {Φ : MapState} {x : ℝ} (hsp : WideSparse Φ x)
    {η : ℝ} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) (w : List ℕ) {T : ℕ} (hT : 0 < T) :
    ∀ᶠ p : ℕ in atTop,
      ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
        |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
          - blockAvg refState T w (gaussMap^[m] x)| ≤ ε * (p : ℝ) := by
  classical
  have hev := (hsp η hη).eventually (eventually_lt_nhds (show (0:ℝ) < ε / 2 by linarith))
  filter_upwards [hev, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set c : ℝ := (((range p).filter fun m => ¬ (runState Φ x m).width < η).card : ℝ) with hc
  have hcard : c ≤ (ε / 2) * (p : ℝ) := by
    rw [hc] at hp ⊢
    rw [div_lt_iff₀ hpR] at hp
    linarith
  have hterm : ∀ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
      |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
        - blockAvg refState T w (gaussMap^[m] x)| ≤ 1 := by
    intro m _
    have h0 := blockAvg_nonneg (runState Φ x m) T w (gaussMap^[m] x)
    have h1 := blockAvg_le_one (runState Φ x m) hT w (gaussMap^[m] x)
    have h0' := blockAvg_nonneg refState T w (gaussMap^[m] x)
    have h1' := blockAvg_le_one refState hT w (gaussMap^[m] x)
    rw [abs_le]
    constructor <;> linarith
  calc ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
        |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
          - blockAvg refState T w (gaussMap^[m] x)|
      ≤ ∑ _m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η), (1:ℝ) :=
        Finset.sum_le_sum hterm
    _ = c := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
    _ ≤ (ε / 2) * (p : ℝ) := hcard
    _ ≤ ε * (p : ℝ) := by nlinarith

/-- **The width debt fails on a run with sparse wide times.**  At `δ = 1/2` no floor works: the
narrow times carry frequency tending to `1`. -/
theorem not_widthAfford_of_wide_sparse {Φ : MapState} {x : ℝ} (hsp : WideSparse Φ x) :
    ¬ WidthAfford Φ x := by
  classical
  intro hwa
  obtain ⟨η, hη, -, hbad⟩ := hwa (1/2) (by norm_num)
  -- the narrow and wide times partition `range p`
  have hsplit : ∀ p : ℕ,
      (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ)
        + (((range p).filter fun m => ¬ (runState Φ x m).width < η).card : ℝ) = (p : ℝ) := by
    intro p
    have := Finset.card_filter_add_card_filter_not
      (s := range p) (p := fun m => (runState Φ x m).width < η)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hev := (hsp η hη).eventually (eventually_lt_nhds (show (0:ℝ) < 1/4 by norm_num))
  obtain ⟨p, hp0, hpbad, hpsp⟩ : ∃ p : ℕ, 0 < p ∧
      (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ) ≤ (1/2) * p ∧
      (((range p).filter fun m => ¬ (runState Φ x m).width < η).card : ℝ) / (p : ℝ) < 1/4 := by
    obtain ⟨p, hp⟩ := ((hbad.and hev).and (eventually_gt_atTop 0)).exists
    exact ⟨p, hp.2, hp.1.1, hp.1.2⟩
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  rw [div_lt_iff₀ hpR] at hpsp
  have := hsplit p
  linarith

end MapState

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.MapState.crux_sum_le_of_wide_sparse
#print axioms NormalNumbers.VandeheyS7.MapState.not_widthAfford_of_wide_sparse

end Audit
