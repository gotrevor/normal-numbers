/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-LAG: the emitter's lag, and a correction to lap 75's bridge

Lap 75 (`VandeheyS7WidthFreq`) proved unconditionally that long emitted blocks are rare — the block
lengths telescope to the clock, so `L · #{n < p : Lₙ ≥ L} ≤ N p`, Markov with no measure.  It then
bridged to the width floor through

    NarrowForcesBlock : ∀ n, width (s n) < η → L ≤ blockLength N n

i.e. "a narrow state emits a long block *at that very input time*".  **That bridge is the wrong
shape, and this module records why.**  A state too narrow to emit has its image `J` straddling a
digit boundary `1/k`; reading the next input digit shrinks `J` but need not move it off the
boundary, so the state can stay narrow — and silent — for several consecutive input times before
the burst arrives.  `NarrowForcesBlock` asks for the burst at time `n`; the geometry only delivers
it at some later time.  So lap 75's `freq_narrow_le` is a true theorem about a hypothesis that the
transducer does not satisfy in that form.

The correct bridge is **amortized**: the narrow times are the times of large *lag*, and lag is a
nonnegative quantity whose time-average is what the clock's budget controls.  Writing

    deficit s = - log (width s)      (≥ 0 exactly when width ≤ 1, i.e. the emitter is not ahead)

Markov gives `freq {n < p : T < deficit (s n)} ≤ (Σ_{n<p} deficit (s n)) / (T p)`, so the single
hypothesis `Σ_{n<p} deficit (s n) ≤ Λ p` — "**the emitter's lag is `O(1)` on average**" — yields the
directive's frequency form, `freq {n : width (s n) < η} ≤ Λ / log (1/η) → 0`.  That hypothesis is
weaker than `NarrowForcesBlock`, is the natural output of the telescoping estimate below, and does
not pretend the burst is synchronous with the narrowness.

`deficit_telescope_le` is that telescoping estimate in abstract form: if each input step moves the
deficit up by at most `ξ n` and down by at least `c` per emitted digit, then the whole clock is
bounded, `c · N p ≤ deficit (s 0) + Σ_{n<p} ξ n`.  This is simultaneously
* the **clock rate** `N p ≤ Λ p` that lap 75's `freq_longBlock_le` needs (take `ξ` bounded on
  average), and
* the reason handoff idea 3 matters: for the Raney transducer `ξ n ≍ 2 log a_{n+1}`, and CF-normality
  does not bound `(1/p) Σ log a` — so the clock rate is a genuine residual, not a freebie.
-/
import NormalNumbers.VandeheyS7WidthFreq

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

namespace MobState

/-- **The emitter's lag** at a state: `- log width`.  Nonnegative exactly when the state's image
is no wider than the unit interval, which is the emitter-not-ahead condition. -/
noncomputable def deficit (s : MobState) : ℝ := - Real.log s.width

lemma deficit_nonneg (s : MobState) (h : s.width ≤ 1) : 0 ≤ s.deficit := by
  have := s.width_pos
  simpa [deficit] using Real.log_nonpos (le_of_lt this) h

/-- Narrowness is large lag: the two descriptions of a bad time agree exactly. -/
lemma lt_width_iff_deficit (s : MobState) {η : ℝ} (hη : 0 < η) :
    s.width < η ↔ Real.log η⁻¹ < s.deficit := by
  have hw := s.width_pos
  rw [deficit, Real.log_inv, neg_lt_neg_iff]
  exact (Real.log_lt_log_iff hw hη).symm

end MobState

/-! ## Markov for the lag -/

/-- **Markov.**  A nonnegative sequence exceeds `T` on at most `(Σ)/T` of the times. -/
theorem card_gt_le_sum_div {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {T : ℝ} (_hT : 0 < T) (p : ℕ) :
    T * (((Finset.range p).filter fun n => T < f n).card : ℝ) ≤ ∑ n ∈ Finset.range p, f n := by
  set F := (Finset.range p).filter fun n => T < f n with hF
  calc T * (F.card : ℝ) = ∑ _n ∈ F, T := by rw [Finset.sum_const, mul_comm, nsmul_eq_mul]
    _ ≤ ∑ n ∈ F, f n := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact le_of_lt (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.range p, f n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro i _ _; exact hf i

/-- **S7-WF, corrected.**  The single hypothesis "the emitter's lag is `O(1)` on average" gives the
directive's frequency form of the width floor. -/
theorem freq_narrow_le_of_lag {s : ℕ → MobState} (hle : ∀ n, (s n).width ≤ 1)
    {Λ η : ℝ} {p : ℕ} (hη : 0 < η) (hη1 : η < 1) (hp : 0 < p)
    (hlag : ∑ n ∈ Finset.range p, (s n).deficit ≤ Λ * p) :
    ((((Finset.range p).filter fun n => (s n).width < η).card : ℝ)) / p
      ≤ Λ / Real.log η⁻¹ := by
  have hT : 0 < Real.log η⁻¹ := Real.log_pos (by rw [one_lt_inv_iff₀]; exact ⟨hη, hη1⟩)
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hset : ((Finset.range p).filter fun n => (s n).width < η)
      = (Finset.range p).filter fun n => Real.log η⁻¹ < (s n).deficit := by
    refine Finset.filter_congr fun n _ => ?_
    simpa using (s n).lt_width_iff_deficit hη
  rw [hset]
  have hmark := card_gt_le_sum_div (f := fun n => (s n).deficit)
    (fun n => (s n).deficit_nonneg (hle n)) hT p
  rw [div_le_div_iff₀ hpR hT]
  calc ((((Finset.range p).filter fun n => Real.log η⁻¹ < (s n).deficit).card : ℝ)) * Real.log η⁻¹
      = Real.log η⁻¹ * _ := by ring
    _ ≤ ∑ n ∈ Finset.range p, (s n).deficit := hmark
    _ ≤ Λ * p := hlag

/-- The limit form: as the floor `η` shrinks, the narrow-state frequency tends to `0`, uniformly
in `p`.  This is what the directive asked for, from the average-lag hypothesis alone. -/
theorem narrow_freq_tendsto_zero_of_lag {s : ℕ → MobState} (hle : ∀ n, (s n).width ≤ 1)
    {Λ : ℝ} (_hΛ : 0 ≤ Λ)
    (hlag : ∀ p, ∑ n ∈ Finset.range p, (s n).deficit ≤ Λ * p)
    {η : ℕ → ℝ} (hηpos : ∀ i, 0 < η i) (hη1 : ∀ i, η i < 1)
    (hηtop : Tendsto (fun i => Real.log (η i)⁻¹) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ p, 0 < p →
      ((((Finset.range p).filter fun n => (s n).width < η i).card : ℝ)) / p ≤ ε := by
  intro ε hε
  filter_upwards [hηtop.eventually_ge_atTop (max 1 (Λ / ε))] with i hi p hp
  have hT : 0 < Real.log (η i)⁻¹ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hi)
  refine le_trans (freq_narrow_le_of_lag hle (hηpos i) (hη1 i) hp (hlag p)) ?_
  rw [div_le_iff₀ hT]
  have : Λ / ε ≤ Real.log (η i)⁻¹ := le_trans (le_max_right _ _) hi
  rw [div_le_iff₀ hε] at this
  linarith

/-! ## The telescoping estimate: the clock rate -/

/-- **The clock's budget from the lag.**  If each input step raises the deficit by at most `ξ n`
and lowers it by at least `c` per emitted output digit, then the total output is bounded:
`c · N p ≤ deficit (s 0) + Σ_{n<p} ξ n`.  This is the clock rate `N p ≤ Λ p` whenever `ξ` is
bounded on average — and for the Raney transducer `ξ n ≍ 2 log a_{n+1}`, which CF-normality does
*not* bound on average (handoff idea 3).  So the clock rate is a residual, not a freebie. -/
theorem deficit_telescope_le {s : ℕ → MobState} {N : ℕ → ℕ} {ξ : ℕ → ℝ} {c : ℝ}
    (hN0 : N 0 = 0) (hmono : Monotone N) (hle : ∀ n, (s n).width ≤ 1)
    (hstep : ∀ n, (s (n + 1)).deficit ≤ (s n).deficit + ξ n - c * blockLength N n) (p : ℕ) :
    c * N p ≤ (s 0).deficit + ∑ n ∈ Finset.range p, ξ n := by
  have key : ∀ q : ℕ, (s q).deficit + c * (∑ n ∈ Finset.range q, (blockLength N n : ℝ))
      ≤ (s 0).deficit + ∑ n ∈ Finset.range q, ξ n := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have h := hstep q
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      linarith
  have h := key p
  have hd : 0 ≤ (s p).deficit := (s p).deficit_nonneg (hle p)
  have hsum : (∑ n ∈ Finset.range p, (blockLength N n : ℝ)) = (N p : ℝ) := by
    have := sum_blockLength N hN0 hmono p
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  rw [hsum] at h
  linarith

section Audit

#print axioms MobState.deficit_nonneg
#print axioms MobState.lt_width_iff_deficit
#print axioms card_gt_le_sum_div
#print axioms freq_narrow_le_of_lag
#print axioms narrow_freq_tendsto_zero_of_lag
#print axioms deficit_telescope_le

end Audit

end NormalNumbers.VandeheyS7
