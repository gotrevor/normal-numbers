/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-C3: the clock does not have to tick every step

`clockIndex` (S7-BD) is `Nat.findGreatest (fun n => N n ≤ m) m`, and the cap `m` is only legitimate
when `N n ≥ n`, i.e. when the clock is strictly monotone — one emitted digit for every input digit.
**A transducer does not do that.**  Reading a digit can leave the state un-emittable, and the
`φ`-machine certainly stalls: the emission rate is asymptotically one, not pointwise one.  So
`StrictMono N` is the wrong hypothesis on the clock and would make `StatePin` uninstantiable.

This module replaces it.  `clockIdx N m = sInf {n | m < N (n+1)}` is the last completed block at
output time `m`, and its two defining properties need **no monotonicity at all**:

* `lt_clockIdx_succ` — `m < N (clockIdx N m + 1)`, from unboundedness alone;
* `clockIdx_le` — `N (clockIdx N m) ≤ m`, from `N 0 = 0` and minimality.

Monotonicity enters only in `le_clockIdx`.  `freq_le_of_clock_mono` is then S7-BD's interpolation
with `Monotone N + Tendsto N atTop atTop` in place of `StrictMono N`, and
`freq_le_of_blockAverage_mono` the corresponding reduction, stated with the coupling as a plain
hypothesis so no structure has to carry `StrictMono`.
-/
import NormalNumbers.VandeheyS7StateAudit

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- The index of the block in progress at output time `m`. -/
noncomputable def clockIdx (N : ℕ → ℕ) (m : ℕ) : ℕ := sInf {n | m < N (n + 1)}

section

variable {N : ℕ → ℕ}

lemma clockIdx_nonempty (hunb : Tendsto N atTop atTop) (m : ℕ) :
    {n | m < N (n + 1)}.Nonempty := by
  obtain ⟨k, hk⟩ := eventually_atTop.1 (hunb.eventually_gt_atTop m)
  exact ⟨k, hk (k + 1) (by omega)⟩

/-- **The block in progress has not finished.**  No monotonicity needed. -/
lemma lt_clockIdx_succ (hunb : Tendsto N atTop atTop) (m : ℕ) :
    m < N (clockIdx N m + 1) := by
  exact Nat.sInf_mem (clockIdx_nonempty hunb m)

/-- **The block in progress has started.**  From `N 0 = 0` and minimality. -/
lemma clockIdx_le (hN0 : N 0 = 0) (m : ℕ) : N (clockIdx N m) ≤ m := by
  rcases Nat.eq_zero_or_pos (clockIdx N m) with h | h
  · rw [h, hN0]; exact Nat.zero_le m
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    have hnot : ¬ (m < N (k + 1)) := by
      intro hmem
      have hle : clockIdx N m ≤ k := Nat.sInf_le hmem
      omega
    rw [hk]; exact Nat.le_of_not_lt hnot

lemma le_clockIdx (hmono : Monotone N) (hunb : Tendsto N atTop atTop) {p m : ℕ}
    (h : N p ≤ m) : p ≤ clockIdx N m := by
  by_contra hc
  simp only [not_le] at hc
  have : m < N p := lt_of_lt_of_le (lt_clockIdx_succ hunb m) (hmono (by omega))
  omega

/-- **Interpolation with a stalling clock.**  S7-BD's `freq_le_of_clock` with `StrictMono N`
weakened to `Monotone N` plus unboundedness. -/
theorem freq_le_of_clock_mono {f : ℕ → ℝ} (hfmono : Monotone f)
    (hmono : Monotone N) (hunb : Tendsto N atTop atTop) (hN0 : N 0 = 0) {B : ℝ} (hB : 0 ≤ B)
    (hratio : Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1))
    (htick : ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, f (N p) ≤ (B + ε) * N p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, f m ≤ (B + ε) * m := by
  intro ε hε
  set δ : ℝ := ε / (2 * (B + ε)) with hδdef
  have hBε : 0 < B + ε := by linarith
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hpos : ∀ᶠ n in atTop, 0 < (N n : ℝ) := by
    filter_upwards [hunb.eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  have hr : ∀ᶠ n in atTop, ((N (n + 1) : ℝ)) ≤ (1 + δ) * (N n : ℝ) := by
    have h1 : ∀ᶠ n in atTop, ((N (n + 1) : ℝ)) / (N n : ℝ) < 1 + δ :=
      hratio.eventually (eventually_lt_nhds (by linarith : (1:ℝ) < 1 + δ))
    filter_upwards [h1, hpos] with n hn hp
    rw [div_lt_iff₀ hp] at hn
    linarith
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.1 (hr.and (htick (ε / 2) (by linarith)))
  filter_upwards [eventually_ge_atTop (N p₁)] with m hm
  set n := clockIdx N m with hn
  have hnp : p₁ ≤ n := le_clockIdx hmono hunb hm
  obtain ⟨hrn, _⟩ := hp₁ n hnp
  obtain ⟨_, htn⟩ := hp₁ (n + 1) (by omega)
  have hNn : (N n : ℝ) ≤ (m : ℝ) := by exact_mod_cast clockIdx_le hN0 m
  have hstep1 : f m ≤ f (N (n + 1)) := hfmono (le_of_lt (lt_clockIdx_succ hunb m))
  have hpos2 : 0 ≤ B + ε / 2 := by linarith
  have hkey : (B + ε / 2) * (1 + δ) ≤ B + ε := by
    have hle : δ * (B + ε / 2) ≤ ε / 2 := by
      have h1 : δ * (B + ε / 2) ≤ δ * (B + ε) := by nlinarith
      have h2 : δ * (B + ε) = ε / 2 := by rw [hδdef]; field_simp
      linarith
    nlinarith
  calc f m ≤ f (N (n + 1)) := hstep1
    _ ≤ (B + ε / 2) * (N (n + 1) : ℝ) := htn
    _ ≤ (B + ε / 2) * ((1 + δ) * (N n : ℝ)) := mul_le_mul_of_nonneg_left hrn hpos2
    _ = ((B + ε / 2) * (1 + δ)) * (N n : ℝ) := by ring
    _ ≤ (B + ε) * (N n : ℝ) := by
        refine mul_le_mul_of_nonneg_right hkey ?_
        positivity
    _ ≤ (B + ε) * (m : ℝ) := mul_le_mul_of_nonneg_left hNn (le_of_lt hBε)

end

/-! ## The reduction with a stalling clock -/

/-- S7-BD's `BlockCoupling` with `StrictMono N` weakened to monotone + unbounded. -/
structure BlockCouplingM (A : Set ℝ) (x y : ℝ) (N : ℕ → ℕ) (S : ℕ → ℕ → Set ℝ) : Prop where
  base : N 0 = 0
  mono : Monotone N
  unbounded : Tendsto N atTop atTop
  couple : ∀ n j, j < N (n + 1) - N n →
    (gaussMap^[N n + j] y ∈ A ↔ gaussMap^[n] x ∈ S n j)

theorem blockCount_clock_eq_mono {A : Set ℝ} {x y : ℝ} {N : ℕ → ℕ} {S : ℕ → ℕ → Set ℝ}
    (h : BlockCouplingM A x y N S) (p : ℕ) :
    blockCount A (N p) y
      = ∑ n ∈ Finset.range p, blockHitCount (S n) (N (n + 1) - N n) (gaussMap^[n] x) := by
  rw [blockCount_eq_sum_blocks A h.base h.mono p y]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < N (n + 1) - N n := Finset.mem_range.1 hj
  unfold blockIndic
  by_cases hmem : gaussMap^[N n + j] y ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((h.couple n j hj').1 hmem)]
    rfl
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun hc => hmem ((h.couple n j hj').2 hc))]

/-- **S7-C3, the reduction.**  A stalling clock still gives the crux's frequency bound. -/
theorem freq_le_of_blockAverage_mono {A : Set ℝ} {x y : ℝ} {N : ℕ → ℕ} {S : ℕ → ℕ → Set ℝ}
    (h : BlockCouplingM A x y N S)
    (hratio : Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1))
    {B : ℝ} (hB : 0 ≤ B) (hBA : BlockAverageBound B x N S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, blockCount A m y / m ≤ B + ε := by
  have hmono : Monotone (fun m => blockCount A m y) := by
    intro a b hab
    simp only [blockCount_apply]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab) ?_
    intro i _ _
    exact Set.indicator_nonneg (by intro _ _; norm_num) _
  have htick : ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, blockCount A (N p) y ≤ (B + ε) * N p := by
    intro ε hε
    filter_upwards [hBA ε hε] with p hp
    rw [blockCount_clock_eq_mono h p]
    exact hp
  intro ε hε
  filter_upwards [freq_le_of_clock_mono hmono h.mono h.unbounded h.base hB hratio htick ε hε,
    eventually_gt_atTop 0] with m hm hm0
  rw [div_le_iff₀ (by exact_mod_cast hm0)]
  exact hm

section Audit

#print axioms freq_le_of_clock_mono
#print axioms freq_le_of_blockAverage_mono

end Audit

end NormalNumbers.VandeheyS7
