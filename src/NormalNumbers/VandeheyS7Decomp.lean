/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-BD: the transducer block decomposition

Lap 74 closed the MEASURE side of the §7 crux (`VandeheyS7Pull`): a state `s` of width `≥ η` and
distortion `≤ K` pulls the whole emitted block `I_w, G^{-1}I_w, …, G^{-(L-1)}I_w` back to input
sets of total Gauss mass `≤ (2K/η)·L·γ(I_w)`, with no accumulation along the block
(`MobState.blockPullback_sum_le`).

This module supplies the COUNTING side, which is what turns that measure bound into
`OrbitWordBound`.  The transducer reads input digit `n` and emits a block of `Lₙ` output digits;
writing `N p = L₀ + ⋯ + L_{p-1}` for the **clock** (the number of output digits produced by the
first `p` input digits), the output position `N n + j` carries the same indicator as the input
position `n` tested against the pulled-back set `S n j = sₙ⁻¹(G^{-j} I_w)`.  Hence

    blockCount (I_w) (N p) y  =  ∑_{n < p} #{j < Lₙ : Gⁿ x ∈ S n j}.                 (BD)

`blockCount_clock_eq` is exactly (BD), from the abstract regrouping `blockCount_eq_sum_blocks`
plus a `BlockCoupling` hypothesis packaging what the transducer supplies.

The residual is then named: `BlockAverageBound B` says the right-hand side of (BD), divided by the
number `N p` of output digits, is eventually `≤ B`.  Combined with the clock being *regular*
(`N (n+1) / N n → 1`, i.e. the bursts are sparse — the SAME hypothesis as the width floor, by
lap 74's `fib_sq_mul_width_le_of_forced`), `freq_le_of_clock` interpolates from the clock ticks to
every output time, giving the frequency bound in the shape `OrbitWordBound` wants.

**Guard rules.**  Degenerate cases: `w = []` (every point is in `I_w`, and `B = 1` is forced), and
a clock with `Lₙ = 0` for some `n` — excluded here by `StrictMono N`, because an input digit that
emits nothing makes the interpolation false, not merely unprovable.  Content locator: at `Lₙ ≡ 1`
(so `N = id`) `BlockAverageBound` is literally the lap-30 one-step statement
"`limsup (1/N) #{n<N : Gⁿx ∈ sₙ⁻¹ E} ≤ C γ(E)`", i.e. directive fact (α).  So this module is pure
bookkeeping: it moves no part of (α), it only shows (α) is all that is left.
-/
import NormalNumbers.VandeheyS7Pull

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-! ## The abstract regrouping -/

/-- `blockHitCount S L x = #{j < L : x ∈ S j}`, as a real number.  This is the count of
occurrences of the target word inside one emitted block, read off at the single input time `x`. -/
noncomputable def blockHitCount (S : ℕ → Set ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range L, blockIndic (S j) x

lemma blockHitCount_nonneg (S : ℕ → Set ℝ) (L : ℕ) (x : ℝ) : 0 ≤ blockHitCount S L x :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (by intro _ _; norm_num) _

/-- **Regrouping.**  A Birkhoff block count up to a clock time `N p` splits along the blocks. -/
theorem blockCount_eq_sum_blocks (A : Set ℝ) {N : ℕ → ℕ} (hN0 : N 0 = 0) (hmono : Monotone N)
    (p : ℕ) (y : ℝ) :
    blockCount A (N p) y
      = ∑ n ∈ Finset.range p, ∑ j ∈ Finset.range (N (n + 1) - N n),
          blockIndic A (gaussMap^[N n + j] y) := by
  induction p with
  | zero => simp [blockCount_apply, hN0]
  | succ p ih =>
    have hle : N p ≤ N (p + 1) := hmono (Nat.le_succ p)
    obtain ⟨L, hL⟩ : ∃ L, N (p + 1) = N p + L := ⟨N (p + 1) - N p, by omega⟩
    rw [Finset.sum_range_succ, ← ih, blockCount_apply, blockCount_apply, hL,
      Nat.add_sub_cancel_left, Finset.sum_range_add]

/-! ## The transducer coupling -/

/-- **What the transducer supplies.**  `N` is the clock (output digits produced by the first `n`
input digits) and `S n j` is the pullback `sₙ⁻¹(G^{-j} A)` of the `j`-th slot of the block emitted
at input time `n`.  `couple` is the defining property of a transducer state: the output digit
stream from position `N n` on is determined by `Gⁿ x` through `sₙ`. -/
structure BlockCoupling (A : Set ℝ) (x y : ℝ) (N : ℕ → ℕ) (S : ℕ → ℕ → Set ℝ) : Prop where
  base : N 0 = 0
  strictMono : StrictMono N
  couple : ∀ n j, j < N (n + 1) - N n →
    (gaussMap^[N n + j] y ∈ A ↔ gaussMap^[n] x ∈ S n j)

/-- **(BD).**  The occurrences of the word in the first `N p` output digits are the sum, over the
first `p` input times, of the hits of the pulled-back block. -/
theorem blockCount_clock_eq {A : Set ℝ} {x y : ℝ} {N : ℕ → ℕ} {S : ℕ → ℕ → Set ℝ}
    (h : BlockCoupling A x y N S) (p : ℕ) :
    blockCount A (N p) y
      = ∑ n ∈ Finset.range p, blockHitCount (S n) (N (n + 1) - N n) (gaussMap^[n] x) := by
  rw [blockCount_eq_sum_blocks A h.base h.strictMono.monotone p y]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < N (n + 1) - N n := Finset.mem_range.1 hj
  unfold blockIndic
  by_cases hmem : gaussMap^[N n + j] y ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((h.couple n j hj').1 hmem)]
    rfl
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun hc => hmem ((h.couple n j hj').2 hc))]

/-! ## The clock index, and interpolation between ticks -/

/-- The number of complete blocks finished by output time `m`. -/
def clockIndex (N : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.findGreatest (fun n => N n ≤ m) m

lemma clock_le {N : ℕ → ℕ} (hN0 : N 0 = 0) (m : ℕ) : N (clockIndex N m) ≤ m :=
  Nat.findGreatest_spec (P := fun n => N n ≤ m) (m := 0) (Nat.zero_le m) (by omega)

lemma lt_clock_succ {N : ℕ → ℕ} (hs : StrictMono N) (m : ℕ) :
    m < N (clockIndex N m + 1) := by
  unfold clockIndex
  rcases eq_or_lt_of_le (Nat.findGreatest_le (P := fun n => N n ≤ m) m) with heq | hlt
  · rw [heq]
    exact lt_of_lt_of_le (Nat.lt_succ_self m) hs.le_apply
  · have hgt := Nat.findGreatest_is_greatest (P := fun n => N n ≤ m)
      (Nat.lt_succ_self (Nat.findGreatest (fun n => N n ≤ m) m)) (by omega)
    exact Nat.lt_of_not_le hgt

lemma le_clockIndex {N : ℕ → ℕ} (hs : StrictMono N) {p m : ℕ} (h : N p ≤ m) :
    p ≤ clockIndex N m := by
  have hp : p ≤ m := le_trans hs.le_apply h
  exact Nat.le_findGreatest hp h

/-- **Interpolation.**  A monotone count controlled at the clock ticks, with a regular clock, is
controlled at every time.  (`f = blockCount A · y`, `B = C γ(I_w)`.) -/
theorem freq_le_of_clock {f : ℕ → ℝ} (hfmono : Monotone f) {N : ℕ → ℕ}
    (hs : StrictMono N) (hN0 : N 0 = 0) {B : ℝ} (hB : 0 ≤ B)
    (hratio : Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1))
    (htick : ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, f (N p) ≤ (B + ε) * N p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, f m ≤ (B + ε) * m := by
  intro ε hε
  set δ : ℝ := ε / (2 * (B + ε)) with hδdef
  have hBε : 0 < B + ε := by linarith
  have hδ : 0 < δ := by rw [hδdef]; positivity
  -- eventually the clock ratio is below `1 + δ`
  have hr : ∀ᶠ n in atTop, ((N (n + 1) : ℝ)) ≤ (1 + δ) * (N n : ℝ) := by
    have h1 : ∀ᶠ n in atTop, ((N (n + 1) : ℝ)) / (N n : ℝ) < 1 + δ := by
      have := hratio.eventually (eventually_lt_nhds (by linarith : (1:ℝ) < 1 + δ))
      exact this
    have h2 : ∀ᶠ n in atTop, 0 < (N n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : 0 < N n := lt_of_lt_of_le (by have := hs (show (0:ℕ) < 1 by norm_num); omega) (hs.monotone hn)
      exact_mod_cast this
    filter_upwards [h1, h2] with n hn hpos
    rw [div_lt_iff₀ hpos] at hn
    linarith
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.1 (hr.and (htick (ε / 2) (by linarith)))
  filter_upwards [eventually_ge_atTop (N p₁)] with m hm
  set n := clockIndex N m with hn
  have hnp : p₁ ≤ n := le_clockIndex hs (le_trans (le_refl _) hm)
  obtain ⟨hrn, _⟩ := hp₁ n hnp
  obtain ⟨_, htn⟩ := hp₁ (n + 1) (by omega)
  have hNn : (N n : ℝ) ≤ (m : ℝ) := by exact_mod_cast clock_le hN0 m
  have hstep1 : f m ≤ f (N (n + 1)) := hfmono (le_of_lt (lt_clock_succ hs m))
  have hpos2 : 0 ≤ B + ε / 2 := by linarith
  have hkey : (B + ε / 2) * (1 + δ) ≤ B + ε := by
    have : δ * (B + ε / 2) ≤ ε / 2 := by
      have h1 : δ * (B + ε / 2) ≤ δ * (B + ε) := by nlinarith
      have h2 : δ * (B + ε) = ε / 2 := by
        rw [hδdef]; field_simp
      linarith
    nlinarith
  calc f m ≤ f (N (n + 1)) := hstep1
    _ ≤ (B + ε / 2) * (N (n + 1) : ℝ) := htn
    _ ≤ (B + ε / 2) * ((1 + δ) * (N n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hrn hpos2
    _ = ((B + ε / 2) * (1 + δ)) * (N n : ℝ) := by ring
    _ ≤ (B + ε) * (N n : ℝ) := by
        refine mul_le_mul_of_nonneg_right hkey ?_
        positivity
    _ ≤ (B + ε) * (m : ℝ) := by
        exact mul_le_mul_of_nonneg_left hNn (le_of_lt hBε)

/-! ## The residual -/

/-- **The residual of the crux.**  The per-input-time average of the in-block hit counts is
bounded by `B`.  At `N = id` this is literally directive fact (α), the open heart of §7. -/
def BlockAverageBound (B : ℝ) (x : ℝ) (N : ℕ → ℕ) (S : ℕ → ℕ → Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop,
    (∑ n ∈ Finset.range p, blockHitCount (S n) (N (n + 1) - N n) (gaussMap^[n] x))
      ≤ (B + ε) * N p

/-- **S7-BD, the reduction.**  Coupling + a regular clock + `BlockAverageBound B` give the
word-frequency bound on the image expansion that `OrbitWordBound` asks for. -/
theorem freq_le_of_blockAverage {A : Set ℝ} {x y : ℝ} {N : ℕ → ℕ} {S : ℕ → ℕ → Set ℝ}
    (h : BlockCoupling A x y N S)
    (hratio : Tendsto (fun n => ((N (n + 1) : ℝ)) / (N n : ℝ)) atTop (nhds 1))
    {B : ℝ} (hB : 0 ≤ B) (hBA : BlockAverageBound B x N S) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, blockCount A m y / m ≤ B + ε := by
  have hmono : Monotone (fun m => blockCount A m y) := by
    intro a b hab
    simp only [blockCount_apply]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hab) ?_
    intro i _ _
    exact Set.indicator_nonneg (by intro _ _; norm_num) _
  have htick : ∀ ε : ℝ, 0 < ε → ∀ᶠ p in atTop, blockCount A (N p) y ≤ (B + ε) * N p := by
    intro ε hε
    filter_upwards [hBA ε hε] with p hp
    rw [blockCount_clock_eq h p]
    exact hp
  intro ε hε
  filter_upwards [freq_le_of_clock hmono h.strictMono h.base hB hratio htick ε hε,
    eventually_gt_atTop 0] with m hm hm0
  rw [div_le_iff₀ (by exact_mod_cast hm0)]
  exact hm

/-! ## The bridge to the measure side (S7-PB)

`BlockAverageBound` asks for a bound on the *empirical* block average along the orbit of `x`.
Lap 74's pullback bound gives the corresponding *`γ`-average* — the expected block count — with
exactly the constant the crux needs.  So the residual is, precisely and only, "empirical matches
expected for a predictable family", which is directive fact (α).
-/

/-- The `j`-th slot of the block emitted by the state `s`, pulled back to the input: this is the
set `S n j` the coupling refers to, in the shape `VandeheyS7Pull` proves bounds for. -/
def stateBlockSet (s : MobState) (w : List ℕ) (j : ℕ) : Set ℝ :=
  s.mob ⁻¹' (gaussMap^[j] ⁻¹' cfCylinder w ∩ Set.Ioo (0:ℝ) 1) ∩ Set.Ioo (0:ℝ) 1

lemma measurableSet_stateBlockSet (s : MobState) (w : List ℕ) (j : ℕ) :
    MeasurableSet (stateBlockSet s w j) := by
  refine MeasurableSet.inter (s.measurable_mob ?_) measurableSet_Ioo
  exact ((measurable_gaussMap.iterate j) (measurableSet_cfCylinder w)).inter measurableSet_Ioo

/-- **The expected block count.**  The `γ`-average of the in-block hit count is bounded by
`(2K/η)·L·γ(I_w)` — the crux's constant, with no accumulation along the block. -/
theorem integral_blockHitCount_le (s : MobState) {η K : ℝ} (hη : 0 < η)
    (hwidth : η ≤ s.width) (hK : s.distortion ≤ K) (w : List ℕ) (L : ℕ) :
    ∫ t, blockHitCount (stateBlockSet s w) L t ∂gaussMeasure
      ≤ 2 * K / η * L * (gaussMeasure (cfCylinder w)).toReal := by
  have hint : ∫ t, blockHitCount (stateBlockSet s w) L t ∂gaussMeasure
      = ∑ j ∈ Finset.range L, (gaussMeasure (stateBlockSet s w j)).toReal := by
    unfold blockHitCount blockIndic
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [MeasureTheory.integral_indicator_one (measurableSet_stateBlockSet s w j),
        MeasureTheory.measureReal_def]
    · intro j _
      exact (MeasureTheory.integrable_indicator_iff
        (measurableSet_stateBlockSet s w j)).2
        (MeasureTheory.integrableOn_const (by simp))
  rw [hint]
  exact s.blockPullback_sum_le hη hwidth hK w L

section Audit

#print axioms blockCount_eq_sum_blocks
#print axioms blockCount_clock_eq
#print axioms clock_le
#print axioms lt_clock_succ
#print axioms le_clockIndex
#print axioms freq_le_of_clock
#print axioms freq_le_of_blockAverage
#print axioms integral_blockHitCount_le

end Audit

end NormalNumbers.VandeheyS7
