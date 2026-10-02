/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-BF: block forgetting — the route-A architecture

Lap 88's review moved §7 Problem 1 off the absolute density bound (route B: `OrbitWordBound` +
cited `GaussACRigidity`) and onto **universality** (route A), which the repo already owns the
endgame for: `affineCFN_of_uniformFreq` and `affineUniformFreq_of_runClock` reduce the headline to
`SampledUniformCount` — *the image's word-frequency limits exist and do not depend on which
CF-normal `x` is fed in* — with NO cited input and no absolute continuity.

This module supplies the architecture for that reduction, on one new hypothesis.

## The mechanism

By S7-SK the run is the orbit of the autonomous map `pairStep`, so the crux's counting function is
a Birkhoff sum of the fixed observable `slotObs w`.  Write

    blockAvg s T w z = (1/T) Σ_{j<T} slotObs w (pairStep^[j] (s, z))

for the *block time-average* started at the state `s` and the point `z`.  Two elementary facts:

* `abs_slotCount_sub_sum_blockAvg_le` — the **sliding-block identity**: the Birkhoff sum over `p`
  steps and the Cesàro sum of the block averages started at every time differ by at most `T`
  (each `j`-shift of a window of length `p` costs `j`).  So up to `T/p → 0` the crux's frequency
  IS the Cesàro average of `blockAvg (state at m) T w (Gᵐ x)`.
* `BlockForget` — if the block average forgets its initial state (uniformly over states of width
  `≥ η` and over the input point), the state at time `m` may be replaced by ONE reference state.
  What is left, `blockAvg refState T w (Gᵐ x)`, is a FIXED function of the orbit point, so its
  Cesàro average is an ordinary Birkhoff average along the CF-normal orbit and its limit cannot
  depend on `x` (`RefCesaro`; the discharge plan is directive item (b): the function is an
  interval-step function up to a digit truncation, so S7-WN evaluates it).

`BlockForget` mentions no `x`, no normality and no measure: it is a statement about the skew
product alone.  It is exactly what both Route-A probes (2026-08-24 and 2026-08-25) measured green
— the state law is KS-indistinguishable across four initial states after ~60 steps — and it is NOT
refuted by pathwise non-merging (S7-CN: reading is inert), because it compares *time averages*,
not trajectories: probe trap #2 verbatim.

## Guard rule

**Content locator.**  The width floor is not decoration: `not_blockForget_of_no_floor` would fail
outright, since a state whose image lies deep inside the cylinder of `w ++ w ++ …` emits `w` for
its whole forced block while a generic state does not; that is why `BlockForget` quantifies over
`η ≤ width` and why the architecture needs the width-frequency input.  At `T = 1` the statement is
false as well (S7-WC's `no_window_function` witnesses emit different digits from the same point),
so all the content is in the `T`-averaging.

**Degenerate cases.**  `T = 0` makes `blockAvg = 0/0 = 0` and the hypothesis vacuous — hence
`0 < T` is part of the statement.  `p = 0` makes both sides of the sliding-block identity `0`.
`w = []` is allowed and then `slotObs` is the emission indicator, so the conclusion is about the
clock rather than a word.
-/
import NormalNumbers.VandeheyS7SkewWindow
import NormalNumbers.VandeheyS7WindowDom

namespace NormalNumbers.VandeheyS7

open Set Filter Finset MeasureTheory NormalNumbers

namespace MapState

attribute [local instance] Classical.propDecidable

/-! ## The block average -/

/-- The block sum of the slot observable: `T` steps of the skew product from `(s, z)`. -/
noncomputable def blockSum (s : MapState) (T : ℕ) (w : List ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range T, slotObs w (pairStep^[j] (s, z))

/-- The block time-average of the slot observable. -/
noncomputable def blockAvg (s : MapState) (T : ℕ) (w : List ℕ) (z : ℝ) : ℝ :=
  blockSum s T w z / T

/-- The slot observable is at most `1` at every pair (not just along a run). -/
lemma slotObs_le_one' (w : List ℕ) (p : MapState × ℝ) : slotObs w p ≤ 1 := by
  have he : emitObs p ≤ 1 := by
    rw [emitObs, pairWord]
    exact_mod_cast step_snd_length_le _
  have hb : blockIndic (mapBlockSet p.1 w 0) p.2 ≤ 1 := by
    rw [blockIndic]
    by_cases hm : p.2 ∈ mapBlockSet p.1 w 0
    · simp [Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hm]
  have hbn : 0 ≤ blockIndic (mapBlockSet p.1 w 0) p.2 := blockIndic_nonneg _ _
  have hen : 0 ≤ emitObs p := by
    rw [emitObs]; exact Nat.cast_nonneg _
  calc slotObs w p = emitObs p * blockIndic (mapBlockSet p.1 w 0) p.2 := rfl
    _ ≤ 1 * 1 := by
        exact mul_le_mul he hb hbn zero_le_one
    _ = 1 := by ring

lemma blockSum_nonneg (s : MapState) (T : ℕ) (w : List ℕ) (z : ℝ) : 0 ≤ blockSum s T w z :=
  Finset.sum_nonneg fun _ _ => slotObs_nonneg _ _

lemma blockSum_le (s : MapState) (T : ℕ) (w : List ℕ) (z : ℝ) : blockSum s T w z ≤ T := by
  calc blockSum s T w z ≤ ∑ _n ∈ range T, (1:ℝ) :=
        Finset.sum_le_sum fun j _ => slotObs_le_one' _ _
    _ = T := by simp

lemma blockAvg_nonneg (s : MapState) (T : ℕ) (w : List ℕ) (z : ℝ) : 0 ≤ blockAvg s T w z :=
  div_nonneg (blockSum_nonneg _ _ _ _) (Nat.cast_nonneg _)

lemma blockAvg_le_one (s : MapState) {T : ℕ} (hT : 0 < T) (w : List ℕ) (z : ℝ) :
    blockAvg s T w z ≤ 1 := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  rw [blockAvg, div_le_one hTR]
  exact blockSum_le _ _ _ _

/-- The block average started at the run's own state and point is the run's own window sum. -/
lemma blockSum_runPair (Φ : MapState) (x : ℝ) (T : ℕ) (w : List ℕ) (m : ℕ) :
    blockSum (runState Φ x m) T w (gaussMap^[m] x)
      = ∑ j ∈ range T, slotObs w (runPair Φ x (m + j)) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [runPair_add]
  rfl

/-! ## The sliding-block identity -/

/-- Shifting the window of a `[0,1]`-valued sequence by `j` costs at most `j`. -/
lemma abs_sum_shift_sub_le {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) (p j : ℕ) :
    |∑ m ∈ range p, f (m + j) - ∑ n ∈ range p, f n| ≤ (j : ℝ) := by
  have hshift : ∑ m ∈ range p, f (m + j) = ∑ n ∈ Finset.Ico j (j + p), f n := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun m _ => by rw [Nat.add_comm]
  have hA : ∑ n ∈ range j, f n + ∑ n ∈ Finset.Ico j (j + p), f n = ∑ n ∈ range (j + p), f n := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le j) (Nat.le_add_right j p)
  have hB : ∑ n ∈ range p, f n + ∑ n ∈ Finset.Ico p (j + p), f n = ∑ n ∈ range (j + p), f n := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le p) (by omega)
  have hAle : ∑ n ∈ range j, f n ≤ (j : ℝ) := by
    calc ∑ n ∈ range j, f n ≤ ∑ _i ∈ range j, (1:ℝ) := Finset.sum_le_sum fun n _ => hf1 n
      _ = (j : ℝ) := by simp
  have hAnn : 0 ≤ ∑ n ∈ range j, f n := Finset.sum_nonneg fun n _ => hf0 n
  have hEle : ∑ n ∈ Finset.Ico p (j + p), f n ≤ (j : ℝ) := by
    calc ∑ n ∈ Finset.Ico p (j + p), f n ≤ ∑ _i ∈ Finset.Ico p (j + p), (1:ℝ) :=
          Finset.sum_le_sum fun n _ => hf1 n
      _ = (j : ℝ) := by simp
  have hEnn : 0 ≤ ∑ n ∈ Finset.Ico p (j + p), f n := Finset.sum_nonneg fun n _ => hf0 n
  rw [hshift, abs_le]
  constructor <;> linarith

/-- **The sliding-block identity.**  The crux's counting function and the Cesàro sum of the block
averages started at every time differ by at most the block length. -/
theorem abs_slotCount_sub_sum_blockAvg_le (Φ : MapState) (x : ℝ) (w : List ℕ) {T : ℕ} (hT : 0 < T)
    (p : ℕ) :
    |slotCount Φ x w p - ∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)|
      ≤ (T : ℝ) := by
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  set f : ℕ → ℝ := fun n => slotObs w (runPair Φ x n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => slotObs_nonneg _ _
  have hf1 : ∀ n, f n ≤ 1 := fun n => slotObs_le_one' _ _
  have hswap : (∑ j ∈ range T, ∑ m ∈ range p, f (m + j))
      = ∑ m ∈ range p, ∑ j ∈ range T, f (m + j) := Finset.sum_comm
  have hsum : ∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)
      = (∑ j ∈ range T, ∑ m ∈ range p, f (m + j)) / T := by
    rw [hswap, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => by rw [blockAvg, blockSum_runPair]
  have hslot : slotCount Φ x w p = ∑ n ∈ range p, f n := slotCount_eq_sum_slotObs Φ x w p
  have hkey : slotCount Φ x w p - ∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)
      = (∑ j ∈ range T, (∑ n ∈ range p, f n - ∑ m ∈ range p, f (m + j))) / T := by
    rw [hsum, hslot, Finset.sum_sub_distrib]
    rw [sub_div]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    field_simp
  rw [hkey, abs_div, abs_of_pos hTR, div_le_iff₀ hTR]
  calc |∑ j ∈ range T, (∑ n ∈ range p, f n - ∑ m ∈ range p, f (m + j))|
      ≤ ∑ j ∈ range T, |∑ n ∈ range p, f n - ∑ m ∈ range p, f (m + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range T, (T : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_sub_comm]
        refine (abs_sum_shift_sub_le hf0 hf1 p j).trans ?_
        exact_mod_cast (Finset.mem_range.1 hj).le
    _ = (T : ℝ) * T := by simp

/-! ## The reference state -/

/-- The identity state (`mob = id`, width `1`).  Any fixed state of width `≥ η` would do; this one
is explicit, so the limit produced below is manifestly independent of the run. -/
def refState : MapState where
  a := 1
  b := 0
  c := 0
  d := 1
  hd := one_pos
  hcd := by norm_num
  hb0 := le_refl 0
  hbd := zero_le_one
  hab0 := by norm_num
  habcd := by norm_num
  hdet := by norm_num

@[simp] lemma refState_mob (z : ℝ) : refState.mob z = z := by
  show (1 * z + 0) / (0 * z + 1) = z
  norm_num

lemma refState_width : refState.width = 1 := by
  rw [width, refState_mob, refState_mob]
  norm_num

/-! ## The three inputs -/

/-- **`BlockForget`** — the crux of route A.  The block time-average forgets its initial state,
uniformly over states of width `≥ η` and over the input point.  No `x`, no normality, no measure:
a statement about the skew product alone. -/
def BlockForget (w : List ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ T : ℕ, 0 < T ∧
    ∀ s s' : MapState, η ≤ s.width → η ≤ s'.width → ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |blockAvg s T w z - blockAvg s' T w z| ≤ ε

/-- **`BlockForgetGen`** — the crux of route A, in the form the architecture actually needs.
Identical to `BlockForget` except that the input point `z` is restricted to CF-normal points.
That restriction costs the architecture nothing (`exists_abs_slotCountFreq_sub_le` only ever
evaluates the hypothesis at the orbit points `Gᵐx` of a CF-normal `x`, and those are CF-normal by
`isCFNormal_gaussMap`), and it is essential: the uniform-`z` form `BlockForget` is FALSE, refuted
in `VandeheyS7Quadratic` by two states whose block averages at the quadratic irrational `√2 − 1`
differ by `≈ 1/2` for every `T`.  A quadratic irrational is never CF-normal, so the witness does
not touch `BlockForgetGen`. -/
def BlockForgetGen (w : List ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ T : ℕ, 0 < T ∧
    ∀ s s' : MapState, η ≤ s.width → η ≤ s'.width → ∀ z ∈ Set.Ioo (0:ℝ) 1, IsCFNormal z →
      |blockAvg s T w z - blockAvg s' T w z| ≤ ε

/-- The refuted uniform form is stronger: it implies the restricted one. -/
theorem BlockForget.gen {w : List ℕ} (h : BlockForget w) : BlockForgetGen w := by
  intro ε hε η hη
  obtain ⟨T, hT, hfor⟩ := h ε hε η hη
  exact ⟨T, hT, fun s s' hs hs' z hz _ => hfor s s' hs hs' z hz⟩

/-- CF-normality is preserved by every iterate of the Gauss map. -/
theorem isCFNormal_iterate {x : ℝ} (hx : IsCFNormal x) (m : ℕ) :
    IsCFNormal (gaussMap^[m] x) := by
  induction m with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact NormalNumbers.Literature.isCFNormal_gaussMap ih

/-- **`BlockForgetRun`** — the crux, in the ONLY form the architecture actually consumes, and the
one that survives S7-BX/S7-BY.  Both `BlockForget` and `BlockForgetGen` are refuted, by a single
`(state, point)` pair; but the architecture never evaluates the crux at an arbitrary pair.  It
evaluates it at the pairs `(runState Φ x m, Gᵐx)` that the run itself visits, and it only needs
their CESÀRO average to be small — a single bad time costs nothing.  So the honest crux is a
frequency statement about the skew product along a CF-normal orbit:

> at the good times (state of width `≥ η`), the block average started at the run's own state
> agrees on average with the block average started at the reference state.

`blockForgetRun_of_gen` records that this is implied by the refuted uniform form, i.e. that it is
strictly weaker, and `not_blockForgetGen` (S7-BY) shows the weakening is not cosmetic. -/
def BlockForgetRun (w : List ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ T : ℕ, 0 < T ∧
    ∀ (Φ : MapState) (x : ℝ), IsCFNormal x → (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
      ∀ᶠ p : ℕ in atTop,
        ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
          |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
            - blockAvg refState T w (gaussMap^[m] x)| ≤ ε * (p : ℝ)

/-- The refuted uniform-CF-normal form implies the run form: the crux only got weaker. -/
theorem blockForgetRun_of_gen {w : List ℕ} (h : BlockForgetGen w) : BlockForgetRun w := by
  classical
  intro ε hε η hη
  obtain ⟨T, hT, hfor⟩ := h ε hε (min η 1) (lt_min hη one_pos)
  refine ⟨T, hT, fun Φ x hx horb => ?_⟩
  filter_upwards with p
  have hterm : ∀ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
      |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
        - blockAvg refState T w (gaussMap^[m] x)| ≤ ε := by
    intro m hm
    refine hfor (runState Φ x m) refState ?_ ?_
      (gaussMap^[m] x) (horb m) (isCFNormal_iterate hx m)
    · exact le_trans (min_le_left _ _) (not_lt.1 (Finset.mem_filter.1 hm).2)
    · rw [refState_width]; exact min_le_right _ _
  calc ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η),
        |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
          - blockAvg refState T w (gaussMap^[m] x)|
      ≤ ∑ _m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η), ε :=
        Finset.sum_le_sum hterm
    _ = (((range p).filter fun m => ¬ (runState Φ x m).width < η).card : ℝ) * ε := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (p : ℝ) * ε := by
        refine mul_le_mul_of_nonneg_right ?_ hε.le
        have := Finset.card_filter_le (range p) (fun m => ¬ (runState Φ x m).width < η)
        rw [Finset.card_range] at this
        exact_mod_cast this
    _ = ε * (p : ℝ) := by ring

/-- The reference-state Cesàro input: for the FIXED state `refState` and a fixed block length the
block average is an ordinary function of the orbit point, and its Birkhoff average along a
CF-normal orbit has an `x`-independent limit.  (Discharge plan: it is an interval-step function up
to a digit truncation, so S7-WN evaluates it — directive item (b).) -/
def RefCesaro (w : List ℕ) : Prop :=
  ∀ T : ℕ, 0 < T → ∃ L : ℝ, ∀ x : ℝ, IsCFNormal x → (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) →
    Tendsto (fun p => (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / p) atTop (nhds L)

/-- The width-frequency input, in the input-time parametrisation: the times whose state is
narrower than `η` have frequency at most `δ`.  This is S7-SK's `exists_eventually_widthBad_le`
transported from the clock to the time axis. -/
def WidthBadFreq (Φ : MapState) (x : ℝ) (η δ : ℝ) : Prop :=
  ∀ᶠ p : ℕ in atTop,
    (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ) ≤ δ * p

lemma WidthBadFreq.mono_eta {Φ : MapState} {x η η' δ : ℝ} (h : WidthBadFreq Φ x η δ)
    (hle : η' ≤ η) : WidthBadFreq Φ x η' δ := by
  filter_upwards [h] with p hp
  refine le_trans ?_ hp
  have hsub : ((range p).filter fun m => (runState Φ x m).width < η')
      ⊆ ((range p).filter fun m => (runState Φ x m).width < η) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, lt_of_lt_of_le hm.2 hle⟩
  exact_mod_cast Finset.card_le_card hsub

/-! ## The architecture -/

/-- A sequence that is, for every `ε`, eventually `ε`-close to SOME constant, converges. -/
lemma exists_tendsto_of_approx {F : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ᶠ p in atTop, |F p - L| ≤ ε) :
    ∃ a : ℝ, Tendsto F atTop (nhds a) := by
  have hcau : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨L, hL⟩ := h (ε / 4) (by linarith)
    rw [eventually_atTop] at hL
    obtain ⟨N, hN⟩ := hL
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq]
    have : |F m - F n| ≤ |F m - L| + |L - F n| := by
      have := abs_add_le (F m - L) (L - F n)
      simpa using this
    rw [abs_sub_comm L (F n)] at this
    linarith
  exact cauchySeq_tendsto_of_complete hcau

/-- The limit inherits an eventual bound. -/
lemma abs_limit_sub_le {F : ℕ → ℝ} {a L ε : ℝ} (hF : Tendsto F atTop (nhds a))
    (h : ∀ᶠ p in atTop, |F p - L| ≤ ε) : |a - L| ≤ ε := by
  have habs : Tendsto (fun p => |F p - L|) atTop (nhds |a - L|) :=
    (hF.sub tendsto_const_nhds).abs
  exact le_of_tendsto habs h

/-- **The architecture theorem.**  `BlockForget` + `RefCesaro` produce, for every `ε` and every
width floor `η ≤ 1`, a constant `L` — depending on neither the map `Φ` nor the input `x` — that
the crux's frequency is eventually `4ε`-close to, for EVERY CF-normal input whose narrow times
have frequency at most `ε` at that floor. -/
theorem exists_abs_slotCountFreq_sub_le {w : List ℕ} (hBF : BlockForgetRun w) (hRC : RefCesaro w)
    {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ L : ℝ, ∀ (Φ : MapState) (x : ℝ), IsCFNormal x →
      (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) → WidthBadFreq Φ x η ε →
      ∀ᶠ p : ℕ in atTop, |slotCount Φ x w p / (p : ℝ) - L| ≤ 4 * ε := by
  obtain ⟨T, hT, hfor⟩ := hBF ε hε η hη
  obtain ⟨L, hL⟩ := hRC T hT
  refine ⟨L, fun Φ x hx horb hbad => ?_⟩
  have hrun := hfor Φ x hx horb
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have hA : ∀ᶠ p : ℕ in atTop, (T : ℝ) / (p : ℝ) ≤ ε := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually (eventually_lt_nhds hε)
    filter_upwards [this] with p hp using hp.le
  have hB := (hL x hx horb).eventually (eventually_abs_sub_lt L hε)
  filter_upwards [hA, hB, hbad, hrun, eventually_gt_atTop 0] with p hA' hB' hbad' hrun' hp0
  have hpR : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- step 1: the sliding-block identity
  have h1 : |slotCount Φ x w p / (p : ℝ)
      - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)| ≤ ε := by
    have hid := abs_slotCount_sub_sum_blockAvg_le Φ x w hT p
    have hTp : (T:ℝ) ≤ ε * (p:ℝ) := by rw [div_le_iff₀ hpR] at hA'; exact hA'
    rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR]
    linarith
  -- step 2: replace every state by the reference state
  have h2 : |(∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
      - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)| ≤ 2 * ε := by
    rw [div_sub_div_same, abs_div, abs_of_pos hpR, div_le_iff₀ hpR, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    classical
    set g : ℕ → ℝ := fun m => |blockAvg (runState Φ x m) T w (gaussMap^[m] x)
      - blockAvg refState T w (gaussMap^[m] x)| with hg
    have hsplit := Finset.sum_filter_add_sum_filter_not (range p)
      (fun m => (runState Φ x m).width < η) g
    have hbadpart : ∑ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m
        ≤ (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ) := by
      have hone : ∀ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m ≤ 1 := by
        intro m _
        have h0 := blockAvg_nonneg (runState Φ x m) T w (gaussMap^[m] x)
        have h1' := blockAvg_le_one (runState Φ x m) hT w (gaussMap^[m] x)
        have h0' := blockAvg_nonneg refState T w (gaussMap^[m] x)
        have h1'' := blockAvg_le_one refState hT w (gaussMap^[m] x)
        rw [hg, abs_le]
        constructor <;> linarith
      calc ∑ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m
          ≤ ∑ _m ∈ (range p).filter (fun m => (runState Φ x m).width < η), (1:ℝ) :=
            Finset.sum_le_sum hone
        _ = (((range p).filter fun m => (runState Φ x m).width < η).card : ℝ) := by simp
    have hgoodpart : ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η), g m
        ≤ ε * (p : ℝ) := hrun'
    calc ∑ m ∈ range p, g m
        = ∑ m ∈ (range p).filter (fun m => (runState Φ x m).width < η), g m
          + ∑ m ∈ (range p).filter (fun m => ¬ (runState Φ x m).width < η), g m := hsplit.symm
      _ ≤ ε * (p:ℝ) + ε * (p:ℝ) := by linarith
      _ = 2 * ε * (p : ℝ) := by ring
  -- step 3: the reference average converges to `L`
  have h3 : |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - L| ≤ ε := hB'.le
  calc |slotCount Φ x w p / (p : ℝ) - L|
      ≤ |slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)|
        + |(∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)|
        + |(∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - L| := by
        have t1 := abs_add_le (slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ))
          ((∑ m ∈ range p, blockAvg (runState Φ x m) T w (gaussMap^[m] x)) / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ))
        have t2 := abs_add_le ((slotCount Φ x w p / (p : ℝ)
          - (∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ)))
          ((∑ m ∈ range p, blockAvg refState T w (gaussMap^[m] x)) / (p : ℝ) - L)
        simp only [sub_add_sub_cancel] at t1 t2
        linarith
    _ ≤ ε + 2 * ε + ε := by linarith
    _ = 4 * ε := by ring

/-! ## The conclusion: existence, and independence of the input -/

/-- The width-frequency input, packaged as it is used: an affordable floor for every tolerance. -/
def WidthAfford (Φ : MapState) (x : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ WidthBadFreq Φ x η δ

/-- **Per input: the crux's frequency converges.**  No value is asserted. -/
theorem exists_tendsto_slotCountFreq {w : List ℕ} (hBF : BlockForgetRun w) (hRC : RefCesaro w)
    (Φ : MapState) {x : ℝ} (hx : IsCFNormal x) (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hwf : WidthAfford Φ x) :
    ∃ a : ℝ, Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop (nhds a) := by
  refine exists_tendsto_of_approx fun ε hε => ?_
  obtain ⟨η, hη, hη1, hbad⟩ := hwf (ε / 4) (by linarith)
  obtain ⟨L, hL⟩ := exists_abs_slotCountFreq_sub_le hBF hRC (show (0:ℝ) < ε / 4 by linarith) hη hη1
  refine ⟨L, ?_⟩
  filter_upwards [hL Φ x hx horb hbad] with p hp
  linarith

/-- **Independence of the input.**  Two CF-normal inputs (and even two maps) that both afford a
width floor give the SAME frequency.  This is the universality that route A needs. -/
theorem tendsto_slotCountFreq_eq {w : List ℕ} (hBF : BlockForgetRun w) (hRC : RefCesaro w)
    {Φ Φ' : MapState} {x x' : ℝ} (hx : IsCFNormal x)
    (horb : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) (hwf : WidthAfford Φ x)
    (hx' : IsCFNormal x') (horb' : ∀ k, gaussMap^[k] x' ∈ Set.Ioo (0:ℝ) 1)
    (hwf' : WidthAfford Φ' x') {a a' : ℝ}
    (ha : Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop (nhds a))
    (ha' : Tendsto (fun p => slotCount Φ' x' w p / (p : ℝ)) atTop (nhds a')) : a = a' := by
  by_contra hne
  have hd : 0 < |a - a'| := abs_pos.2 (sub_ne_zero.2 hne)
  set d : ℝ := |a - a'| with hdd
  obtain ⟨η, hη, hη1, hbad⟩ := hwf (d / 16) (by linarith)
  obtain ⟨η', hη', hη1', hbad'⟩ := hwf' (d / 16) (by linarith)
  set θ : ℝ := min η η' with hθ
  have hθ0 : 0 < θ := lt_min hη hη'
  have hθ1 : θ ≤ 1 := le_trans (min_le_left _ _) hη1
  have hb1 : WidthBadFreq Φ x θ (d / 16) := hbad.mono_eta (min_le_left _ _)
  have hb2 : WidthBadFreq Φ' x' θ (d / 16) := hbad'.mono_eta (min_le_right _ _)
  obtain ⟨L, hL⟩ := exists_abs_slotCountFreq_sub_le hBF hRC
    (show (0:ℝ) < d / 16 by linarith) hθ0 hθ1
  have h1 : |a - L| ≤ 4 * (d / 16) := abs_limit_sub_le ha (hL Φ x hx horb hb1)
  have h2 : |a' - L| ≤ 4 * (d / 16) := abs_limit_sub_le ha' (hL Φ' x' hx' horb' hb2)
  have h3 : |a - a'| ≤ |a - L| + |L - a'| := by
    have := abs_add_le (a - L) (L - a')
    simpa using this
  rw [abs_sub_comm L a'] at h3
  linarith

/-- **S7-BF, the route-A architecture.**  `BlockForget` + `RefCesaro` + an affordable width floor
give one constant `L` that EVERY CF-normal input's crux frequency converges to.  That is the
`SampledUniformCount` shape — existence of the limit and independence of `x` — with no absolute
continuity, no constant `C` and no cited ergodic input. -/
theorem exists_uniform_slotCountFreq {w : List ℕ} (hBF : BlockForgetRun w) (hRC : RefCesaro w) :
    ∃ L : ℝ, ∀ (Φ : MapState) (x : ℝ), IsCFNormal x →
      (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) → WidthAfford Φ x →
      Tendsto (fun p => slotCount Φ x w p / (p : ℝ)) atTop (nhds L) := by
  classical
  by_cases hex : ∃ (Φ : MapState) (x : ℝ), IsCFNormal x ∧
      (∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1) ∧ WidthAfford Φ x
  · obtain ⟨Φ₀, x₀, hx₀, horb₀, hwf₀⟩ := hex
    obtain ⟨a₀, ha₀⟩ := exists_tendsto_slotCountFreq hBF hRC Φ₀ hx₀ horb₀ hwf₀
    refine ⟨a₀, fun Φ x hx horb hwf => ?_⟩
    obtain ⟨a, ha⟩ := exists_tendsto_slotCountFreq hBF hRC Φ hx horb hwf
    have heq : a = a₀ :=
      tendsto_slotCountFreq_eq hBF hRC hx horb hwf hx₀ horb₀ hwf₀ ha ha₀
    exact heq ▸ ha
  · exact ⟨0, fun Φ x hx horb hwf => absurd ⟨Φ, x, hx, horb, hwf⟩ hex⟩

end MapState

section Audit

#print axioms MapState.abs_slotCount_sub_sum_blockAvg_le
#print axioms MapState.exists_abs_slotCountFreq_sub_le
#print axioms MapState.exists_tendsto_slotCountFreq
#print axioms MapState.tendsto_slotCountFreq_eq
#print axioms MapState.BlockForget.gen
#print axioms MapState.exists_uniform_slotCountFreq

end Audit

end NormalNumbers.VandeheyS7
