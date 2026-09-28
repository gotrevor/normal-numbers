/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyStateMixing
import NormalNumbers.VandeheyCocycle
import NormalNumbers.CFAeNormal

/-!
# The two-point correlation of the joint (window, state) deviation

`VandeheyCocycle.ClassEquidistribution` asks for the *local `K`-averages* of
`VandeheyCocycle.jointDev` to be small on average along every CF-normal orbit.  A mean bound is
not enough — the averages sit inside an absolute value — so what is needed is a **variance**
bound, i.e. the decay of the two-point correlations

> `∫ jointDev(·,k) · jointDev(·,k') dγ`,  `k + |q| ≤ k'`.

This file supplies the measure-theoretic side.  Its plan:

* **Plumbing.**  `mem_cfCylinder_iff_cfWord`, `mem_familySetC_iff_cfWord`, `cfWord_iterate`,
  `mem_horizonSet_cfCylinder_iff` — the dictionary between the *word* description of an event
  (as `VandeheyCocycle` states it) and its *set* description (as the mixing bricks state it).
* **`devFun`** — the manifestly measurable representative of `jointDev`:
  `1_{A_k} − L·1_{B_k}` with `A_k = stateHorizonSet δ (I_q) k d t`, `B_k = horizonSet (I_q) k`.
* The four a.e. identifications of `A_k ∩ A_{k'}`, `A_k ∩ B_{k'}`, `B_k ∩ A_{k'}`, `B_k ∩ B_{k'}`
  as (past family) ∩ (past-dependent future), feeding the bricks of `VandeheyStateMixing`.
* The correlation bound: with `L` equal to the pin's constant `c` the four leading terms cancel
  **exactly**, leaving a pure `θ^{k'−k−|q|}` remainder.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut

/-! ## Plumbing: words versus sets -/

/-- The `i`-th entry of the digit word. -/
lemma cfWord_getD (y : ℝ) (n i : ℕ) (hi : i < n) : (cfWord y n).getD i 0 = cfDigit y i := by
  have hlen : i < (cfWord y n).length := by simpa [cfWord] using hi
  rw [List.getD_eq_getElem _ 0 hlen]
  simp only [cfWord, List.getElem_map, List.getElem_range]

/-- Membership in a CF cylinder, read off the digit word.  No irrationality needed. -/
lemma mem_cfCylinder_iff_cfWord {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) (w : List ℕ) :
    y ∈ cfCylinder w ↔ w = cfWord y w.length := by
  constructor
  · rintro ⟨-, hdig⟩
    refine List.ext_getElem (by simp [cfWord]) ?_
    intro i h1 h2
    have hi : i < w.length := h1
    have := hdig i hi
    rw [List.getD_eq_getElem w 0 hi] at this
    simp only [cfWord, List.getElem_map, List.getElem_range]
    exact this.symm
  · intro hw
    refine ⟨hy, ?_⟩
    intro i hi
    have hcg := congrArg (fun l : List ℕ => List.getD l i 0) hw
    rw [hcg, cfWord_getD y w.length i hi]

/-- Membership in a countable same-length cylinder family, read off the digit word. -/
lemma mem_familySetC_iff_cfWord {𝒮 : Set (List ℕ)} {m : ℕ} (hlen : ∀ w ∈ 𝒮, w.length = m)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    y ∈ VandeheyMix.familySetC 𝒮 ↔ cfWord y m ∈ 𝒮 := by
  constructor
  · intro h
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp h
    have := (mem_cfCylinder_iff_cfWord hy w).mp hyw
    rw [hlen w hw] at this
    exact this ▸ hw
  · intro h
    refine Set.mem_iUnion₂.mpr ⟨cfWord y m, h, ?_⟩
    refine (mem_cfCylinder_iff_cfWord hy _).mpr ?_
    simp [cfWord]

/-- The digits of `Tᵐy` are the digits of `y` shifted by `m`. -/
lemma cfDigit_iterate (y : ℝ) (m i : ℕ) : cfDigit (gaussMap^[m] y) i = cfDigit y (m + i) := by
  rw [cfDigit, cfDigit, ← Function.iterate_add_apply, Nat.add_comm i m]

/-- The digit word of `Tᵐy` is the digit window of `y` at `m`. -/
lemma cfWord_iterate (y : ℝ) (m n : ℕ) : cfWord (gaussMap^[m] y) n = cfWindow y m n := by
  simp only [cfWord, cfWindow]
  exact List.map_congr_left fun i _ => cfDigit_iterate y m i

/-- The horizon set of a cylinder, read off the digit window.  Irrationality enters only to
keep the orbit inside `(0,1)`. -/
lemma mem_horizonSet_cfCylinder_iff {y : ℝ} (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (q : List ℕ) (k : ℕ) :
    y ∈ horizonSet (cfCylinder q) k ↔ q = cfWindow y k q.length := by
  obtain ⟨-, horb⟩ := irrational_orbit y hirr hy k
  rw [horizonSet]
  constructor
  · rintro ⟨-, hmem⟩
    have := (mem_cfCylinder_iff_cfWord horb q).mp hmem
    rwa [cfWord_iterate] at this
  · intro h
    refine ⟨hy, ?_⟩
    refine (mem_cfCylinder_iff_cfWord horb q).mpr ?_
    rwa [cfWord_iterate]

/-- Windows of `Tᵐy` are windows of `y`, shifted. -/
lemma cfWindow_iterate (y : ℝ) (m n ℓ : ℕ) :
    cfWindow (gaussMap^[m] y) n ℓ = cfWindow y (m + n) ℓ := by
  simp only [cfWindow]
  refine List.map_congr_left fun i _ => ?_
  rw [cfDigit_iterate y m (n + i), Nat.add_assoc]

lemma cfWord_length (y : ℝ) (n : ℕ) : (cfWord y n).length = n := by simp [cfWord]

/-- The automaton run over `W_{m+n}(y)` splits at `m`: the second half is read off `Tᵐy`. -/
lemma runState_cfWord_split {S : Type*} (δ : S → ℕ → S) (d : S) (y : ℝ) (m n : ℕ) :
    runState δ d (cfWord y (m + n))
      = runState δ (runState δ d (cfWord y m)) (cfWord (gaussMap^[m] y) n) := by
  rw [cfWord_add, runState_append, cfWord_iterate]

lemma cfWord_take (y : ℝ) (m k : ℕ) (h : k ≤ m) : (cfWord y m).take k = cfWord y k := by
  rw [← cfWindow_from_zero y m, cfWindow_take y 0 m k h, cfWindow_from_zero]

lemma cfWord_drop (y : ℝ) (m k : ℕ) (h : k ≤ m) :
    (cfWord y m).drop k = cfWindow y k (m - k) := by
  rw [← cfWindow_from_zero y m, cfWindow_drop y 0 m k h, Nat.zero_add]

/-! ## The two events, and the measurable representative of `jointDev` -/

namespace VandeheyTwo

open VandeheyState VandeheyMix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The window event at time `k`: the digits at `k, …, k+|q|−1` spell `q`. -/
noncomputable def winEvent (q : List ℕ) (k : ℕ) : Set ℝ := horizonSet (cfCylinder q) k

/-- The joint event at time `k`: the window spells `q` *and* the automaton, started at `d`,
sits at `t`. -/
noncomputable def jointEvent (δ : S → ℕ → S) (d t : S) (q : List ℕ) (k : ℕ) : Set ℝ :=
  stateHorizonSet δ (cfCylinder q) k d t

lemma measurableSet_winEvent (q : List ℕ) (k : ℕ) : MeasurableSet (winEvent q k) :=
  measurableSet_horizonSet (measurableSet_cfCylinder q) k

lemma measurableSet_jointEvent (δ : S → ℕ → S) (d t : S) (q : List ℕ) (k : ℕ) :
    MeasurableSet (jointEvent δ d t q k) :=
  measurableSet_stateHorizonSet (measurableSet_cfCylinder q) δ k d t

omit [Fintype S] [DecidableEq S] in
lemma jointEvent_subset_winEvent (δ : S → ℕ → S) (d t : S) (q : List ℕ) (k : ℕ) :
    jointEvent δ d t q k ⊆ winEvent q k := fun _ hy => hy.1

omit [Fintype S] [DecidableEq S] in
lemma mem_winEvent_iff {y : ℝ} (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (q : List ℕ) (k : ℕ) : y ∈ winEvent q k ↔ q = cfWindow y k q.length :=
  mem_horizonSet_cfCylinder_iff hirr hy q k

omit [Fintype S] [DecidableEq S] in
lemma mem_jointEvent_iff (δ : S → ℕ → S) (d t : S) {y : ℝ} (hirr : Irrational y)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (q : List ℕ) (k : ℕ) :
    y ∈ jointEvent δ d t q k ↔ q = cfWindow y k q.length ∧ stateAt δ d y k = t := by
  rw [jointEvent, stateHorizonSet]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_winEvent_iff hirr hy q k).mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_winEvent_iff hirr hy q k).mpr h1, h2⟩

/-- The measurable representative of `VandeheyCocycle.jointDev`. -/
noncomputable def devFun (δ : S → ℕ → S) (d t : S) (q : List ℕ) (L : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (jointEvent δ d t q k).indicator (fun _ => (1 : ℝ)) y
    - L * (winEvent q k).indicator (fun _ => (1 : ℝ)) y

lemma measurable_devFun (δ : S → ℕ → S) (d t : S) (q : List ℕ) (L : ℝ) (k : ℕ) :
    Measurable (devFun δ d t q L k) :=
  (measurable_const.indicator (measurableSet_jointEvent δ d t q k)).sub
    (measurable_const.mul (measurable_const.indicator (measurableSet_winEvent q k)))

omit [Fintype S] [DecidableEq S] in
lemma abs_devFun_le (δ : S → ℕ → S) (d t : S) (q : List ℕ) {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (k : ℕ) (y : ℝ) : |devFun δ d t q L k y| ≤ 1 := by
  rw [devFun]
  by_cases hw : y ∈ winEvent q k
  · rw [Set.indicator_of_mem hw]
    by_cases hj : y ∈ jointEvent δ d t q k
    · rw [Set.indicator_of_mem hj, abs_le]; constructor <;> nlinarith
    · rw [Set.indicator_of_notMem hj, abs_le]; constructor <;> nlinarith
  · have hj : y ∉ jointEvent δ d t q k :=
      fun hc => hw (jointEvent_subset_winEvent δ d t q k hc)
    rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hj, abs_le]
    constructor <;> nlinarith

omit [Fintype S] in
/-- **`devFun` represents `jointDev`.**  They agree at every irrational point of `(0,1)`. -/
lemma jointDev_eq_devFun (δ : S → ℕ → S) (d t : S) (q : List ℕ) (L : ℝ) (k : ℕ)
    {y : ℝ} (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    VandeheyCocycle.jointDev δ d t q L y k = devFun δ d t q L k y := by
  classical
  rw [VandeheyCocycle.jointDev, devFun]
  by_cases hw : q = cfWindow y k q.length
  · have hwin : y ∈ winEvent q k := (mem_winEvent_iff hirr hy q k).mpr hw
    rw [if_pos hw, Set.indicator_of_mem hwin]
    by_cases hst : stateAt δ d y k = t
    · rw [if_pos hst,
        Set.indicator_of_mem ((mem_jointEvent_iff δ d t hirr hy q k).mpr ⟨hw, hst⟩)]
      ring
    · rw [if_neg hst,
        Set.indicator_of_notMem
          (fun hj => hst ((mem_jointEvent_iff δ d t hirr hy q k).mp hj).2)]
      ring
  · have hwin : y ∉ winEvent q k := fun hc => hw ((mem_winEvent_iff hirr hy q k).mp hc)
    rw [if_neg hw, Set.indicator_of_notMem hwin,
      Set.indicator_of_notMem (fun hj => hwin (jointEvent_subset_winEvent δ d t q k hj))]
    ring

/-! ## Shifting the events along the orbit -/

omit [Fintype S] [DecidableEq S] in
/-- The window event at `m + n`, read from `Tᵐy`. -/
lemma mem_iterate_horizonSet_iff (q : List ℕ) {y : ℝ} (hirr : Irrational y)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (m n : ℕ) :
    gaussMap^[m] y ∈ horizonSet (cfCylinder q) n ↔ y ∈ winEvent q (m + n) := by
  obtain ⟨hirr', horb⟩ := irrational_orbit y hirr hy m
  rw [mem_horizonSet_cfCylinder_iff hirr' horb q n, cfWindow_iterate,
    mem_winEvent_iff hirr hy q (m + n)]

omit [Fintype S] [DecidableEq S] in
/-- The joint event at `m + n`, read from `Tᵐy` with the automaton restarted at the state it
reaches after the first `m` digits.  This is the cocycle identity in set form. -/
lemma mem_iterate_stateHorizonSet_iff (δ : S → ℕ → S) (d t : S) (q : List ℕ) {y : ℝ}
    (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (m n : ℕ) :
    gaussMap^[m] y ∈ stateHorizonSet δ (cfCylinder q) n (runState δ d (cfWord y m)) t
      ↔ y ∈ jointEvent δ d t q (m + n) := by
  obtain ⟨hirr', horb⟩ := irrational_orbit y hirr hy m
  rw [stateHorizonSet, mem_jointEvent_iff δ d t hirr hy q (m + n)]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq] at h2
    refine ⟨?_, ?_⟩
    · have := (mem_horizonSet_cfCylinder_iff hirr' horb q n).mp h1
      rwa [cfWindow_iterate] at this
    · rw [stateAt, runState_cfWord_split]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · refine (mem_horizonSet_cfCylinder_iff hirr' horb q n).mpr ?_
      rwa [cfWindow_iterate]
    · simp only [Set.mem_ofPred_eq]
      rw [stateAt, runState_cfWord_split] at h2
      exact h2

/-! ## The past families -/

/-- Genuine words of length `k + |q|` that put `q` at position `k`. -/
def pastWin (q : List ℕ) (k : ℕ) : Set (List ℕ) :=
  {v | v.length = k + q.length ∧ (∀ a ∈ v, 1 ≤ a) ∧ q = v.drop k}

/-- The words of `pastWin` that additionally drive the automaton from `d` to `t` in `k` steps. -/
def pastJoint (δ : S → ℕ → S) (d t : S) (q : List ℕ) (k : ℕ) : Set (List ℕ) :=
  {v | v ∈ pastWin q k ∧ runState δ d (v.take k) = t}

lemma pastWin_len {q : List ℕ} {k : ℕ} : ∀ v ∈ pastWin q k, v.length = k + q.length :=
  fun _ hv => hv.1

lemma pastWin_pos {q : List ℕ} {k : ℕ} : ∀ v ∈ pastWin q k, ∀ a ∈ v, 1 ≤ a :=
  fun _ hv => hv.2.1

omit [Fintype S] [DecidableEq S] in
lemma pastJoint_subset (δ : S → ℕ → S) (d t : S) (q : List ℕ) (k : ℕ) :
    pastJoint δ d t q k ⊆ pastWin q k := fun _ hv => hv.1

omit [Fintype S] [DecidableEq S] in
lemma pastJoint_len (δ : S → ℕ → S) (d t : S) {q : List ℕ} {k : ℕ} :
    ∀ v ∈ pastJoint δ d t q k, v.length = k + q.length := fun _ hv => hv.1.1

omit [Fintype S] [DecidableEq S] in
lemma pastJoint_pos (δ : S → ℕ → S) (d t : S) {q : List ℕ} {k : ℕ} :
    ∀ v ∈ pastJoint δ d t q k, ∀ a ∈ v, 1 ≤ a := fun _ hv => hv.1.2.1

omit [Fintype S] [DecidableEq S] in
/-- The window event *is* a countable union of same-length cylinders. -/
lemma winEvent_ae_eq (q : List ℕ) (k : ℕ) :
    winEvent q k =ᵐ[gaussMeasure] familySetC (pastWin q k) := by
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [ae_irrational, ae_mem_Ioo] with y hirr hy
  rw [mem_winEvent_iff hirr hy q k,
    mem_familySetC_iff_cfWord (pastWin_len (q := q) (k := k)) hy]
  constructor
  · intro h
    refine ⟨cfWord_length y _, ?_, ?_⟩
    · intro a ha
      simp only [cfWord, List.mem_map, List.mem_range] at ha
      obtain ⟨i, -, hi⟩ := ha
      rw [← hi]; exact one_le_cfDigit y hirr hy i
    · rw [cfWord_drop y (k + q.length) k (by omega)]
      simpa using h
  · rintro ⟨-, -, h⟩
    rw [cfWord_drop y (k + q.length) k (by omega)] at h
    simpa using h

omit [Fintype S] [DecidableEq S] in
/-- The joint event *is* a countable union of same-length cylinders. -/
lemma jointEvent_ae_eq (δ : S → ℕ → S) (d t : S) (q : List ℕ) (k : ℕ) :
    jointEvent δ d t q k =ᵐ[gaussMeasure] familySetC (pastJoint δ d t q k) := by
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [ae_irrational, ae_mem_Ioo] with y hirr hy
  rw [mem_jointEvent_iff δ d t hirr hy q k,
    mem_familySetC_iff_cfWord (pastJoint_len δ d t (q := q) (k := k)) hy]
  have hdrop : (cfWord y (k + q.length)).drop k = cfWindow y k q.length := by
    rw [cfWord_drop y (k + q.length) k (by omega)]; simp
  have htake : (cfWord y (k + q.length)).take k = cfWord y k :=
    cfWord_take y (k + q.length) k (by omega)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨cfWord_length y _, ?_, ?_⟩, ?_⟩
    · intro a ha
      simp only [cfWord, List.mem_map, List.mem_range] at ha
      obtain ⟨i, -, hi⟩ := ha
      rw [← hi]; exact one_le_cfDigit y hirr hy i
    · rw [hdrop]; exact h1
    · rw [htake]; exact h2
  · rintro ⟨⟨-, -, h1⟩, h2⟩
    rw [hdrop] at h1
    rw [htake] at h2
    exact ⟨h1, h2⟩

/-! ## Shifting the second event past the first -/

omit [Fintype S] [DecidableEq S] in
lemma winEvent_shift_ae_eq (q : List ℕ) (m n : ℕ) :
    (winEvent q (m + n) : Set ℝ)
      =ᵐ[gaussMeasure] ((gaussMap^[m]) ⁻¹' horizonSet (cfCylinder q) n : Set ℝ) := by
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [ae_irrational, ae_mem_Ioo] with y hirr hy
  exact (mem_iterate_horizonSet_iff q hirr hy m n).symm

omit [Fintype S] [DecidableEq S] in
lemma inter_winEvent_ae_eq (q : List ℕ) {E : Set ℝ} {𝒱 : Set (List ℕ)} {m : ℕ}
    (hE : E =ᵐ[gaussMeasure] familySetC 𝒱) (n : ℕ) :
    (E ∩ winEvent q (m + n) : Set ℝ)
      =ᵐ[gaussMeasure]
        (familySetC 𝒱 ∩ (gaussMap^[m]) ⁻¹' horizonSet (cfCylinder q) n : Set ℝ) := by
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [Filter.eventuallyEq_set.mp hE,
    Filter.eventuallyEq_set.mp (winEvent_shift_ae_eq q m n)] with y h1 h2
  rw [Set.mem_inter_iff, Set.mem_inter_iff, h1, h2]

omit [Fintype S] [DecidableEq S] in
/-- **The load-bearing identification.**  A past event that is a countable union of length-`m`
cylinders, intersected with the joint event at `m + n`, is the *past-dependent* union the brick
`abs_gaussMeasure_biUnion_state_sub_le` eats: each cylinder `I_v` paired with the future event
read from `runState δ d v`. -/
lemma inter_jointEvent_ae_eq (δ : S → ℕ → S) (d t : S) (q : List ℕ) {E : Set ℝ}
    {𝒱 : Set (List ℕ)} {m : ℕ} (hlen : ∀ w ∈ 𝒱, w.length = m)
    (hE : E =ᵐ[gaussMeasure] familySetC 𝒱) (n : ℕ) :
    (E ∩ jointEvent δ d t q (m + n) : Set ℝ)
      =ᵐ[gaussMeasure] (⋃ v ∈ 𝒱, cfCylinder v ∩ (gaussMap^[m]) ⁻¹'
        stateHorizonSet δ (cfCylinder q) n (runState δ d v) t : Set ℝ) := by
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [ae_irrational, ae_mem_Ioo, Filter.eventuallyEq_set.mp hE] with y hirr hy hEy
  rw [Set.mem_inter_iff, hEy, mem_familySetC_iff_cfWord hlen hy,
    ← mem_iterate_stateHorizonSet_iff δ d t q hirr hy m n]
  constructor
  · rintro ⟨h1, h2⟩
    exact Set.mem_iUnion₂.mpr ⟨cfWord y m, h1,
      ⟨(mem_cfCylinder_iff_cfWord hy _).mpr (by rw [cfWord_length]), h2⟩⟩
  · intro h
    obtain ⟨v, hv, hmem⟩ := Set.mem_iUnion₂.mp h
    have hvw : v = cfWord y m := by
      have := (mem_cfCylinder_iff_cfWord hy v).mp hmem.1
      rwa [hlen v hv] at this
    exact ⟨hvw ▸ hv, by rw [← hvw]; exact hmem.2⟩

/-! ## The four measures, and the correlation bound -/

omit [Fintype S] [DecidableEq S] in
lemma ind_mul_ind (A B : Set ℝ) (y : ℝ) :
    A.indicator (fun _ => (1 : ℝ)) y * B.indicator (fun _ => (1 : ℝ)) y
      = (A ∩ B).indicator (fun _ => (1 : ℝ)) y := by
  rw [← Set.inter_indicator_mul]
  simp

private lemma integrable_ind {E : Set ℝ} (hE : MeasurableSet E) :
    Integrable (E.indicator (fun _ => (1 : ℝ))) gaussMeasure :=
  (integrable_const (1 : ℝ)).indicator hE

/-- The product of two `devFun`s integrates to the four joint masses. -/
lemma integral_devFun_mul (δ : S → ℕ → S) (d t : S) (q : List ℕ) (L : ℝ) (k k' : ℕ) :
    ∫ y, devFun δ d t q L k y * devFun δ d t q L k' y ∂gaussMeasure
      = (gaussMeasure (jointEvent δ d t q k ∩ jointEvent δ d t q k')).toReal
        - L * (gaussMeasure (jointEvent δ d t q k ∩ winEvent q k')).toReal
        - L * (gaussMeasure (winEvent q k ∩ jointEvent δ d t q k')).toReal
        + L ^ 2 * (gaussMeasure (winEvent q k ∩ winEvent q k')).toReal := by
  set J := jointEvent δ d t q k with hJdef
  set J' := jointEvent δ d t q k' with hJ'def
  set W := winEvent q k with hWdef
  set W' := winEvent q k' with hW'def
  have hJm : MeasurableSet J := measurableSet_jointEvent δ d t q k
  have hJ'm : MeasurableSet J' := measurableSet_jointEvent δ d t q k'
  have hWm : MeasurableSet W := measurableSet_winEvent q k
  have hW'm : MeasurableSet W' := measurableSet_winEvent q k'
  set f1 : ℝ → ℝ := (J ∩ J').indicator (fun _ => (1 : ℝ)) with hf1
  set f2 : ℝ → ℝ := (J ∩ W').indicator (fun _ => (1 : ℝ)) with hf2
  set f3 : ℝ → ℝ := (W ∩ J').indicator (fun _ => (1 : ℝ)) with hf3
  set f4 : ℝ → ℝ := (W ∩ W').indicator (fun _ => (1 : ℝ)) with hf4
  have i1 : Integrable f1 gaussMeasure := integrable_ind (hJm.inter hJ'm)
  have i2 : Integrable f2 gaussMeasure := integrable_ind (hJm.inter hW'm)
  have i3 : Integrable f3 gaussMeasure := integrable_ind (hWm.inter hJ'm)
  have i4 : Integrable f4 gaussMeasure := integrable_ind (hWm.inter hW'm)
  have hE1 : ∫ y, f1 y ∂gaussMeasure = (gaussMeasure (J ∩ J')).toReal := by
    rw [hf1, integral_indicator_const (1:ℝ) (hJm.inter hJ'm), measureReal_def, smul_eq_mul, mul_one]
  have hE2 : ∫ y, f2 y ∂gaussMeasure = (gaussMeasure (J ∩ W')).toReal := by
    rw [hf2, integral_indicator_const (1:ℝ) (hJm.inter hW'm), measureReal_def, smul_eq_mul, mul_one]
  have hE3 : ∫ y, f3 y ∂gaussMeasure = (gaussMeasure (W ∩ J')).toReal := by
    rw [hf3, integral_indicator_const (1:ℝ) (hWm.inter hJ'm), measureReal_def, smul_eq_mul, mul_one]
  have hE4 : ∫ y, f4 y ∂gaussMeasure = (gaussMeasure (W ∩ W')).toReal := by
    rw [hf4, integral_indicator_const (1:ℝ) (hWm.inter hW'm), measureReal_def, smul_eq_mul, mul_one]
  have hpt : ∀ y : ℝ, devFun δ d t q L k y * devFun δ d t q L k' y
      = f1 y - L * f2 y - L * f3 y + L ^ 2 * f4 y := by
    intro y
    simp only [devFun, hf1, hf2, hf3, hf4, ← ind_mul_ind, hJdef, hJ'def, hWdef, hW'def]
    ring
  have s1 := integral_add (μ := gaussMeasure)
    (f := fun y => f1 y - L * f2 y - L * f3 y) (g := fun y => L ^ 2 * f4 y)
    ((i1.sub (i2.const_mul L)).sub (i3.const_mul L)) (i4.const_mul (L ^ 2))
  have s2 := integral_sub (μ := gaussMeasure)
    (f := fun y => f1 y - L * f2 y) (g := fun y => L * f3 y)
    (i1.sub (i2.const_mul L)) (i3.const_mul L)
  have s3 := integral_sub (μ := gaussMeasure) (f := fun y => f1 y) (g := fun y => L * f2 y)
    i1 (i2.const_mul L)
  calc ∫ y, devFun δ d t q L k y * devFun δ d t q L k' y ∂gaussMeasure
      = ∫ y, (f1 y - L * f2 y - L * f3 y + L ^ 2 * f4 y) ∂gaussMeasure := by
        simp only [hpt]
    _ = (gaussMeasure (J ∩ J')).toReal - L * (gaussMeasure (J ∩ W')).toReal
          - L * (gaussMeasure (W ∩ J')).toReal + L ^ 2 * (gaussMeasure (W ∩ W')).toReal := by
        rw [s1, s2, s3, integral_const_mul, integral_const_mul, integral_const_mul,
          hE1, hE2, hE3, hE4]

/-! ## The correlation bound -/

private lemma gaussMeasure_toReal_le_one (X : Set ℝ) : (gaussMeasure X).toReal ≤ 1 := by
  have h : gaussMeasure X ≤ 1 := prob_le_one
  have := ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) h
  simpa using this

/-- **The two-point correlation bound.**  With `k' = k + |q| + n`, the four joint masses combine
so that the leading terms cancel **exactly** when `L` is the pin's constant `c`: the `𝒥`-terms
cancel against each other and so do the `𝒲`-terms.  What is left is a pure geometric remainder
in the gap `n`. -/
theorem abs_integral_devFun_mul_le (δ : S → ℕ → S) (d t : S) (q : List ℕ)
    {c C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hpin : ∀ (n : ℕ) (e s : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ (cfCylinder q) n e s τ
          - c * (gaussMeasure (cfCylinder q)).toReal|
        ≤ C * θ ^ n * (gaussMeasure (cfCylinder q)).toReal)
    (k n : ℕ) :
    |∫ y, devFun δ d t q c k y * devFun δ d t q c (k + q.length + n) y ∂gaussMeasure|
      ≤ 2 * (C + 1) * max θ (79 / 100) ^ n * (gaussMeasure (cfCylinder q)).toReal := by
  classical
  set γq : ℝ := (gaussMeasure (cfCylinder q)).toReal with hγq
  have hγq0 : 0 ≤ γq := ENNReal.toReal_nonneg
  set ρ : ℝ := max θ (79 / 100) with hρdef
  have hρ0 : 0 ≤ ρ := le_trans hθ0 (le_max_left _ _)
  have hθρ : θ ^ n ≤ ρ ^ n := pow_le_pow_left₀ hθ0 (le_max_left _ _) n
  have hρ'ρ : (79 / 100 : ℝ) ^ n ≤ ρ ^ n :=
    pow_le_pow_left₀ (by norm_num) (le_max_right _ _) n
  set m : ℕ := k + q.length with hm
  set 𝒥 : Set (List ℕ) := pastJoint δ d t q k with h𝒥
  set 𝒲 : Set (List ℕ) := pastWin q k with h𝒲
  set PJ : ℝ := (gaussMeasure (familySetC 𝒥)).toReal with hPJ
  set PW : ℝ := (gaussMeasure (familySetC 𝒲)).toReal with hPW
  have hPJ0 : 0 ≤ PJ := ENNReal.toReal_nonneg
  have hPW0 : 0 ≤ PW := ENNReal.toReal_nonneg
  have hPJ1 : PJ ≤ 1 := gaussMeasure_toReal_le_one _
  have hPW1 : PW ≤ 1 := gaussMeasure_toReal_le_one _
  have hqm : MeasurableSet (cfCylinder q) := measurableSet_cfCylinder q
  have hq1 : cfCylinder q ⊆ Set.Ioo (0 : ℝ) 1 := cfCylinder_subset_Ioo q
  -- the unrefined pin, in the form the family brick wants
  have hpin' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |(∫ y in horizonSet (cfCylinder q) n, tailDensity τ y) - γq| ≤ (79 / 100) ^ n * γq :=
    fun τ hτ => horizonIntegral_pin_geom hqm hq1 n hτ
  -- the four joint masses
  have hT1 : |(gaussMeasure (jointEvent δ d t q k ∩ jointEvent δ d t q (m + n))).toReal
      - c * γq * PJ| ≤ C * θ ^ n * γq * PJ := by
    rw [measure_congr (inter_jointEvent_ae_eq δ d t q (pastJoint_len δ d t) (jointEvent_ae_eq δ d t q k) n)]
    exact abs_gaussMeasure_biUnion_state_sub_le δ hqm hpin n d t (Set.to_countable _)
      (pastJoint_len δ d t) (pastJoint_pos δ d t)
  have hT2 : |(gaussMeasure (jointEvent δ d t q k ∩ winEvent q (m + n))).toReal
      - γq * PJ| ≤ (79 / 100) ^ n * γq * PJ := by
    rw [measure_congr (inter_winEvent_ae_eq q (jointEvent_ae_eq δ d t q k) n)]
    exact abs_gaussMeasure_familySetC_inter_sub_le (Set.to_countable _)
      (pastJoint_len δ d t) (pastJoint_pos δ d t)
      (measurableSet_horizonSet hqm n) (horizonSet_subset _ n) hpin'
  have hT3 : |(gaussMeasure (winEvent q k ∩ jointEvent δ d t q (m + n))).toReal
      - c * γq * PW| ≤ C * θ ^ n * γq * PW := by
    rw [measure_congr (inter_jointEvent_ae_eq δ d t q (pastWin_len) (winEvent_ae_eq q k) n)]
    exact abs_gaussMeasure_biUnion_state_sub_le δ hqm hpin n d t (Set.to_countable _)
      pastWin_len pastWin_pos
  have hT4 : |(gaussMeasure (winEvent q k ∩ winEvent q (m + n))).toReal
      - γq * PW| ≤ (79 / 100) ^ n * γq * PW := by
    rw [measure_congr (inter_winEvent_ae_eq q (winEvent_ae_eq q k) n)]
    exact abs_gaussMeasure_familySetC_inter_sub_le (Set.to_countable _)
      pastWin_len pastWin_pos (measurableSet_horizonSet hqm n) (horizonSet_subset _ n) hpin'
  -- the exact cancellation
  set T1 : ℝ := (gaussMeasure (jointEvent δ d t q k ∩ jointEvent δ d t q (m + n))).toReal with hT1d
  set T2 : ℝ := (gaussMeasure (jointEvent δ d t q k ∩ winEvent q (m + n))).toReal with hT2d
  set T3 : ℝ := (gaussMeasure (winEvent q k ∩ jointEvent δ d t q (m + n))).toReal with hT3d
  set T4 : ℝ := (gaussMeasure (winEvent q k ∩ winEvent q (m + n))).toReal with hT4d
  have hid : ∫ y, devFun δ d t q c k y * devFun δ d t q c (m + n) y ∂gaussMeasure
      = (T1 - c * γq * PJ) - c * (T2 - γq * PJ) - c * (T3 - c * γq * PW)
        + c ^ 2 * (T4 - γq * PW) := by
    rw [integral_devFun_mul δ d t q c k (m + n), ← hT1d, ← hT2d, ← hT3d, ← hT4d]
    ring
  -- collapse each term to `K·ρⁿ·γq`
  have hstep : ∀ K a P X : ℝ, 0 ≤ K → 0 ≤ a → a ≤ ρ → 0 ≤ P → P ≤ 1 →
      X ≤ K * a ^ n * γq * P → X ≤ K * ρ ^ n * γq := by
    intro K a P X hK ha haρ hP hP1 hle
    have h1 : a ^ n ≤ ρ ^ n := pow_le_pow_left₀ ha haρ n
    have h2 : K * a ^ n * γq ≤ K * ρ ^ n * γq :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hγq0
    have h3 : (0 : ℝ) ≤ K * ρ ^ n * γq :=
      mul_nonneg (mul_nonneg hK (pow_nonneg hρ0 n)) hγq0
    calc X ≤ K * a ^ n * γq * P := hle
      _ ≤ K * ρ ^ n * γq * 1 := by
          refine mul_le_mul h2 hP1 hP h3
      _ = K * ρ ^ n * γq := by ring
  have b1 : |T1 - c * γq * PJ| ≤ C * ρ ^ n * γq :=
    hstep C θ PJ _ hC hθ0 (le_max_left _ _) hPJ0 hPJ1 hT1
  have b2 : |T2 - γq * PJ| ≤ 1 * ρ ^ n * γq := by
    refine hstep 1 (79 / 100) PJ _ zero_le_one (by norm_num) (le_max_right _ _) hPJ0 hPJ1 ?_
    simpa using hT2
  have b3 : |T3 - c * γq * PW| ≤ C * ρ ^ n * γq :=
    hstep C θ PW _ hC hθ0 (le_max_left _ _) hPW0 hPW1 hT3
  have b4 : |T4 - γq * PW| ≤ 1 * ρ ^ n * γq := by
    refine hstep 1 (79 / 100) PW _ zero_le_one (by norm_num) (le_max_right _ _) hPW0 hPW1 ?_
    simpa using hT4
  -- assemble
  have htri : |(T1 - c * γq * PJ) - c * (T2 - γq * PJ) - c * (T3 - c * γq * PW)
        + c ^ 2 * (T4 - γq * PW)|
      ≤ |T1 - c * γq * PJ| + |c * (T2 - γq * PJ)| + |c * (T3 - c * γq * PW)|
        + |c ^ 2 * (T4 - γq * PW)| := by
    have e1 := abs_add_le ((T1 - c * γq * PJ) - c * (T2 - γq * PJ) - c * (T3 - c * γq * PW))
      (c ^ 2 * (T4 - γq * PW))
    have e2 := abs_sub ((T1 - c * γq * PJ) - c * (T2 - γq * PJ)) (c * (T3 - c * γq * PW))
    have e3 := abs_sub (T1 - c * γq * PJ) (c * (T2 - γq * PJ))
    linarith
  have hc2 : |c * (T2 - γq * PJ)| ≤ 1 * ρ ^ n * γq := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |T2 - γq * PJ| ≤ 1 * |T2 - γq * PJ| :=
          mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ = |T2 - γq * PJ| := one_mul _
      _ ≤ 1 * ρ ^ n * γq := b2
  have hc3 : |c * (T3 - c * γq * PW)| ≤ C * ρ ^ n * γq := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |T3 - c * γq * PW| ≤ 1 * |T3 - c * γq * PW| :=
          mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ = |T3 - c * γq * PW| := one_mul _
      _ ≤ C * ρ ^ n * γq := b3
  have hc4 : |c ^ 2 * (T4 - γq * PW)| ≤ 1 * ρ ^ n * γq := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ 2)]
    have hcsq : c ^ 2 ≤ 1 := by nlinarith
    calc c ^ 2 * |T4 - γq * PW| ≤ 1 * |T4 - γq * PW| :=
          mul_le_mul_of_nonneg_right hcsq (abs_nonneg _)
      _ = |T4 - γq * PW| := one_mul _
      _ ≤ 1 * ρ ^ n * γq := b4
  rw [hid]
  calc |(T1 - c * γq * PJ) - c * (T2 - γq * PJ) - c * (T3 - c * γq * PW)
        + c ^ 2 * (T4 - γq * PW)|
      ≤ |T1 - c * γq * PJ| + |c * (T2 - γq * PJ)| + |c * (T3 - c * γq * PW)|
        + |c ^ 2 * (T4 - γq * PW)| := htri
    _ ≤ C * ρ ^ n * γq + 1 * ρ ^ n * γq + C * ρ ^ n * γq + 1 * ρ ^ n * γq := by
        linarith [b1, hc2, hc3, hc4]
    _ = 2 * (C + 1) * ρ ^ n * γq := by ring

end VandeheyTwo

end NormalNumbers
