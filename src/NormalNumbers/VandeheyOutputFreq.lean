/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyClassEquidist
import NormalNumbers.VandeheyRenewal

/-!
# Vandehey §4.3 + §5 + §6, abstract: output frequencies from joint (window, state) frequencies

This is the **output** half of Vandehey 2017 Theorem 1.1, and it is transducer-free.  The
input half — Raney normal forms (§2), the skew product (§3), transitive components (§4) —
supplies exactly one thing: for every genuine window `q` and every state `t`, the joint
frequency

  `#{i < n : the digit window of x at i spells q, and the automaton is in state t at i} / n`

converges to an `x`-independent limit.  Our engine
(`VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`) delivers that limit in
**factorized** form `ν t · γ(I_q)`: the state at time `i` reads the past, the window reads
the future, and the ψ-mixing of the Gauss map decouples them.  That is strictly stronger
than Vandehey's Remark 3.6 (`ρ ≪≫ μ̃`, no product structure), and the strength is what makes
this file elementary: countable additivity of `ρ` reduces to countable additivity of `γ`.

## What §5–§6 actually needs

A *trigger* for an output word `r` is a pair `(q, t)`: reading the genuine word `q` from
state `t` emits an output block in which `r` appears "nicely" (away from both ends), with
`q` minimal.  Vandehey's §5 shows the number of occurrences of `r` in the output of the
first `n` input digits equals, up to `O(1)`, the number of positions `i < n` at which some
trigger fires, counted with multiplicity.  Triggers are **not** of bounded length (the paper
says so, and says it does not know whether they are), so the count is an infinite sum of
window-state indicators; §6 controls it by the approximants `F_j^±`.

The engine here is the upper bound for such an infinite sum:

* `limsup_weighted_le` — for weights `a` supported on the length-`m` genuine words,
  `limsup (1/n) Σ_{i<n} a(wᵢ)·1[tᵢ = t] ≤ ν t · Σ_w a(w) γ(I_w)`.

The escape from the infinite alphabet is a **finite** subfamily of `allWords m` carrying
almost all the Gauss mass (`exists_boundedWords_sum_gt`), which is the elementary stand-in
for the Airey–Mance tightness patch the published §3 needs.  Together with the trivial
truncation lower bound this gives Vandehey's Lemma 4.3 without any soft analysis.

## Status

* Step 0 (this file, kernel): the length-`m` word partition carries full Gauss mass, and a
  finite digit-truncated subfamily carries `> 1 − ε` of it.
* Step 1: the weighted upper-bound engine.
* Step 2: the assembly (bucket the trigger family by length, `K·1` above the cut).
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut VandeheyMix VandeheyRenewal

namespace VandeheyOut

/-! ## Step 0: the length-`m` genuine words carry full Gauss mass -/

/-- A genuine word is in `allWords` of its own length. -/
lemma cfWord_mem_allWords {y : ℝ} (hirr : Irrational y) (hy : y ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    cfWord y m ∈ allWords m := by
  refine ⟨cfWord_length y m, ?_⟩
  intro a ha
  simp only [cfWord, List.mem_map, List.mem_range] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact one_le_cfDigit y hirr hy i

lemma subset_allWordsEvent {m : ℕ} :
    {y : ℝ | Irrational y ∧ y ∈ Set.Ioo (0 : ℝ) 1} ⊆ allWordsEvent m := by
  rintro y ⟨hirr, hy⟩
  refine (mem_familySetC_iff_cfWord (m := m) (fun w hw => hw.1) hy).mpr ?_
  exact cfWord_mem_allWords hirr hy m

/-- **The length-`m` partition is full.**  Almost every point has `m` genuine digits, so the
length-`m` cylinders exhaust the Gauss measure. -/
theorem gaussMeasure_allWordsEvent (m : ℕ) : gaussMeasure (allWordsEvent m) = 1 := by
  have hae : ∀ᵐ y ∂gaussMeasure, y ∈ allWordsEvent m := by
    filter_upwards [ae_irrational, ae_mem_Ioo] with y hirr hy
    exact subset_allWordsEvent ⟨hirr, hy⟩
  have hnull : gaussMeasure (allWordsEvent m)ᶜ = 0 := by
    rw [MeasureTheory.ae_iff] at hae
    exact hae
  refine le_antisymm ?_ ?_
  · rw [← gaussMeasure_univ]; exact measure_mono (Set.subset_univ _)
  · calc (1 : ENNReal) = gaussMeasure Set.univ := gaussMeasure_univ.symm
      _ = gaussMeasure (allWordsEvent m ∪ (allWordsEvent m)ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ gaussMeasure (allWordsEvent m) + gaussMeasure (allWordsEvent m)ᶜ :=
          measure_union_le _ _
      _ = gaussMeasure (allWordsEvent m) := by rw [hnull, add_zero]

/-! ## The finite digit-truncated subfamilies -/

/-- The union of the cylinders of the length-`m` words with all digits in `[1, B]`. -/
noncomputable def boundedWordsEvent (B m : ℕ) : Set ℝ := familySetC ↑(boundedWords B m)

lemma boundedWords_subset_allWords (B m : ℕ) :
    ↑(boundedWords B m) ⊆ allWords m := by
  intro w hw
  have h := mem_boundedWords.mp (by simpa using hw)
  exact ⟨h.1, fun a ha => (h.2 a ha).1⟩

lemma boundedWords_mono {B B' : ℕ} (h : B ≤ B') (m : ℕ) :
    (boundedWords B m : Set (List ℕ)) ⊆ ↑(boundedWords B' m) := by
  intro w hw
  have hw' := mem_boundedWords.mp (by simpa using hw)
  have : w ∈ boundedWords B' m :=
    mem_boundedWords.mpr ⟨hw'.1, fun a ha => ⟨(hw'.2 a ha).1, (hw'.2 a ha).2.trans h⟩⟩
  simpa using this

lemma boundedWordsEvent_mono (m : ℕ) : Monotone fun B => boundedWordsEvent B m := by
  intro B B' h
  exact Set.biUnion_subset_biUnion_left (boundedWords_mono h m)

lemma iUnion_boundedWordsEvent (m : ℕ) :
    (⋃ B : ℕ, boundedWordsEvent B m) = allWordsEvent m := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun B => ?_) ?_
  · exact Set.biUnion_subset_biUnion_left (boundedWords_subset_allWords B m)
  · intro y hy
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
    refine Set.mem_iUnion.mpr ⟨w.sum, Set.mem_iUnion₂.mpr ⟨w, ?_, hyw⟩⟩
    have : w ∈ boundedWords w.sum m :=
      mem_boundedWords.mpr ⟨hw.1, fun a ha =>
        ⟨hw.2 a ha, List.single_le_sum (fun x _ => Nat.zero_le x) a ha⟩⟩
    simpa using this

/-- **The digit truncation is tight.**  The finite length-`m` families `boundedWords B m`
carry Gauss mass tending to `1`. -/
theorem tendsto_gaussMeasure_boundedWordsEvent (m : ℕ) :
    Tendsto (fun B => gaussMeasure (boundedWordsEvent B m)) atTop (nhds 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := gaussMeasure)
    (boundedWordsEvent_mono m)
  rw [iUnion_boundedWordsEvent m, gaussMeasure_allWordsEvent m] at h
  exact h

/-- Masses add over a finite same-length family. -/
lemma gaussMeasure_boundedWordsEvent_eq_sum (B m : ℕ) :
    gaussMeasure (boundedWordsEvent B m)
      = ∑ w ∈ boundedWords B m, gaussMeasure (cfCylinder w) := by
  have hdisj : (↑(boundedWords B m) : Set (List ℕ)).PairwiseDisjoint
      (fun w => cfCylinder w) :=
    pairwiseDisjoint_cfCylinder (n := m) (fun w hw => (boundedWords_subset_allWords B m hw).1)
  have := measure_biUnion_finset (μ := gaussMeasure) hdisj
    (fun w _ => measurableSet_cfCylinder w)
  simpa [boundedWordsEvent, familySetC] using this

/-- **The finite escape.**  For every `ε > 0` there is a digit bound `B` for which the finite
family `boundedWords B m` already carries real Gauss mass `> 1 − ε`.  This replaces the
tightness hypothesis that the published §3 needs. -/
theorem exists_boundedWords_sum_gt (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 - ε < ∑ w ∈ boundedWords B m, (gaussMeasure (cfCylinder w)).toReal := by
  have h := tendsto_gaussMeasure_boundedWordsEvent m
  have hreal : Tendsto (fun B => (gaussMeasure (boundedWordsEvent B m)).toReal) atTop
      (nhds 1) := by
    have h2 := (ENNReal.tendsto_toReal (a := (1 : ENNReal)) (by simp)).comp h
    simpa [Function.comp_def] using h2
  have hev : ∀ᶠ B in atTop, 1 - ε < (gaussMeasure (boundedWordsEvent B m)).toReal := by
    have := hreal.eventually (eventually_gt_nhds (by linarith : (1 : ℝ) - ε < 1))
    simpa using this
  obtain ⟨B, hB⟩ := hev.exists
  refine ⟨B, ?_⟩
  rw [gaussMeasure_boundedWordsEvent_eq_sum B m,
    ENNReal.toReal_sum (fun w _ => measure_ne_top _ _)] at hB
  exact hB

/-! ## Step 1: the weighted upper-bound engine -/

variable {S : Type*} [DecidableEq S]

/-- **The factorized joint-frequency hypothesis.**  For every genuine window `q` and every
state `t`, the joint (window, state) frequency along a CF-normal `x` converges to
`ν t · γ(I_q)`.  This is exactly what `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`
delivers once `ClassEquidistribution` is supplied, with `ν t` the stationary weight of `t`;
the *product* form is the strengthening over Vandehey's Remark 3.6, and it is what makes
countable additivity of the limit free. -/
def JointStateFreq (δ : S → ℕ → S) (s₀ : S) (ν : S → ℝ) : Prop :=
  ∀ (t : S) (q : List ℕ), q ≠ [] → (∀ a ∈ q, 1 ≤ a) → ∀ x : ℝ, IsCFNormal x →
    Tendsto (fun n => (jointCount δ s₀ t q x n : ℝ) / n) atTop
      (nhds (ν t * (gaussMeasure (cfCylinder q)).toReal))

/-- The number of positions `i < n` at which the length-`|w|` digit window spells `w`. -/
noncomputable def winCard (w : List ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => w = cfWindow x i w.length).card

/-- The state-restricted weighted count: `Σ_{i<n} a(wᵢ)·1[tᵢ = t]`, where `wᵢ` is the
length-`m` window at `i`.  For a trigger family bucketed by length this is exactly the
`F_j` of Vandehey §6, and for `a = 1` on one word it is `jointCount`. -/
noncomputable def wCount (δ : S → ℕ → S) (s₀ t : S) (a : List ℕ → ℝ) (m : ℕ) (x : ℝ)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if stateAt δ s₀ x i = t then a (cfWindow x i m) else 0

/-- **The pointwise split.**  Against any finite set `Q` of length-`m` words, the weighted
count is bounded by the exact contribution of `Q` plus `C` times the number of positions
whose window escapes `Q`.  No limits, no measure theory — this is the whole combinatorial
content of Vandehey's `F_j^±` sandwich. -/
lemma wCount_le_of_finset (δ : S → ℕ → S) (s₀ t : S) {a : List ℕ → ℝ} {C : ℝ} {m : ℕ}
    (ha0 : ∀ w, 0 ≤ a w) (haC : ∀ w, a w ≤ C) (x : ℝ) (n : ℕ)
    (Q : Finset (List ℕ)) (hQ : ∀ w ∈ Q, w.length = m) :
    wCount δ s₀ t a m x n
      ≤ ∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ)
        + C * ((n : ℝ) - ∑ w ∈ Q, (winCard w x n : ℝ)) := by
  classical
  set g : ℕ → ℝ := fun i => if stateAt δ s₀ x i = t then a (cfWindow x i m) else 0 with hgdef
  have hC0 : 0 ≤ C := le_trans (ha0 []) (haC [])
  have hgC : ∀ i, g i ≤ C := by
    intro i
    simp only [hgdef]
    split
    · exact haC _
    · exact hC0
  -- the fiber of a word `w ∈ Q`
  have hfib : ∀ w ∈ Q, ((Finset.range n).filter fun i => cfWindow x i m = w)
      = (Finset.range n).filter fun i => w = cfWindow x i w.length := by
    intro w hw
    rw [hQ w hw]
    exact Finset.filter_congr fun i _ => eq_comm
  have hjoint : ∀ w ∈ Q,
      (((Finset.range n).filter fun i => cfWindow x i m = w).filter
        fun i => stateAt δ s₀ x i = t) = jointSet δ s₀ t w x n := by
    intro w hw
    have hlen := hQ w hw
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, jointSet, hlen]
    constructor
    · rintro ⟨⟨hi, hw'⟩, hs⟩; exact ⟨hi, hw'.symm, hs⟩
    · rintro ⟨hi, hw', hs⟩; exact ⟨⟨hi, hw'.symm⟩, hs⟩
  have key : ∀ w ∈ Q, ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m = w), g i
      = a w * (jointCount δ s₀ t w x n : ℝ) := by
    intro w hw
    have h1 : ∀ i ∈ (Finset.range n).filter (fun i => cfWindow x i m = w),
        g i = if stateAt δ s₀ x i = t then a w else 0 := by
      intro i hi
      have hiw : cfWindow x i m = w := (Finset.mem_filter.mp hi).2
      simp only [hgdef, hiw]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, hjoint w hw, Finset.sum_const,
      jointCount_eq_card, nsmul_eq_mul, mul_comm]
  -- split `range n` by membership of the window in `Q`
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun i => cfWindow x i m ∈ Q) g
  have hmaps : ∀ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∈ Q),
      cfWindow x i m ∈ Q := fun i hi => (Finset.mem_filter.mp hi).2
  have hfw := Finset.sum_fiberwise_of_maps_to hmaps g
  have hrestrict : ∀ w ∈ Q,
      (((Finset.range n).filter fun i => cfWindow x i m ∈ Q).filter
        fun i => cfWindow x i m = w) = (Finset.range n).filter fun i => cfWindow x i m = w := by
    intro w hw
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hi, -⟩, he⟩; exact ⟨hi, he⟩
    · rintro ⟨hi, he⟩; exact ⟨⟨hi, he ▸ hw⟩, he⟩
  have hpart : ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∈ Q), g i
      = ∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ) := by
    rw [← hfw]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hrestrict w hw, key w hw]
  -- the escaping positions
  have hcardsum : ∑ w ∈ Q, winCard w x n
      = ((Finset.range n).filter fun i => cfWindow x i m ∈ Q).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [winCard, ← hfib w hw, hrestrict w hw]
  have hcardtot := Finset.card_filter_add_card_filter_not
      (s := Finset.range n) (p := fun i => cfWindow x i m ∈ Q)
  rw [Finset.card_range] at hcardtot
  have hesc : (((Finset.range n).filter fun i => cfWindow x i m ∉ Q).card : ℝ)
      = (n : ℝ) - ∑ w ∈ Q, (winCard w x n : ℝ) := by
    have : ((Finset.range n).filter fun i => ¬ (cfWindow x i m ∈ Q)).card
        = n - ((Finset.range n).filter fun i => cfWindow x i m ∈ Q).card := by omega
    rw [show ((Finset.range n).filter fun i => cfWindow x i m ∉ Q)
        = ((Finset.range n).filter fun i => ¬ (cfWindow x i m ∈ Q)) from rfl, this,
      Nat.cast_sub (by omega), ← hcardsum, Nat.cast_sum]
  have hle2 : ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∉ Q), g i
      ≤ C * ((n : ℝ) - ∑ w ∈ Q, (winCard w x n : ℝ)) := by
    rw [← hesc]
    have := Finset.sum_le_card_nsmul
      ((Finset.range n).filter fun i => cfWindow x i m ∉ Q) g C (fun i _ => hgC i)
    rw [nsmul_eq_mul] at this
    rw [mul_comm]
    exact this
  calc wCount δ s₀ t a m x n = ∑ i ∈ Finset.range n, g i := rfl
    _ = ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∈ Q), g i
        + ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∉ Q), g i := hsplit.symm
    _ ≤ ∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ)
        + C * ((n : ℝ) - ∑ w ∈ Q, (winCard w x n : ℝ)) := by rw [hpart]; linarith [hle2]

/-- **The upper-bound engine** (Vandehey Lemma 4.3, upper half).  If every finite
length-`m` subfamily has weighted limit mass at most `Sb`, then the weighted count is
eventually at most `(Sb + ε)·n`, for every `ε > 0`.  The infinite CF alphabet is escaped by
the digit-truncated finite family of `exists_boundedWords_sum_gt`: the escaping positions
carry frequency `< ε`, and each contributes at most `C`. -/
theorem eventually_wCount_le (δ : S → ℕ → S) (s₀ : S) {ν : S → ℝ}
    (hjs : JointStateFreq δ s₀ ν) (t : S) {a : List ℕ → ℝ} {C Sb : ℝ} {m : ℕ} (hm : 0 < m)
    (ha0 : ∀ w, 0 ≤ a w) (haC : ∀ w, a w ≤ C)
    (hSb : ∀ Q : Finset (List ℕ), (∀ w ∈ Q, w ∈ allWords m) →
      ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal) ≤ Sb)
    {x : ℝ} (hx : IsCFNormal x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, wCount δ s₀ t a m x n ≤ (Sb + ε) * n := by
  classical
  have hC0 : 0 ≤ C := le_trans (ha0 []) (haC [])
  set ε' : ℝ := ε / (2 * (C + 1)) with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; positivity
  obtain ⟨B, hB⟩ := exists_boundedWords_sum_gt m hε'
  set Q : Finset (List ℕ) := boundedWords B m with hQdef
  have hQmem : ∀ w ∈ Q, w ∈ allWords m := fun w hw =>
    boundedWords_subset_allWords B m (by simpa [hQdef] using hw)
  have hQlen : ∀ w ∈ Q, w.length = m := fun w hw => (hQmem w hw).1
  have hQne : ∀ w ∈ Q, w ≠ [] := by
    intro w hw hnil
    rw [hnil] at hw
    have := hQlen [] hw
    simp at this
    omega
  have hQpos : ∀ w ∈ Q, ∀ b ∈ w, 1 ≤ b := fun w hw => (hQmem w hw).2
  -- the two frequency limits, for each `w ∈ Q`
  set γ : List ℕ → ℝ := fun w => (gaussMeasure (cfCylinder w)).toReal with hγdef
  have hjc : ∀ w ∈ Q, Tendsto (fun n => (jointCount δ s₀ t w x n : ℝ) / n) atTop
      (nhds (ν t * γ w)) := fun w hw => hjs t w (hQne w hw) (hQpos w hw) x hx
  have hwc : ∀ w ∈ Q, Tendsto (fun n => (winCard w x n : ℝ) / n) atTop (nhds (γ w)) := by
    intro w hw
    simpa [winCard, hγdef] using tendsto_windowFreq hx w (hQne w hw) (hQpos w hw)
  -- the limit of the majorant
  set F : ℕ → ℝ := fun n => (∑ w ∈ Q, a w * ((jointCount δ s₀ t w x n : ℝ) / n))
      + C * (1 - ∑ w ∈ Q, ((winCard w x n : ℝ) / n)) with hFdef
  set L : ℝ := (∑ w ∈ Q, a w * (ν t * γ w)) + C * (1 - ∑ w ∈ Q, γ w) with hLdef
  have hFL : Tendsto F atTop (nhds L) := by
    rw [hFdef, hLdef]
    refine Tendsto.add (tendsto_finsetSum _ fun w hw => ?_) ?_
    · exact (hjc w hw).const_mul (a w)
    · exact Tendsto.const_mul _ (tendsto_const_nhds.sub (tendsto_finsetSum _ hwc))
  -- the limit is below `Sb + ε`
  have hsum1 : ∑ w ∈ Q, γ w ≤ 1 := by
    simpa [hγdef, hQdef] using sum_gaussMeasure_boundedWords_le_one B m
  have htail : 1 - ∑ w ∈ Q, γ w ≤ ε' := by
    have : 1 - ε' < ∑ w ∈ Q, γ w := by simpa [hγdef, hQdef] using hB
    linarith
  have hCε : C * ε' ≤ ε / 2 := by
    have hd : (0 : ℝ) < C + 1 := by linarith
    rw [hε'def, ← mul_div_assoc,
      div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε.le, hC0]
  have hLlt : L < Sb + ε := by
    have h1 : (∑ w ∈ Q, a w * (ν t * γ w)) ≤ Sb := hSb Q hQmem
    have h2 : C * (1 - ∑ w ∈ Q, γ w) ≤ C * ε' :=
      mul_le_mul_of_nonneg_left htail hC0
    rw [hLdef]
    linarith
  have hev : ∀ᶠ n in atTop, F n < Sb + ε := hFL.eventually (eventually_lt_nhds hLlt)
  -- transfer the pointwise split
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have h1 : (∑ w ∈ Q, a w * ((jointCount δ s₀ t w x n : ℝ) / n))
      = (∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ)) / n := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h2 : (∑ w ∈ Q, ((winCard w x n : ℝ) / n))
      = (∑ w ∈ Q, (winCard w x n : ℝ)) / n := by rw [Finset.sum_div]
  have hident : (∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ))
      + C * ((n : ℝ) - ∑ w ∈ Q, (winCard w x n : ℝ)) = (n : ℝ) * F n := by
    simp only [hFdef]
    rw [h1, h2]
    field_simp
  have hsplit := wCount_le_of_finset δ s₀ t ha0 haC x n Q hQlen
  rw [hident] at hsplit
  calc wCount δ s₀ t a m x n ≤ (n : ℝ) * F n := hsplit
    _ ≤ (Sb + ε) * n := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hn.le hnpos.le

/-! ## The lower half: truncation -/

/-- A finite same-length cylinder family has total Gauss mass at most `1`. -/
lemma sum_gaussMeasure_le_one_of_length {m : ℕ} (Q : Finset (List ℕ))
    (hQ : ∀ w ∈ Q, w.length = m) :
    ∑ w ∈ Q, (gaussMeasure (cfCylinder w)).toReal ≤ 1 := by
  classical
  have hdisj : (↑Q : Set (List ℕ)).PairwiseDisjoint (fun w => cfCylinder w) :=
    pairwiseDisjoint_cfCylinder (n := m) fun w hw => hQ w hw
  have hbi := measure_biUnion_finset (μ := gaussMeasure) hdisj
    (fun w _ => measurableSet_cfCylinder w)
  have hle1 : gaussMeasure (⋃ w ∈ Q, cfCylinder w) ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq gaussMeasure_univ
  rw [← ENNReal.toReal_sum (fun w _ => measure_ne_top _ _), ← hbi]
  calc (gaussMeasure (⋃ w ∈ Q, cfCylinder w)).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono (by norm_num) hle1
    _ = 1 := by simp

/-- **The `Q`-part of the weighted count is exactly the `Q`-weighted joint count.**  The
fiberwise identity behind both halves of the sandwich. -/
lemma sum_filter_mem_eq (δ : S → ℕ → S) (s₀ t : S) (a : List ℕ → ℝ) {m : ℕ} (x : ℝ) (n : ℕ)
    (Q : Finset (List ℕ)) (hQ : ∀ w ∈ Q, w.length = m) :
    ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∈ Q),
        (if stateAt δ s₀ x i = t then a (cfWindow x i m) else 0)
      = ∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ) := by
  classical
  set g : ℕ → ℝ := fun i => if stateAt δ s₀ x i = t then a (cfWindow x i m) else 0 with hgdef
  have hjoint : ∀ w ∈ Q,
      (((Finset.range n).filter fun i => cfWindow x i m = w).filter
        fun i => stateAt δ s₀ x i = t) = jointSet δ s₀ t w x n := by
    intro w hw
    have hlen := hQ w hw
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, jointSet, hlen]
    constructor
    · rintro ⟨⟨hi, hw'⟩, hs⟩; exact ⟨hi, hw'.symm, hs⟩
    · rintro ⟨hi, hw', hs⟩; exact ⟨⟨hi, hw'.symm⟩, hs⟩
  have key : ∀ w ∈ Q, ∑ i ∈ (Finset.range n).filter (fun i => cfWindow x i m = w), g i
      = a w * (jointCount δ s₀ t w x n : ℝ) := by
    intro w hw
    have h1 : ∀ i ∈ (Finset.range n).filter (fun i => cfWindow x i m = w),
        g i = if stateAt δ s₀ x i = t then a w else 0 := by
      intro i hi
      have hiw : cfWindow x i m = w := (Finset.mem_filter.mp hi).2
      simp only [hgdef, hiw]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, hjoint w hw, Finset.sum_const,
      jointCount_eq_card, nsmul_eq_mul, mul_comm]
  have hmaps : ∀ i ∈ (Finset.range n).filter (fun i => cfWindow x i m ∈ Q),
      cfWindow x i m ∈ Q := fun i hi => (Finset.mem_filter.mp hi).2
  have hfw := Finset.sum_fiberwise_of_maps_to hmaps g
  have hrestrict : ∀ w ∈ Q,
      (((Finset.range n).filter fun i => cfWindow x i m ∈ Q).filter
        fun i => cfWindow x i m = w) = (Finset.range n).filter fun i => cfWindow x i m = w := by
    intro w hw
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hi, -⟩, he⟩; exact ⟨hi, he⟩
    · rintro ⟨hi, he⟩; exact ⟨⟨hi, he ▸ hw⟩, he⟩
  rw [← hfw]
  exact Finset.sum_congr rfl fun w hw => by rw [hrestrict w hw, key w hw]

/-- **The pointwise truncation lower bound.**  Dropping every position whose window escapes
`Q` can only lower a nonnegative weighted count. -/
lemma wCount_ge_of_finset (δ : S → ℕ → S) (s₀ t : S) {a : List ℕ → ℝ} {m : ℕ}
    (ha0 : ∀ w, 0 ≤ a w) (x : ℝ) (n : ℕ)
    (Q : Finset (List ℕ)) (hQ : ∀ w ∈ Q, w.length = m) :
    ∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ) ≤ wCount δ s₀ t a m x n := by
  classical
  rw [← sum_filter_mem_eq δ s₀ t a x n Q hQ, wCount]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  split
  · exact ha0 _
  · exact le_rfl

/-- **The lower-bound engine** (Vandehey Lemma 4.3, lower half).  Every finite length-`m`
subfamily's limit mass is eventually attained, up to `ε`. -/
theorem eventually_le_wCount (δ : S → ℕ → S) (s₀ : S) {ν : S → ℝ}
    (hjs : JointStateFreq δ s₀ ν) (t : S) {a : List ℕ → ℝ} {m : ℕ} (hm : 0 < m)
    (ha0 : ∀ w, 0 ≤ a w) (Q : Finset (List ℕ)) (hQmem : ∀ w ∈ Q, w ∈ allWords m)
    {x : ℝ} (hx : IsCFNormal x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ((∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal)) - ε) * n
        ≤ wCount δ s₀ t a m x n := by
  classical
  have hQlen : ∀ w ∈ Q, w.length = m := fun w hw => (hQmem w hw).1
  have hQne : ∀ w ∈ Q, w ≠ [] := by
    intro w hw hnil
    have := hQlen w hw
    rw [hnil] at this
    simp at this
    omega
  have hQpos : ∀ w ∈ Q, ∀ b ∈ w, 1 ≤ b := fun w hw => (hQmem w hw).2
  set γ : List ℕ → ℝ := fun w => (gaussMeasure (cfCylinder w)).toReal with hγdef
  set Sq : ℝ := ∑ w ∈ Q, a w * (ν t * γ w) with hSqdef
  have hjc : ∀ w ∈ Q, Tendsto (fun n => (jointCount δ s₀ t w x n : ℝ) / n) atTop
      (nhds (ν t * γ w)) := fun w hw => hjs t w (hQne w hw) (hQpos w hw) x hx
  have hlim : Tendsto (fun n => ∑ w ∈ Q, a w * ((jointCount δ s₀ t w x n : ℝ) / n)) atTop
      (nhds Sq) := by
    rw [hSqdef]
    exact tendsto_finsetSum _ fun w hw => (hjc w hw).const_mul (a w)
  have hev : ∀ᶠ n in atTop,
      Sq - ε < ∑ w ∈ Q, a w * ((jointCount δ s₀ t w x n : ℝ) / n) :=
    hlim.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have h1 : (∑ w ∈ Q, a w * ((jointCount δ s₀ t w x n : ℝ) / n))
      = (∑ w ∈ Q, a w * (jointCount δ s₀ t w x n : ℝ)) / n := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [h1, lt_div_iff₀ hnpos] at hn
  exact le_trans hn.le (wCount_ge_of_finset δ s₀ t ha0 x n Q hQlen)

/-! ## Vandehey Lemma 4.3 at a single window length -/

/-- **The `x`-independent limit**, defined with no reference to any `x`: the supremum of the
weighted limit masses of the finite length-`m` subfamilies.  For a *finite* family this is the
plain sum; the content is that a countable family has the same Cesàro behaviour. -/
noncomputable def wLimit (ν : S → ℝ) (t : S) (a : List ℕ → ℝ) (m : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ Q : Finset (List ℕ), (∀ w ∈ Q, w ∈ allWords m) ∧
    c = ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal)}

omit [DecidableEq S] in
lemma wLimit_set_nonempty (ν : S → ℝ) (t : S) (a : List ℕ → ℝ) (m : ℕ) :
    {c : ℝ | ∃ Q : Finset (List ℕ), (∀ w ∈ Q, w ∈ allWords m) ∧
      c = ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal)}.Nonempty :=
  ⟨0, ∅, by simp, by simp⟩

omit [DecidableEq S] in
lemma wLimit_set_bddAbove {ν : S → ℝ} {t : S} {a : List ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hν : 0 ≤ ν t) (haC : ∀ w, a w ≤ C) (ha0 : ∀ w, 0 ≤ a w) :
    BddAbove {c : ℝ | ∃ Q : Finset (List ℕ), (∀ w ∈ Q, w ∈ allWords m) ∧
      c = ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal)} := by
  refine ⟨C * ν t, ?_⟩
  rintro c ⟨Q, hQ, rfl⟩
  have hC0 : 0 ≤ C := le_trans (ha0 []) (haC [])
  calc ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal)
      ≤ ∑ w ∈ Q, C * (ν t * (gaussMeasure (cfCylinder w)).toReal) := by
        refine Finset.sum_le_sum fun w _ => ?_
        exact mul_le_mul_of_nonneg_right (haC w) (by positivity)
    _ = C * ν t * ∑ w ∈ Q, (gaussMeasure (cfCylinder w)).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    _ ≤ C * ν t * 1 := by
        refine mul_le_mul_of_nonneg_left
          (sum_gaussMeasure_le_one_of_length Q fun w hw => (hQ w hw).1) (by positivity)
    _ = C * ν t := by ring

/-- **Vandehey Lemma 4.3, single length, `x`-independent.**  For a bounded nonnegative weight
supported on the (countably infinite) length-`m` genuine words, the state-restricted weighted
count has Cesàro limit `wLimit ν t a m` — a value that mentions no `x`.  This is the whole
content of the published Lemma 4.3 in the infinite-family case, and it needs no ergodic theory,
no Ryll-Nardzewski and no Vitali-Hahn-Saks: the finite digit truncation of
`exists_boundedWords_sum_gt` does the work. -/
theorem tendsto_wCount_div (δ : S → ℕ → S) (s₀ : S) {ν : S → ℝ}
    (hjs : JointStateFreq δ s₀ ν) (t : S) (hν : 0 ≤ ν t) {a : List ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hm : 0 < m) (ha0 : ∀ w, 0 ≤ a w) (haC : ∀ w, a w ≤ C)
    {x : ℝ} (hx : IsCFNormal x) :
    Tendsto (fun n => wCount δ s₀ t a m x n / n) atTop (nhds (wLimit ν t a m)) := by
  classical
  set T : Set ℝ := {c : ℝ | ∃ Q : Finset (List ℕ), (∀ w ∈ Q, w ∈ allWords m) ∧
    c = ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal)} with hTdef
  have hne : T.Nonempty := wLimit_set_nonempty ν t a m
  have hbdd : BddAbove T := wLimit_set_bddAbove (C := C) hν haC ha0
  set L : ℝ := wLimit ν t a m with hLdef
  have hLsup : L = sSup T := rfl
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- upper half
  have hUB : ∀ Q : Finset (List ℕ), (∀ w ∈ Q, w ∈ allWords m) →
      ∑ w ∈ Q, a w * (ν t * (gaussMeasure (cfCylinder w)).toReal) ≤ L := by
    intro Q hQ
    exact le_csSup hbdd ⟨Q, hQ, rfl⟩
  have hup := eventually_wCount_le δ s₀ hjs t hm ha0 haC hUB hx
    (show (0 : ℝ) < ε / 4 by positivity)
  -- lower half
  obtain ⟨c, hcT, hclt⟩ := exists_lt_of_lt_csSup hne
    (show L - ε / 4 < sSup T by rw [← hLsup]; linarith)
  obtain ⟨Q, hQ, rfl⟩ := hcT
  have hlow := eventually_le_wCount δ s₀ hjs t hm ha0 Q hQ hx
    (show (0 : ℝ) < ε / 4 by positivity)
  filter_upwards [hup, hlow, eventually_ge_atTop 1] with n hnu hnl hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hA : L - ε / 2 ≤ wCount δ s₀ t a m x n / n := by
    rw [le_div_iff₀ hnpos]
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hnpos.le) hnl
  have hB : wCount δ s₀ t a m x n / n ≤ L + ε / 2 := by
    rw [div_le_iff₀ hnpos]
    exact le_trans hnu (mul_le_mul_of_nonneg_right (by linarith) hnpos.le)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## The guard rule for `JointStateFreq` -/

/-- Some real is CF-normal (a.e. one is). -/
lemma exists_isCFNormal : ∃ x : ℝ, IsCFNormal x := by
  by_contra h
  push Not at h
  have hnull : gaussMeasure {y | ¬ IsCFNormal y} = 0 := by
    rw [← MeasureTheory.ae_iff]; exact ae_isCFNormal
  have hu : {y : ℝ | ¬ IsCFNormal y} = Set.univ := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact h y
  rw [hu, gaussMeasure_univ] at hnull
  exact one_ne_zero hnull

/-- The one-state automaton reduces the joint count to the plain window count. -/
lemma jointCount_unit (q : List ℕ) (x : ℝ) (n : ℕ) :
    jointCount (fun (_ : Unit) (_ : ℕ) => ()) () () q x n
      = ((Finset.range n).filter fun i => q = cfWindow x i q.length).card := by
  rw [jointCount, jointSet]
  congr 1
  exact Finset.filter_congr fun i _ => and_iff_left (Subsingleton.elim _ _)

/-- **Content locator** (guard rule): the one-state automaton satisfies `JointStateFreq` with
`ν ≡ 1`, on CF-normality of `x` alone.  So the transducer hypothesis has no content until the
state space is nontrivial — this is where the content is *not*. -/
theorem jointStateFreq_unit :
    JointStateFreq (fun (_ : Unit) (_ : ℕ) => ()) () (fun _ => 1) := by
  intro t q hq hqpos x hx
  have ht : t = () := Subsingleton.elim _ _
  subst ht
  simpa [jointCount_unit, one_mul] using tendsto_windowFreq hx q hq hqpos

/-- **Degenerate-case verdict** (guard rule): `ν ≡ 0` is FALSE, already for the one-state
automaton, because the joint count is then the window count and `γ(I_{[1]}) > 0`.  So the
weight `ν` is load-bearing: it cannot be normalized away. -/
theorem not_jointStateFreq_unit_zero :
    ¬ JointStateFreq (fun (_ : Unit) (_ : ℕ) => ()) () (fun _ => 0) := by
  intro h
  obtain ⟨x, hx⟩ := exists_isCFNormal
  have h1 := h () [1] (by simp) (by simp) x hx
  have h2 := jointStateFreq_unit () [1] (by simp) (by simp) x hx
  have heq := tendsto_nhds_unique h1 h2
  have hpos : 0 < (gaussMeasure (cfCylinder [1])).toReal :=
    VandeheyRenyi.Doeblin.gaussMeasure_cfCylinder_toReal_pos [1] (by simp) (by simp)
  rw [zero_mul, one_mul] at heq
  exact absurd heq.symm (ne_of_gt hpos)

/-- **Degenerate-case verdict** (guard rule, boundary configuration): `wCount` at `m = 0` is
just the dwell count of the state, with the single weight `a []`.  No window information
survives, so the `m = 0` slice of the engine is vacuous — the hypothesis `0 < m` in
`eventually_wCount_le` is doing real work. -/
theorem wCount_zero_length (δ : S → ℕ → S) (s₀ t : S) (a : List ℕ → ℝ) (x : ℝ) (n : ℕ) :
    wCount δ s₀ t a 0 x n
      = a [] * (((Finset.range n).filter fun i => stateAt δ s₀ x i = t).card : ℝ) := by
  classical
  rw [wCount]
  have : ∀ i ∈ Finset.range n,
      (if stateAt δ s₀ x i = t then a (cfWindow x i 0) else 0)
        = if stateAt δ s₀ x i = t then a [] else 0 := by
    intro i _
    simp [cfWindow]
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Degenerate-case verdict** (guard rule, constant-function configuration): the engine's
conclusion is sharp at `a ≡ 0` — the count is identically zero and the bound is `ε·n`. -/
theorem wCount_zero_weight (δ : S → ℕ → S) (s₀ t : S) (m : ℕ) (x : ℝ) (n : ℕ) :
    wCount δ s₀ t (fun _ => 0) m x n = 0 := by
  rw [wCount]
  exact Finset.sum_eq_zero fun i _ => by simp

end VandeheyOut

end NormalNumbers

section
open NormalNumbers.VandeheyOut
#print axioms gaussMeasure_allWordsEvent
#print axioms exists_boundedWords_sum_gt
#print axioms wCount_le_of_finset
#print axioms eventually_wCount_le
#print axioms jointStateFreq_unit
#print axioms not_jointStateFreq_unit_zero
#print axioms eventually_le_wCount
#print axioms tendsto_wCount_div
end
