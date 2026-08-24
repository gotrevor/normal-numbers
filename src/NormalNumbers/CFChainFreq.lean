/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFConcat
import NormalNumbers.CFOrbitFreq
import NormalNumbers.TBrickRefine

/-!
# B6 crux — abstract generic-chain frequency telescoping

The frozen `CFCorrect.xstar_cf_freq_tendsto` proves CF window-frequency
convergence for the SPECIFIC limit point `xstar` of `CFSchedule.sched`.  Its
argument (B–Y Lemma 7 telescoping) only ever uses two facts about the schedule:
each appended block is *frequency-good*, and each appended block is *short
relative to the accumulated word* (dominance).  This module ABSTRACTS that
argument to an arbitrary nested chain `w : ℕ → List ℕ` satisfying those two
facts as hypotheses.

This is the route-decisive crux atom of the interleaved affine-image schedule
(B6, `CFScheduleA`): the schedule builds TWO chains (`x`-stream, `ψ`-stream),
each a nested chain of genuine CF words with freq-good dominant appended blocks;
feeding each into `chain_orbit_equidist` gives `CFOrbitEquidist` for both the
`x`-limit and the `ψ`-chain limit, and the interval invariant glues the latter
to `ψ(x)`.  Additive over B5′: this module copy-EXTENDS `CFCorrect`; it never
edits it.

Design of the two abstract hypotheses (per genuine pattern `v`, `γv := γ(I_v)`):
* `hgood ε` : eventually every appended block `chainApp w s` is margin-good —
  `|count v (app s) − γv·|app s|| < ε·|app s| − (|v|−1)`.
* `hdom ε`  : eventually every appended block is short vs the accumulated word —
  `|app s| + (|v|−1) < ε·|w s|`.
Both quantify `∀ ε>0 ∃ s₀ ∀ s≥s₀`, matching how the schedule delivers them
(tolerance → 0 with growing depth).  The interleaved-schedule *fillers* are
folded into `chainApp` by the caller: a bounded-but-growing filler is absorbed
into `hgood`/`hdom` by choosing each stage's freq-good block length large enough.
-/

namespace NormalNumbers

open MeasureTheory Filter

/-! ## Generic chain tail machinery (ports `CFCorrect`'s `tailSched` block) -/

/-- The block appended to the chain when going from stage `s` to `s + 1`. -/
noncomputable def chainApp (w : ℕ → List ℕ) (s : ℕ) : List ℕ :=
  (w (s + 1)).drop (w s).length

/-- Under the extension hypothesis, `w (s+1)` splits as `w s ++ chainApp w s`,
and the appended block is nonempty. -/
theorem chainApp_eq (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) (s : ℕ) :
    w (s + 1) = w s ++ chainApp w s ∧ chainApp w s ≠ [] := by
  obtain ⟨u, hune, hu⟩ := hext s
  have hce : chainApp w s = u := by rw [chainApp, hu, List.drop_left]
  rw [hce]; exact ⟨hu, hune⟩

/-- The digits appended after stage `s₀`. -/
noncomputable def chainTail (w : ℕ → List ℕ) (s₀ s : ℕ) : List ℕ :=
  (w s).drop (w s₀).length

theorem chainTail_self (w : ℕ → List ℕ) (s₀ : ℕ) : chainTail w s₀ s₀ = [] := by
  rw [chainTail, List.drop_length]

/-- The chained word splits at any earlier stage. -/
theorem w_eq_append_tail (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) (s₀ : ℕ) :
    ∀ k, w (s₀ + k) = w s₀ ++ chainTail w s₀ (s₀ + k) := by
  intro k
  induction k with
  | zero => simp [chainTail_self]
  | succ k ih =>
    have hidx : s₀ + (k + 1) = (s₀ + k) + 1 := by omega
    have happ := (chainApp_eq w hext (s₀ + k)).1
    have htail : chainTail w s₀ ((s₀ + k) + 1)
        = chainTail w s₀ (s₀ + k) ++ chainApp w (s₀ + k) := by
      rw [chainTail, happ, ih, List.append_assoc, List.drop_left]
    rw [hidx, htail, happ, ih, List.append_assoc]

/-- The tail extends by the appended block each step. -/
theorem chainTail_succ (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) (s₀ k : ℕ) :
    chainTail w s₀ (s₀ + k + 1)
      = chainTail w s₀ (s₀ + k) ++ chainApp w (s₀ + k) := by
  have happ := (chainApp_eq w hext (s₀ + k)).1
  rw [chainTail, happ, w_eq_append_tail w hext s₀ k, List.append_assoc,
    List.drop_left]

/-- The chained word length grows at least linearly (strict extension). -/
theorem w_length_ge (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) (s : ℕ) :
    ∀ k, (w s).length + k ≤ (w (s + k)).length := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have happ := chainApp_eq w hext (s + k)
    have hlen : (w (s + k + 1)).length
        = (w (s + k)).length + (chainApp w (s + k)).length := by
      rw [happ.1, List.length_append]
    have hpos : 1 ≤ (chainApp w (s + k)).length :=
      List.length_pos_of_ne_nil happ.2
    have hidx : s + (k + 1) = (s + k) + 1 := by omega
    rw [hidx, hlen]; omega

/-- Tail length grows at least linearly. -/
theorem le_chainTail_length (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) (s₀ k : ℕ) :
    k ≤ (chainTail w s₀ (s₀ + k)).length := by
  have h1 := w_eq_append_tail w hext s₀ k
  have h2 : ((w s₀).length) + k ≤ (w (s₀ + k)).length := w_length_ge w hext s₀ k
  have h3 : (w (s₀ + k)).length
      = (w s₀).length + (chainTail w s₀ (s₀ + k)).length := by
    rw [h1, List.length_append]
  omega

/-- Every position `p` past stage `s₁` lies in a definite stage window
`[|w s|, |w (s+1)|)` with `s ≥ s₁`. -/
theorem chain_exists_stage (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u) (s₁ p : ℕ)
    (hp : (w s₁).length ≤ p) :
    ∃ s, s₁ ≤ s ∧ (w s).length ≤ p ∧ p < (w (s + 1)).length := by
  classical
  set Q : ℕ → Prop := fun k => (w (s₁ + k)).length ≤ p with hQdef
  have hQ0 : Q 0 := by simpa [hQdef] using hp
  have hQbig : ¬ Q (p + 1) := by
    have h := w_length_ge w hext s₁ (p + 1)
    simp only [hQdef]; omega
  set k := Nat.findGreatest Q (p + 1) with hkdef
  have hk : Q k := Nat.findGreatest_spec (Nat.zero_le _) hQ0
  have hkne : k ≠ p + 1 := fun h => hQbig (h ▸ hk)
  have hkb : k ≤ p + 1 := Nat.findGreatest_le _
  have hk1 : ¬ Q (k + 1) :=
    Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by omega)
  refine ⟨s₁ + k, by omega, hk, ?_⟩
  have h2 : s₁ + k + 1 = s₁ + (k + 1) := by omega
  rw [h2]
  simp only [hQdef] at hk1
  omega

/-! ## The tail chain (B–Y Lemma 7 induction), abstract form -/

/-- **The good-tail chain (abstract).**  If every appended block past `s₀` is
margin-good for `v`, every tail past `s₀` is `ε`-good for `v`.  Direct port of
`CFCorrect.tailSched_cfDiscLt` with the level-margin machinery replaced by the
`hblock` hypothesis. -/
theorem chainTail_cfDiscLt (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u)
    (v : List ℕ) (hne : v ≠ []) {γv ε : ℝ} (s₀ : ℕ)
    (hblock : ∀ k, |(countOccurrences v (chainApp w (s₀ + k)) : ℝ)
        - γv * (chainApp w (s₀ + k)).length|
      < ε * (chainApp w (s₀ + k)).length - ((v.length : ℝ) - 1)) :
    ∀ k, CFDiscLt v (chainTail w s₀ (s₀ + k + 1)) γv ε := by
  have hv1 : (1 : ℝ) ≤ v.length := by
    exact_mod_cast List.length_pos_of_ne_nil hne
  intro k
  induction k with
  | zero =>
    have h0 : chainTail w s₀ (s₀ + 0 + 1) = chainApp w s₀ := by
      have := chainTail_succ w hext s₀ 0
      simpa [chainTail_self] using this
    rw [h0]
    have h := hblock 0
    simp only [Nat.add_zero] at h
    rw [CFDiscLt]
    calc |(countOccurrences v (chainApp w s₀) : ℝ)
        - γv * (chainApp w s₀).length|
        < ε * (chainApp w s₀).length - ((v.length : ℝ) - 1) := h
      _ ≤ ε * (chainApp w s₀).length := by linarith
  | succ k ih =>
    have h1 : s₀ + (k + 1) = s₀ + k + 1 := by omega
    have hstep := chainTail_succ w hext s₀ (k + 1)
    rw [h1] at hstep
    have h2 : s₀ + (k + 1) + 1 = s₀ + k + 1 + 1 := by omega
    rw [h2, hstep]
    exact CFDiscLt.append hne ih (by
      have := hblock (k + 1)
      rwa [h1] at this)

/-! ## The digit prefix identity -/

/-- The length-`|w s|` CF digit prefix of a point `y` in every chain cylinder
IS `w s`. -/
theorem chain_cfPref_eq (w : ℕ → List ℕ) {y : ℝ}
    (hy : ∀ s, y ∈ cfCylinder (w s)) (s : ℕ) :
    (List.range (w s).length).map (cfDigit y) = w s := by
  have h := range_map_cfDigit_eq (w := ([] : List ℕ)) (u := w s) (x := y)
    (by simpa using hy s)
  simpa using h

/-- Digit prefixes restrict under `take`. -/
theorem cfPref_take {y : ℝ} {p q : ℕ} (h : p ≤ q) :
    (List.range p).map (cfDigit y) = ((List.range q).map (cfDigit y)).take p := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ## The abstract window-frequency limit (ports `xstar_cf_freq_tendsto`) -/

/-- **Abstract chain CF window-frequency convergence.**  For a nested genuine
chain `w` with limit point `y ∈ ⋂ cfCylinder (w s)`, if the appended blocks are
eventually margin-good (`hgood`) and eventually short vs the accumulated word
(`hdom`), then the window frequency of `v` in `y`'s digit prefix tends to `γv`.
Faithful port of `CFCorrect.xstar_cf_freq_tendsto`. -/
theorem chain_cf_digit_freq_tendsto (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u)
    {y : ℝ} (hy : ∀ s, y ∈ cfCylinder (w s))
    (v : List ℕ) (hne : v ≠ [])
    {γv : ℝ} (hγ0 : 0 ≤ γv) (hγ1 : γv ≤ 1)
    (hgood : ∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s →
      |(countOccurrences v (chainApp w s) : ℝ) - γv * (chainApp w s).length|
        < ε * (chainApp w s).length - ((v.length : ℝ) - 1))
    (hdom : ∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s →
      ((chainApp w s).length : ℝ) + ((v.length : ℝ) - 1) < ε * (w s).length) :
    Filter.Tendsto
      (fun p => (countOccurrences v ((List.range p).map (cfDigit y)) : ℝ) / p)
      Filter.atTop (nhds γv) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε5 : 0 < ε / 5 := by positivity
  have hv1 : (1 : ℝ) ≤ v.length := by
    exact_mod_cast List.length_pos_of_ne_nil hne
  -- good blocks past `s₀`, short blocks past `s_d`
  obtain ⟨s₀, hs₀⟩ := hgood (ε / 5) hε5
  obtain ⟨s_d, hs_d⟩ := hdom (2 * (ε / 5)) (by positivity)
  -- the tail chain is `ε/5`-good
  have hchain : ∀ k, CFDiscLt v (chainTail w s₀ (s₀ + k + 1)) γv (ε / 5) :=
    chainTail_cfDiscLt w hext v hne s₀
      (fun k => hs₀ (s₀ + k) (Nat.le_add_right _ _))
  set L₀ := (w s₀).length with hL₀
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (((L₀ : ℝ) + v.length) / (ε / 5))
  set K := max K₁ 1 with hK
  -- boundary: whole chained words past stage `s₀ + K` are `2ε/5`-good
  have hbound : ∀ s, s₀ + K ≤ s → CFDiscLt v (w s) γv (2 * (ε / 5)) := by
    intro s hs
    set k := s - s₀ with hk
    have hks : s = s₀ + k := by omega
    have hk1 : 1 ≤ k := by omega
    have htail : CFDiscLt v (chainTail w s₀ s) γv (ε / 5) := by
      have h := hchain (k - 1)
      have h2 : s₀ + (k - 1) + 1 = s := by omega
      rwa [h2] at h
    have hlen : (K : ℕ) ≤ (chainTail w s₀ s).length := by
      have h := le_chainTail_length w hext s₀ k
      rw [← hks] at h
      omega
    have hshort : ((w s₀).length : ℝ) + ((v.length : ℝ) - 1)
        < (ε / 5) * (chainTail w s₀ s).length := by
      have hKk : ((L₀ : ℝ) + v.length) ≤ (ε / 5) * K₁ := by
        rw [div_le_iff₀ hε5] at hK₁; linarith
      have hK₁K : (K₁ : ℝ) ≤ K := by
        exact_mod_cast le_max_left _ _
      have hKlen : (K : ℝ) ≤ (chainTail w s₀ s).length := by exact_mod_cast hlen
      have := mul_le_mul_of_nonneg_left (le_trans hK₁K hKlen) hε5.le
      rw [hL₀] at hKk
      linarith
    have h := cfDiscLt_short_append hne hγ0 hγ1 htail hshort
    have hsplit := w_eq_append_tail w hext s₀ k
    rw [← hks] at hsplit
    rwa [← hsplit] at h
  -- interior prefixes past stage `max (s₀+K) s_d` are `4ε/5`-good
  set s₁ := max (s₀ + K) s_d with hs1def
  have hprefix : ∀ p, (w s₁).length ≤ p →
      CFDiscLt v ((List.range p).map (cfDigit y)) γv (2 * (2 * (ε / 5))) := by
    intro p hp
    obtain ⟨s, hs1, hsp, hsp1⟩ := chain_exists_stage w hext s₁ p hp
    have hsK : s₀ + K ≤ s := le_trans (le_max_left _ _) hs1
    have hsd : s_d ≤ s := le_trans (le_max_right _ _) hs1
    have hdecomp : (List.range p).map (cfDigit y)
        = w s ++ (chainApp w s).take (p - (w s).length) := by
      rw [cfPref_take (y := y) hsp1.le, chain_cfPref_eq w hy,
        (chainApp_eq w hext s).1, List.take_append,
        List.take_of_length_le hsp]
    rw [hdecomp]
    exact cfDiscLt_append_take hne hγ0 hγ1 (hbound s hsK) (hs_d s hsd) _
  -- convert to the metric statement
  set N := max (w s₁).length 1 with hN
  refine ⟨N, fun p hp => ?_⟩
  have hp1 : 1 ≤ p := le_trans (le_max_right _ _) hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have h := hprefix p (le_trans (le_max_left _ _) hp)
  rw [CFDiscLt, List.length_map, List.length_range] at h
  rw [Real.dist_eq]
  have heq : (countOccurrences v ((List.range p).map (cfDigit y)) : ℝ) / p - γv
      = ((countOccurrences v ((List.range p).map (cfDigit y)) : ℝ) - γv * p) / p := by
    field_simp
  rw [heq, abs_div, abs_of_pos hpR, div_lt_iff₀ hpR]
  calc |(countOccurrences v ((List.range p).map (cfDigit y)) : ℝ) - γv * p|
      < 2 * (2 * (ε / 5)) * p := h
    _ ≤ ε * p := by nlinarith

/-! ## The orbit-equidistribution wrapper -/

/-- **Abstract chain orbit equidistribution.**  Under the same chain +
goodness + dominance hypotheses, an irrational limit point `y ∈ (0,1)` of the
chain has equidistributing Gauss orbit: `blockCount (cfCylinder v) p y / p →
γ(I_v)` for every genuine `v`.  This is exactly the `CFOrbitEquidist` payload
the interleaved schedule consumes for BOTH streams.  Combines the window-limit
`chain_cf_digit_freq_tendsto` with the orbit↔window bridge
`blockCount_sub_countOccurrences_bounds` (gap `≤ |v|`, vanishing). -/
theorem chain_orbit_equidist (w : ℕ → List ℕ)
    (hext : ∀ s, ∃ u, u ≠ [] ∧ w (s + 1) = w s ++ u)
    {y : ℝ} (hirr : Irrational y) (hy01 : y ∈ Set.Ioo (0 : ℝ) 1)
    (hy : ∀ s, y ∈ cfCylinder (w s))
    (hfreq : ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      (∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s →
        |(countOccurrences v (chainApp w s) : ℝ) - (gaussMeasure (cfCylinder v)).toReal
            * (chainApp w s).length|
          < ε * (chainApp w s).length - ((v.length : ℝ) - 1)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ s₀, ∀ s, s₀ ≤ s →
        ((chainApp w s).length : ℝ) + ((v.length : ℝ) - 1)
          < ε * (w s).length)) :
    ∀ v : List ℕ, v ≠ [] → (∀ a ∈ v, 1 ≤ a) →
      Filter.Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ))
        Filter.atTop (nhds (gaussMeasure (cfCylinder v)).toReal) := by
  intro v hne hpos
  set γv := (gaussMeasure (cfCylinder v)).toReal with hγ
  obtain ⟨hγ0, hγ1⟩ := gaussMeasure_toReal_mem_Icc (cfCylinder v)
  obtain ⟨hgood, hdom⟩ := hfreq v hne hpos
  have horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0 : ℝ) 1 :=
    fun j => (irrational_orbit y hirr hy01 j).2
  set A : ℕ → ℕ := fun p => countOccurrences v ((List.range p).map (cfDigit y)) with hA
  set B : ℕ → ℝ := fun p => blockCount (cfCylinder v) p y with hB
  have hAfreq : Tendsto (fun p => (A p : ℝ) / (p : ℝ)) atTop (nhds γv) :=
    chain_cf_digit_freq_tendsto w hext hy v hne hγ0 hγ1 hgood hdom
  have hbnds : ∀ p, (A p : ℝ) ≤ B p ∧ B p ≤ (A p : ℝ) + v.length := by
    intro p
    have h := blockCount_sub_countOccurrences_bounds horb v hne 0 p
    simp only [Function.iterate_zero_apply, Nat.zero_add] at h
    exact h
  have hzero : Tendsto (fun p : ℕ => (v.length : ℝ) / (p : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hupp : Tendsto (fun p => (A p : ℝ) / (p : ℝ) + (v.length : ℝ) / (p : ℝ))
      atTop (nhds γv) := by simpa using hAfreq.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hAfreq hupp ?_ ?_
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
      gcongr
      exact (hbnds p).1
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
      rw [← add_div]
      gcongr
      linarith [(hbnds p).2]

end NormalNumbers
