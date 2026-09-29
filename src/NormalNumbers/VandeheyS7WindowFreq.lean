/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-WN: CF-normality computes the frequency of EVERY finite-window event

S7-WC split the crux's state into (far-past state, `L`-digit window).  This module supplies what
the window half needs, and it is the only place in the chain where CF-normality of the input does
real work on a *joint* quantity rather than on a marginal.

For a finite set `S` of words all of one length `K` — i.e. an arbitrary event depending on `K`
consecutive input digits — the visit frequency of a CF-normal `y` to the corresponding union of
cylinders converges to its Gauss mass:

    (1/p) · #{ i < p : the K-window of y at i lies in S }  →  Σ_{v ∈ S} γ(I_v)
                                                             (`tendsto_windowFreq`)

Two ingredients: `blockCount_tendsto_of_isCFNormal` (the converse of `isCFNormal_of_orbit_freq`,
same `|v|`-boundary bridge, squeeze reversed), and exact additivity of the block count over a
same-length family (`blockCount_biUnion_eq_sum`), which holds because same-length cylinders are
disjoint (`cfCylinder_disjoint`).

## What it buys the crux

By S7-WC the tested predicate at time `n` is a function of `(s_{n−L}, x_{n−L} … x_{n−1})` and of
`x_n …`.  Freeze the far-past state: what is left is a finite-window event, and this module says
its frequency is *exactly* its Gauss mass — no slack, no modulus, no hypothesis beyond normality
of `x`.  So the entire remaining gap in the crux is the dependence on `s_{n−L}`, and directive
fact (α)'s obstruction does not touch this half.

## Guard rule

Content locator: `blockCount_biUnion_eq_sum` is where disjointness is consumed — for a family
with repeated masses the sum would over-count and the limit would exceed the union's mass.
Degenerate case: `S = ∅` gives both sides `0`, and `S` = all words of length `K` gives frequency
`1`, matching `Σ γ(I_v) = 1` over a full level.
-/
import NormalNumbers.CFOrbitFreq
import NormalNumbers.VandeheyMixing

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **The converse bridge.**  A CF-normal point's orbit block-count frequency converges to the
cylinder's Gauss mass. -/
theorem blockCount_tendsto_of_isCFNormal {y : ℝ} (hy : IsCFNormal y)
    (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (hne : v ≠ []) (hpos : ∀ a ∈ v, 1 ≤ a) :
    Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ)) atTop
      (nhds (gaussMeasure (cfCylinder v)).toReal) := by
  set γv := (gaussMeasure (cfCylinder v)).toReal with hγ
  set B : ℕ → ℝ := fun p => blockCount (cfCylinder v) p y with hB
  set A : ℕ → ℕ := fun p => countOccurrences v ((List.range p).map (cfDigit y)) with hA
  have hbnds : ∀ p, (A p : ℝ) ≤ B p ∧ B p ≤ (A p : ℝ) + v.length := by
    intro p
    have h := blockCount_sub_countOccurrences_bounds horb v hne 0 p
    simp only [Function.iterate_zero_apply, Nat.zero_add] at h
    exact h
  have hAfreq : Tendsto (fun p => (A p : ℝ) / (p : ℝ)) atTop (nhds γv) := hy v hne hpos
  have hzero : Tendsto (fun p : ℕ => (v.length : ℝ) / (p : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hhigh : Tendsto (fun p => (A p : ℝ) / (p : ℝ) + (v.length : ℝ) / (p : ℝ))
      atTop (nhds γv) := by simpa using hAfreq.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hAfreq hhigh ?_ ?_
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
      exact (hbnds p).2

/-- The indicator of a same-length union splits as a sum. -/
lemma blockIndic_biUnion_eq_sum {S : Finset (List ℕ)} {K : ℕ}
    (hlen : ∀ v ∈ S, v.length = K) (t : ℝ) :
    blockIndic (⋃ v ∈ S, cfCylinder v) t = ∑ v ∈ S, blockIndic (cfCylinder v) t := by
  classical
  by_cases h : ∃ v ∈ S, t ∈ cfCylinder v
  · obtain ⟨v, hvS, hvt⟩ := h
    have hmem : t ∈ ⋃ v ∈ S, cfCylinder v := Set.mem_biUnion hvS hvt
    rw [blockIndic, Set.indicator_of_mem hmem]
    rw [Finset.sum_eq_single v]
    · rw [blockIndic, Set.indicator_of_mem hvt]
    · intro u huS hune
      have hdisj := cfCylinder_disjoint (by rw [hlen u huS, hlen v hvS]) hune
      have : t ∉ cfCylinder u := fun hu => (Set.disjoint_left.1 hdisj hu) hvt
      rw [blockIndic, Set.indicator_of_notMem this]
    · intro hv; exact absurd hvS hv
  · push_neg at h
    have hmem : t ∉ ⋃ v ∈ S, cfCylinder v := by
      intro hu
      obtain ⟨v, hvS, hvt⟩ := Set.mem_iUnion₂.1 hu
      exact h v hvS hvt
    rw [blockIndic, Set.indicator_of_notMem hmem]
    refine (Finset.sum_eq_zero fun u huS => ?_).symm
    rw [blockIndic, Set.indicator_of_notMem (h u huS)]

/-- **Exact additivity** of the block count over a same-length family. -/
theorem blockCount_biUnion_eq_sum {S : Finset (List ℕ)} {K : ℕ}
    (hlen : ∀ v ∈ S, v.length = K) (p : ℕ) (y : ℝ) :
    blockCount (⋃ v ∈ S, cfCylinder v) p y = ∑ v ∈ S, blockCount (cfCylinder v) p y := by
  simp only [blockCount, birkhoffSum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => blockIndic_biUnion_eq_sum hlen _

/-- **S7-WN.**  CF-normality computes the frequency of every finite-window event exactly. -/
theorem tendsto_windowFreq {y : ℝ} (hy : IsCFNormal y)
    (horb : ∀ j : ℕ, gaussMap^[j] y ∈ Set.Ioo (0 : ℝ) 1)
    {S : Finset (List ℕ)} {K : ℕ} (hK : 0 < K) (hlen : ∀ v ∈ S, v.length = K)
    (hpos : ∀ v ∈ S, ∀ a ∈ v, 1 ≤ a) :
    Tendsto (fun p => blockCount (⋃ v ∈ S, cfCylinder v) p y / (p : ℝ)) atTop
      (nhds (∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal)) := by
  have hsum : Tendsto (fun p => ∑ v ∈ S, blockCount (cfCylinder v) p y / (p : ℝ)) atTop
      (nhds (∑ v ∈ S, (gaussMeasure (cfCylinder v)).toReal)) := by
    refine tendsto_finsetSum S fun v hvS => ?_
    have hne : v ≠ [] := by
      intro hv
      have hlv := hlen v hvS
      rw [hv] at hlv
      simp at hlv
      omega
    exact blockCount_tendsto_of_isCFNormal hy horb v hne (hpos v hvS)
  refine hsum.congr fun p => ?_
  rw [← Finset.sum_div, ← blockCount_biUnion_eq_sum hlen]

end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.blockCount_tendsto_of_isCFNormal
#print axioms NormalNumbers.VandeheyS7.blockCount_biUnion_eq_sum
#print axioms NormalNumbers.VandeheyS7.tendsto_windowFreq

end Audit
