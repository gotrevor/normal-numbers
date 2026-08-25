/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFBlockFreq
import NormalNumbers.Counting

/-!
# W5 groundwork — orbit block counts vs digit-word window counts

`chebyshev_blockCount_brick` (W4) controls the *orbit* count
`blockCount (cfCylinder v) n (T^s x)`; the refinement discrepancy of
Definition 11 is about the *finite digit word* via `countOccurrences`.
This file bridges the two for points whose Gauss orbit stays in `(0,1)`:

* `blockCount_eq_card_matches` — the orbit count is the number of matched
  windows of `v` in the digit stream starting at offset `s`;
* `blockCount_sub_countOccurrences_bounds` — the orbit count and the
  fitting-window count of `v` in the length-`n` digit word differ by at
  most `|v|` boundary windows.

Everything is pointwise counting; the only analytic fact used is that
cylinder membership is digit-defined.
-/

namespace NormalNumbers

open Finset

/-- On a full orbit, membership of `T^m x` in a cylinder is a digit-window
match at offset `m`. -/
theorem iterate_mem_cfCylinder_iff {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (m : ℕ) :
    gaussMap^[m] x ∈ cfCylinder v ↔ MatchesAt (cfDigit x) v m := by
  rw [cfCylinder]
  constructor
  · rintro ⟨-, hdig⟩ j hj
    have := hdig j hj
    rwa [cfDigit, ← Function.iterate_add_apply, Nat.add_comm j m] at this
  · intro hmatch
    refine ⟨horb m, fun j hj => ?_⟩
    have := hmatch j hj
    rwa [cfDigit, ← Function.iterate_add_apply, Nat.add_comm j m]

/-- The orbit block count is a cardinality of matched windows in the digit
stream. -/
theorem blockCount_eq_card_matches {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (s n : ℕ) :
    blockCount (cfCylinder v) n (gaussMap^[s] x)
      = (((Finset.range n).filter
          (fun j => MatchesAt (cfDigit x) v (s + j))).card : ℝ) := by
  rw [blockCount_apply]
  have hterm : ∀ k : ℕ,
      blockIndic (cfCylinder v) (gaussMap^[k] (gaussMap^[s] x))
        = if MatchesAt (cfDigit x) v (s + k) then (1 : ℝ) else 0 := by
    intro k
    rw [← Function.iterate_add_apply, Nat.add_comm k s]
    rw [blockIndic]
    by_cases h : gaussMap^[s + k] x ∈ cfCylinder v
    · rw [Set.indicator_of_mem h,
        if_pos ((iterate_mem_cfCylinder_iff horb v (s + k)).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        if_neg (fun hm => h ((iterate_mem_cfCylinder_iff horb v (s + k)).2 hm))]
  simp only [hterm]
  rw [Finset.sum_boole]

/-- **The bridge**: for a full orbit, the orbit block count at offset `s`
and the fitting-window count of `v` in the digit word
`(cfDigit x s, …, cfDigit x (s+n−1))` differ by at most `|v|`. -/
theorem blockCount_sub_countOccurrences_bounds {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (hv : v ≠ []) (s n : ℕ) :
    (countOccurrences v
        ((List.range n).map (fun i => cfDigit x (s + i))) : ℝ)
      ≤ blockCount (cfCylinder v) n (gaussMap^[s] x) ∧
    blockCount (cfCylinder v) n (gaussMap^[s] x)
      ≤ countOccurrences v
          ((List.range n).map (fun i => cfDigit x (s + i))) + v.length := by
  set s' : ℕ → ℕ := fun i => cfDigit x (s + i) with hs'
  have hshift : ∀ j, MatchesAt s' v j ↔ MatchesAt (cfDigit x) v (s + j) := by
    intro j
    constructor <;> intro h i hi
    · have hthis := h i hi
      simp only [hs'] at hthis
      rwa [← Nat.add_assoc] at hthis
    · show cfDigit x (s + (j + i)) = v.getD i 0
      rw [← Nat.add_assoc]
      exact h i hi
  have hcards : ((Finset.range n).filter (fun j => MatchesAt s' v j)).card
      = ((Finset.range n).filter
          (fun j => MatchesAt (cfDigit x) v (s + j))).card := by
    congr 1
    apply Finset.filter_congr
    intro j _
    simp [hshift j]
  obtain ⟨h1, h2⟩ := card_filter_matchesAt_le s' v hv n
  rw [blockCount_eq_card_matches horb v s n, ← hcards]
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- **Orbit block-count splits at a pinned prefix** (z-transfer conditional core).  For a
full-orbit real `x` and `L ≤ n`, the length-`n` orbit count of `cfCylinder v` from `x` equals
the count of `v`-matches in the FIRST `L` digit windows plus the length-`(n−L)` orbit count from
the SHIFTED orbit `gaussMap^[L] x`.  Pure partition of the window index set `range n = range L ⊎
[L,n)`.  This is the exact decomposition behind the ψ-conditional z-Chebyshev: within a cylinder
that pins the first `L` z-digits, the prefix count is COMMON to all points, so the discrepancy at
scale `n` is driven by the shifted count at scale `n−L` — which `chebyshev_blockCount_brick`
controls with density `O(1/(n−L))` (relative), not the too-weak absolute `O(1/n)`. -/
theorem blockCount_split {x : ℝ}
    (horb : ∀ j : ℕ, gaussMap^[j] x ∈ Set.Ioo (0 : ℝ) 1)
    (v : List ℕ) (L n : ℕ) (hLn : L ≤ n) :
    blockCount (cfCylinder v) n x
      = (((Finset.range L).filter (fun j => MatchesAt (cfDigit x) v j)).card : ℝ)
        + blockCount (cfCylinder v) (n - L) (gaussMap^[L] x) := by
  have hx0 : blockCount (cfCylinder v) n x = blockCount (cfCylinder v) n (gaussMap^[0] x) := by
    rw [Function.iterate_zero_apply]
  rw [hx0, blockCount_eq_card_matches horb v 0 n, blockCount_eq_card_matches horb v L (n - L)]
  simp only [Nat.zero_add]
  have hn : n = L + (n - L) := by omega
  have hdisj : Disjoint (Finset.range L) ((Finset.range (n - L)).map (addLeftEmbedding L)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hb
    obtain ⟨k, _, rfl⟩ := hb
    omega
  rw [← Nat.cast_add]
  congr 1
  conv_lhs => rw [hn, Finset.range_add, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    Finset.filter_map, Finset.card_map]
  simp only [Function.comp, addLeftEmbedding_apply]

/-- **ψ-conditional (pinned-prefix) z-Chebyshev.**  Within the cylinder `cfCylinder wz`,
whose first `L = |wz|` digits are pinned, the mass of full-orbit points `z` whose length-`n`
block frequency of `cfCylinder v` deviates from `γ(cfCylinder v)` by `≥ δ` is controlled by the
*relative* density `O(1/(n−L))`, NOT the absolute `O(1/n)`.  Route: `blockCount_split` peels the
COMMON pinned-prefix count (`C ∈ [0,L]`, contributing `≤ L/n` to the frequency) off the scale-`n`
count, leaving the shifted scale-`(n−L)` count on `gaussMap^[L] z`, which
`chebyshev_blockCount_brick` at base `wz` bounds.  The slack `2L ≤ δ·n` guarantees the peeled
prefix cannot itself explain a `δ`-deviation, so a scale-`n` `δ`-bad point is a scale-`(n−L)`
`(δ/2)`-bad point on the shifted orbit.  This is the analytic lemma the single-stream z-side
rests on. -/
theorem chebyshev_blockCount_brick_psi_conditional
    (wz v : List ℕ) (hposw : ∀ a ∈ wz, 1 ≤ a) (hposv : ∀ a ∈ v, 1 ≤ a)
    (n : ℕ) (hLn : wz.length < n) {δ : ℝ} (hδ : 0 < δ)
    (hslack : 2 * (wz.length : ℝ) ≤ δ * n) :
    (gaussMeasure {z : ℝ | z ∈ cfCylinder wz ∧
        (∀ j : ℕ, gaussMap^[j] z ∈ Set.Ioo (0 : ℝ) 1) ∧
        δ ≤ |blockCount (cfCylinder v) n z / n -
          (gaussMeasure (cfCylinder v)).toReal|}).toReal ≤
      7 * ((8 * v.length + 80) * (gaussMeasure (cfCylinder v)).toReal /
        ((δ / 2) ^ 2 * (n - wz.length))) * (gaussMeasure (cfCylinder wz)).toReal := by
  set L := wz.length with hLdef
  set γv := (gaussMeasure (cfCylinder v)).toReal with hγv
  have hL0 : 0 < n - L := by omega
  -- the shifted (scale `n−L`, tol `δ/2`) brick bound at base `wz`
  have hchel := chebyshev_blockCount_brick wz v hposw hposv (n - L) hL0 (half_pos hδ)
  rw [← hLdef] at hchel
  have hmcastT : ((n - L : ℕ) : ℝ) = (n : ℝ) - (L : ℝ) := by exact_mod_cast Nat.cast_sub (le_of_lt hLn)
  rw [hmcastT] at hchel
  -- the pinned-prefix bad set is contained in the shifted brick-bad set
  have hsub : {z : ℝ | z ∈ cfCylinder wz ∧
      (∀ j : ℕ, gaussMap^[j] z ∈ Set.Ioo (0 : ℝ) 1) ∧
      δ ≤ |blockCount (cfCylinder v) n z / n - γv|} ⊆
      cfCylinder wz ∩ (gaussMap^[L]) ⁻¹'
        {x ∈ Set.Ioo (0 : ℝ) 1 |
          δ / 2 ≤ |blockCount (cfCylinder v) (n - L) x / ((n : ℝ) - (L : ℝ)) - γv|} := by
    rintro z ⟨hzcyl, hzorb, hzbad⟩
    refine ⟨hzcyl, hzorb L, ?_⟩
    -- notation
    set nn : ℝ := (n : ℝ) with hnn
    set LL : ℝ := (L : ℝ) with hLL
    have hnpos : 0 < nn := by rw [hnn]; exact_mod_cast (by omega : 0 < n)
    have hLL_nonneg : 0 ≤ LL := by rw [hLL]; positivity
    have hmcast : ((n - L : ℕ) : ℝ) = nn - LL := by rw [hnn, hLL]; exact_mod_cast Nat.cast_sub (le_of_lt hLn)
    have hmpos : 0 < nn - LL := by rw [← hmcast]; exact_mod_cast hL0
    set Bn : ℝ := blockCount (cfCylinder v) n z with hBn
    set Bf : ℝ := blockCount (cfCylinder v) (n - L) (gaussMap^[L] z) with hBf
    set C : ℝ := (((Finset.range L).filter (fun j => MatchesAt (cfDigit z) v j)).card : ℝ) with hC
    -- split
    have hsplit : Bn = C + Bf := blockCount_split hzorb v L n (le_of_lt hLn)
    -- bounds on the pieces
    have hC0 : 0 ≤ C := by rw [hC]; exact_mod_cast Nat.zero_le _
    have hCL : C ≤ LL := by
      rw [hC, hLL]; exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_range L)
    have hBf0 : 0 ≤ Bf := by
      rw [hBf, blockCount_apply]
      exact Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hBfle : Bf ≤ nn - LL := by
      rw [hBf, blockCount_apply]
      calc ∑ k ∈ Finset.range (n - L), blockIndic (cfCylinder v) (gaussMap^[k] (gaussMap^[L] z))
          ≤ ∑ _k ∈ Finset.range (n - L), (1 : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            unfold blockIndic
            by_cases h : gaussMap^[k] (gaussMap^[L] z) ∈ cfCylinder v
            · simp [Set.indicator_of_mem h]
            · simp [Set.indicator_of_notMem h]
        _ = ((n - L : ℕ) : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        _ = nn - LL := hmcast
    -- the peeled prefix perturbs the frequency by at most `LL/nn`
    set D : ℝ := C / nn - Bf * LL / ((nn - LL) * nn) with hD
    have hident : Bf / (nn - LL) - γv = (Bn / nn - γv) - D := by
      rw [hsplit, hD]; field_simp; ring
    have hDbound : |D| ≤ LL / nn := by
      have hE0 : 0 ≤ Bf * LL / ((nn - LL) * nn) :=
        div_nonneg (mul_nonneg hBf0 hLL_nonneg) (mul_nonneg hmpos.le hnpos.le)
      have hELL : Bf * LL / ((nn - LL) * nn) ≤ LL / nn := by
        rw [div_le_div_iff₀ (mul_pos hmpos hnpos) hnpos]
        nlinarith [mul_le_mul_of_nonneg_right hBfle (mul_nonneg hLL_nonneg hnpos.le)]
      have hCnn0 : 0 ≤ C / nn := div_nonneg hC0 hnpos.le
      have hCnn : C / nn ≤ LL / nn := by
        rw [div_le_div_iff₀ hnpos hnpos]; nlinarith [hCL, hnpos.le]
      rw [hD, abs_le]
      constructor <;> nlinarith [hE0, hELL, hCnn0, hCnn]
    -- assemble
    have hLLnn : LL / nn ≤ δ / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num : (0:ℝ) < 2)]
      linarith [hslack]
    rw [hident]
    calc δ / 2 = δ - δ / 2 := by ring
      _ ≤ |Bn / nn - γv| - |D| := by
          have := hzbad
          rw [hBn, hnn] at this ⊢
          linarith [hDbound, hLLnn, this]
      _ ≤ |(Bn / nn - γv) - D| := abs_sub_abs_le_abs_sub _ _
  calc (gaussMeasure {z : ℝ | z ∈ cfCylinder wz ∧
          (∀ j : ℕ, gaussMap^[j] z ∈ Set.Ioo (0 : ℝ) 1) ∧
          δ ≤ |blockCount (cfCylinder v) n z / n - γv|}).toReal
      ≤ (gaussMeasure (cfCylinder wz ∩ (gaussMap^[L]) ⁻¹'
          {x ∈ Set.Ioo (0 : ℝ) 1 | δ / 2 ≤ |blockCount (cfCylinder v) (n - L) x / ((n : ℝ) - (L : ℝ)) -
            γv|})).toReal :=
        ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_mono hsub)
    _ ≤ 7 * ((8 * v.length + 80) * γv / ((δ / 2) ^ 2 * (n - L))) *
          (gaussMeasure (cfCylinder wz)).toReal := hchel

end NormalNumbers
