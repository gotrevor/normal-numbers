/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SM: the straddle set has mass `≍ √w` — the quantitative heart of the stall rate

S7-LD reduced `MeanSlack` to the stall rate: the machine stalls at exactly the times when its
image, an interval of length `w = width`, **straddles** a digit endpoint `1/k`.  This module
computes the measure of the set of positions where an interval of length `w` straddles, and the
answer is the reason `MeanSlack` is in doubt:

    K·w  ≤  volume (straddleSet w)   whenever  1 ≤ K  and  w ≤ 1/(K(K+1))     (`straddle_volume_ge`)
    volume (straddleSet w) ≤ 2·√w                                             (`straddle_volume_le`)

Taking `K ≍ 1/√w` in the first makes both bounds `≍ √w`.

* **Lower bound.**  The `K` intervals `(1/k − w, 1/k)`, `k = 1 … K`, all lie in `straddleSet w`,
  and they are pairwise disjoint as soon as `w` is below the smallest gap `1/(K(K+1))`.
* **Upper bound.**  Endpoints `1/k ≥ √w` number at most `1/√w` and contribute `w` each; the rest
  of the straddling positions lie in `(0, √w)`.

## Why this decides the route

The stall rate is `≍ √w`, not `≍ w`.  Since the lag is monotone (S7-LD), a stall rate `≍ √w` with
`w ≍ e^{−λ·lag}` gives `d(lag)/dn ≍ e^{−λ·lag/2}`, i.e. `lag n ≍ (2/λ)·log n` — **logarithmic, not
bounded**.  That makes `Σ_{m<q} slack m ≍ q log q` and `MeanSlack` (`≤ A·q`) FALSE by exactly one
log factor, while `ClockLinear` — which is all the front's clock needs — survives comfortably.
The consequence for the front is that `WidthFreqBound` must be taken with `η = η(q) → 0`, not at a
fixed `η`.  This module supplies the mass estimate; the frequency statement (the orbit's visits to
`straddleSet`) is the next step, and it is a CF-normality statement about a finite union of
intervals, not a new wall.

## Guard rule

Content locator: `straddle_volume_ge` at `K = 1` is the single interval `(1 − w, 1)`, so all the
content is in the disjointness for `k ≥ 2`.  Degenerate cases: `w ≤ 0` makes `straddleSet` empty
(`straddleSet_of_nonpos`); `K = 1` forces only `w ≤ 1/2`.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace NormalNumbers.VandeheyS7

open MeasureTheory Set

/-- The positions at which an interval of length `w` straddles a continued-fraction endpoint. -/
def straddleSet (w : ℝ) : Set ℝ :=
  {z | ∃ k : ℕ, 1 ≤ k ∧ z ≤ 1 / (k : ℝ) ∧ 1 / (k : ℝ) < z + w}

lemma straddleSet_of_nonpos {w : ℝ} (hw : w ≤ 0) : straddleSet w = ∅ := by
  ext z
  simp only [straddleSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨k, -, h1, h2⟩
  linarith

/-- The `k`-th straddling window. -/
lemma Ioo_subset_straddleSet {w : ℝ} (k : ℕ) (hk : 1 ≤ k) :
    Ioo (1 / (k : ℝ) - w) (1 / (k : ℝ)) ⊆ straddleSet w := by
  intro z hz
  exact ⟨k, hk, hz.2.le, by linarith [hz.1]⟩

/-- **The lower bound.**  `K` disjoint windows of length `w`. -/
theorem straddle_volume_ge {w : ℝ} (hw : 0 < w) {K : ℕ} (hK : 1 ≤ K)
    (hwK : w ≤ 1 / ((K : ℝ) * ((K : ℝ) + 1))) :
    ENNReal.ofReal ((K : ℝ) * w) ≤ volume (straddleSet w) := by
  classical
  have hKpos : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  -- gaps between consecutive endpoints dominate `w` up to `K`
  have hgap : ∀ k : ℕ, 1 ≤ k → k ≤ K → 1 / ((k : ℝ) + 1) ≤ 1 / (k : ℝ) - w := by
    intro k hk1 hkK
    have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkK' : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hkK
    have hstep : w ≤ 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
      refine le_trans hwK ?_
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hid : 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
      field_simp; ring
    linarith
  set F : Finset ℕ := Finset.Icc 1 K with hF
  set I : ℕ → Set ℝ := fun k => Ioo (1 / (k : ℝ) - w) (1 / (k : ℝ)) with hI
  have key : ∀ k l : ℕ, 1 ≤ k → k ≤ K → k < l → Disjoint (I k) (I l) := by
    intro k l hk1 hkK hkl
    refine Set.disjoint_left.mpr ?_
    intro z hzk hzl
    have h1 : 1 / (l : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hkl
      linarith
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / (k : ℝ) - w := hgap k hk1 hkK
    have hz1 := hzk.1
    have hz2 := hzl.2
    linarith
  have hdisj : (F : Set ℕ).PairwiseDisjoint I := by
    intro k hk l hl hkl
    have hk' := Finset.mem_Icc.mp (by simpa [hF] using hk)
    have hl' := Finset.mem_Icc.mp (by simpa [hF] using hl)
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l hk'.1 hk'.2 h
    · exact (key l k hl'.1 hl'.2 h).symm
  have hsub : (⋃ k ∈ F, I k) ⊆ straddleSet w := by
    refine Set.iUnion₂_subset fun k hk => ?_
    exact Ioo_subset_straddleSet k (Finset.mem_Icc.mp hk).1
  have hmeas : ∀ k ∈ F, MeasurableSet (I k) := fun k _ => measurableSet_Ioo
  have hvol : volume (⋃ k ∈ F, I k) = ∑ k ∈ F, volume (I k) :=
    measure_biUnion_finset hdisj hmeas
  have heach : ∀ k ∈ F, volume (I k) = ENNReal.ofReal w := by
    intro k _
    rw [hI]
    simp only [Real.volume_Ioo]
    congr 1
    ring
  have hsum : ∑ k ∈ F, volume (I k) = (F.card : ℕ) • ENNReal.ofReal w := by
    rw [Finset.sum_congr rfl heach, Finset.sum_const]
  have hcard : F.card = K := by rw [hF, Nat.card_Icc]; omega
  calc ENNReal.ofReal ((K : ℝ) * w) = (K : ℕ) • ENNReal.ofReal w := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (by positivity)]
    _ = ∑ k ∈ F, volume (I k) := by rw [hsum, hcard]
    _ = volume (⋃ k ∈ F, I k) := hvol.symm
    _ ≤ volume (straddleSet w) := measure_mono hsub

/-- **The upper bound.**  Endpoints `1/k` with `k ≤ K` contribute `w` each; everything the deeper
endpoints can straddle lies in `(−w, 1/K)`. -/
theorem straddle_volume_le {w : ℝ} (hw : 0 < w) {K : ℕ} (hK : 1 ≤ K) :
    volume (straddleSet w) ≤ ENNReal.ofReal ((K : ℝ) * w + (1 / (K : ℝ) + w)) := by
  classical
  have hKpos : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  set F : Finset ℕ := Finset.Icc 1 K with hF
  set I : ℕ → Set ℝ := fun k => Ioc (1 / (k : ℝ) - w) (1 / (k : ℝ)) with hI
  set T : Set ℝ := Ioc (-w) (1 / (K : ℝ)) with hT
  have hsub : straddleSet w ⊆ (⋃ k ∈ F, I k) ∪ T := by
    rintro z ⟨k, hk1, h1, h2⟩
    have hkpos : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk1
    by_cases hkK : k ≤ K
    · exact Or.inl (Set.mem_biUnion (by simp [hF]; omega) ⟨by linarith, h1⟩)
    · push_neg at hkK
      have hle : 1 / (k : ℝ) ≤ 1 / (K : ℝ) :=
        one_div_le_one_div_of_le hKpos (by exact_mod_cast hkK.le)
      have hinv : (0:ℝ) < 1 / (k : ℝ) := by positivity
      exact Or.inr ⟨by linarith, le_trans h1 hle⟩
  have hTvol : volume T ≤ ENNReal.ofReal (1 / (K : ℝ) + w) := by
    rw [hT, Real.volume_Ioc]
    exact le_of_eq (by congr 1; ring)
  have hUvol : volume (⋃ k ∈ F, I k) ≤ ENNReal.ofReal ((K : ℝ) * w) := by
    refine le_trans (measure_biUnion_finset_le F I) ?_
    have heach : ∀ k ∈ F, volume (I k) = ENNReal.ofReal w := by
      intro k _
      rw [hI]; simp only [Real.volume_Ioc]; congr 1; ring
    rw [Finset.sum_congr rfl heach, Finset.sum_const]
    have hcard : F.card = K := by rw [hF, Nat.card_Icc]; omega
    rw [hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast K,
      ← ENNReal.ofReal_mul (by positivity)]
  calc volume (straddleSet w) ≤ volume ((⋃ k ∈ F, I k) ∪ T) := measure_mono hsub
    _ ≤ volume (⋃ k ∈ F, I k) + volume T := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((K : ℝ) * w) + ENNReal.ofReal (1 / (K : ℝ) + w) :=
        add_le_add hUvol hTvol
    _ = ENNReal.ofReal ((K : ℝ) * w + (1 / (K : ℝ) + w)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm


end NormalNumbers.VandeheyS7

section Audit

#print axioms NormalNumbers.VandeheyS7.straddle_volume_ge
#print axioms NormalNumbers.VandeheyS7.straddle_volume_le

end Audit
