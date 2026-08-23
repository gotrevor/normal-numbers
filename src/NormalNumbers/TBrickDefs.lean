/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.BaryBlockCount
import NormalNumbers.DigitInterval

/-!
# W5 groundwork — d-ary cells and Becher–Yuhjtman Proposition 12

The t-brick machinery (B–Y Definitions 10–11, Lemma 13) nests a CF cylinder
inside one d-ary interval — or two consecutive ones — per base `d ≤ t`.
This file sets up the d-ary cells and proves Prop 12:

* `daryCell d m j r` — the union of `r` consecutive d-ary intervals of
  order `m` starting at index `j` (bricks use `r = 1` or `r = 2`).
* `volume_daryCell` — its Lebesgue measure is `r/d^m`.
* `interval_subset_daryCell_two` (**Prop 12**): every interval of length
  `< d^(−m)` lies in the union of two consecutive d-ary intervals of
  order `m` (explicitly, the one containing its left endpoint and its
  right neighbour).
-/

namespace NormalNumbers

open MeasureTheory

/-- The union of `r` consecutive d-ary intervals of order `m`, starting at
index `j` (as a half-open interval `[j/d^m, (j+r)/d^m)`). -/
def daryCell (d m : ℕ) (j : ℤ) (r : ℕ) : Set ℝ :=
  Set.Ico ((j : ℝ) / d ^ m) (((j : ℝ) + r) / d ^ m)

/-- The Lebesgue measure of `r` consecutive order-`m` cells is `r/d^m`. -/
theorem volume_daryCell (d m : ℕ) (hd : 1 ≤ d) (j : ℤ) (r : ℕ) :
    volume (daryCell d m j r) = ENNReal.ofReal ((r : ℝ) / d ^ m) := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ m := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  rw [daryCell, Real.volume_Ico]
  congr 1
  field_simp
  ring

/-- **B–Y Proposition 12**: an interval of length `< d^(−m)` is contained in
the union of two consecutive d-ary intervals of order `m` — namely the cell
of its left endpoint and the next one. -/
theorem interval_subset_daryCell_two (d m : ℕ) (hd : 1 ≤ d) {a c : ℝ}
    (h : c - a < 1 / d ^ m) :
    Set.Icc a c ⊆ daryCell d m ⌊a * d ^ m⌋ 2 := by
  have hdpow : (0 : ℝ) < (d : ℝ) ^ m := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  intro x hx
  obtain ⟨hax, hxc⟩ := hx
  constructor
  · -- `⌊a·d^m⌋/d^m ≤ a ≤ x`
    rw [div_le_iff₀ hdpow]
    calc (⌊a * d ^ m⌋ : ℝ) ≤ a * d ^ m := Int.floor_le _
      _ ≤ x * d ^ m := by nlinarith
  · -- `x ≤ c < a + d^(−m) < (⌊a·d^m⌋ + 2)/d^m`
    rw [lt_div_iff₀ hdpow]
    have hfl : a * d ^ m < (⌊a * d ^ m⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hc : c * d ^ m < a * d ^ m + 1 := by
      have := (sub_lt_iff_lt_add.1 h)
      calc c * d ^ m < (1 / d ^ m + a) * d ^ m := by nlinarith
        _ = a * d ^ m + 1 := by field_simp; ring
    push_cast
    nlinarith

attribute [local instance] Classical.propDecidable

/-- The `ε`-bad blocks of length `k` in base `d` — the Lemma 8 filter:
some digit's count deviates from the fair share `k/d` by at least `εk`. -/
noncomputable def badBlocks (d k : ℕ) (ε : ℝ) : Finset (Fin k → Fin d) :=
  Finset.univ.filter fun u =>
    ∃ s : Fin d, ε * k ≤ |(digitCount s u : ℝ) - k / d|

/-- Lemma 8 in `badBlocks` form. -/
theorem card_badBlocks_le (d k : ℕ) (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεd : (d : ℝ) * ε ≤ 1) :
    ((badBlocks d k ε).card : ℝ)
      ≤ 2 * (d : ℝ) ^ (k + 1) * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) := by
  have h := card_baryDiscrepancy_ge_le d k hd hε0 hεd
  calc ((badBlocks d k ε).card : ℝ)
      = ((Finset.univ.filter fun u : Fin k → Fin d =>
          ∃ s : Fin d, ε * k ≤ |(digitCount s u : ℝ) - k / d|).card : ℝ) := by
        rw [badBlocks]
    _ ≤ _ := by exact_mod_cast h
  
/-- **The d-ary bad zone is exponentially small**: inside one d-ary cell of
order `m0`, the union of the order-`(m0+k)` sub-cells carrying an `ε`-bad
new block has measure at most `2d·e^{−dε²k/6}·d^{−m0}`, i.e. `2d·e^{−dε²k/6}`
times the measure of the cell. -/
theorem volume_daryBadZone_le (d m0 k : ℕ) (hd : 1 ≤ d) (j0 : ℤ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεd : (d : ℝ) * ε ≤ 1) :
    volume (⋃ β ∈ badBlocks d k ε,
      daryCell d (m0 + k)
        (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1)
      ≤ ENNReal.ofReal
          (2 * d * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) / d ^ m0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc volume (⋃ β ∈ badBlocks d k ε,
      daryCell d (m0 + k)
        (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1)
      ≤ ∑ β ∈ badBlocks d k ε,
          volume (daryCell d (m0 + k)
            (j0 * d ^ k + blockNatVal d (List.ofFn fun i => (β i : ℕ))) 1) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _β ∈ badBlocks d k ε,
          ENNReal.ofReal ((1 : ℝ) / d ^ (m0 + k)) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [volume_daryCell d (m0 + k) hd _ 1]
        norm_num
    _ = ENNReal.ofReal (((badBlocks d k ε).card : ℝ) / d ^ (m0 + k)) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal
          ((2 * (d : ℝ) ^ (k + 1) * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6))
            / d ^ (m0 + k)) := by
        apply ENNReal.ofReal_le_ofReal
        have hcard := card_badBlocks_le d k hd hε0 hεd
        gcongr
    _ = ENNReal.ofReal
          (2 * d * Real.exp (-((d : ℝ) * ε ^ 2 * k) / 6) / d ^ m0) := by
        congr 1
        rw [pow_add, pow_succ]
        field_simp
        ring

end NormalNumbers
