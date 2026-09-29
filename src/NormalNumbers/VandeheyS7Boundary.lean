/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Word
import NormalNumbers.CFDefs

/-!
# The trigger window: the depth-one boundary set has measure `O(√δ)`

Merging (`abs_sub_runWord_le`) says two output points are within `δ` of each other.  A CF digit
is `⌊1/x⌋`, so the digits agree UNLESS one of the points is within `δ` of a depth-one cylinder
endpoint `1/k`.  DIRECTION item 3 calls the good set a *trigger window* and asks for
`ρ(∂U) = 0`; this module makes that quantitative at depth one.

## The estimate, and why it is not immediate

The endpoints `1/k` are INFINITELY many and they accumulate at `0`, so the naive bound
"`2δ` per endpoint" diverges.  The correct split is by scale:

* below `2√δ` the neighbourhoods merge into each other and one simply discards the whole interval
  `(0, 2√δ)`, of measure `2√δ`;
* above `2√δ` only the endpoints with `k ≤ 1/√δ` are reachable — there are at most `1/√δ + 1` of
  them, contributing at most `2δ(1/√δ + 1) ≤ 4√δ`.

So `boundaryBad δ` has Lebesgue measure at most `6√δ` (`volume_boundaryBad_le`), and in
particular `→ 0`.  The rate `√δ`, not `δ`, is the real content: it is the price of the
accumulation at `0`, and it is why a digit CUTOFF is not needed here — a point worth recording,
since a cutoff would have to be carried through the whole Cesàro argument.

Since merging supplies `δ = 1/(fib(n-1) fib(n))`, which is exponentially small, `√δ` is still
exponentially small and the loss is harmless.

## Guard rule

Content locator: `mem_boundaryBad_of_close` — a point within `δ` of `1/k` really is in the set,
so the bound is about a nonempty obstruction and not a vacuous one.  Degenerate case:
`boundaryBad_eq_empty_of_nonpos` — for `δ ≤ 0` the set is empty, so all the content is in the
positive-`δ` regime.
-/

namespace NormalNumbers.VandeheyS7

open MeasureTheory Set

/-- Points of `(0,1)` within `δ` of a depth-one cylinder endpoint `1/k`. -/
def boundaryBad (δ : ℝ) : Set ℝ :=
  {x | x ∈ Ioo (0:ℝ) 1 ∧ ∃ k : ℕ, 1 ≤ k ∧ |x - (k:ℝ)⁻¹| < δ}

/-- Content locator: the set really does contain the points it is meant to. -/
theorem mem_boundaryBad_of_close {δ x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) {k : ℕ} (hk : 1 ≤ k)
    (h : |x - (k:ℝ)⁻¹| < δ) : x ∈ boundaryBad δ := ⟨hx, k, hk, h⟩

/-- Degenerate case: no content below `δ = 0`. -/
theorem boundaryBad_eq_empty_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) : boundaryBad δ = ∅ := by
  ext x
  simp only [boundaryBad, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨-, k, -, h⟩
  exact absurd (lt_of_lt_of_le h hδ) (not_lt.2 (abs_nonneg _))

/-- **The covering.**  Above the scale `2√δ` only finitely many endpoints are reachable. -/
theorem boundaryBad_subset {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    boundaryBad δ ⊆ Ioo (0:ℝ) (2 * Real.sqrt δ) ∪
      ⋃ k ∈ Finset.Icc 1 (Nat.ceil (Real.sqrt δ)⁻¹),
        Ioo ((k:ℝ)⁻¹ - δ) ((k:ℝ)⁻¹ + δ) := by
  rintro x ⟨⟨hx0, -⟩, k, hk, hclose⟩
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsle : Real.sqrt δ ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hδ1
  have hds : δ ≤ Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.le, hs, hsle]
  rcases lt_or_ge x (2 * Real.sqrt δ) with hlt | hge
  · exact Or.inl ⟨hx0, hlt⟩
  · refine Or.inr ?_
    obtain ⟨h1, h2⟩ := abs_lt.1 hclose
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
    have hinv : Real.sqrt δ < (k:ℝ)⁻¹ := by linarith
    have hkle : k ≤ Nat.ceil (Real.sqrt δ)⁻¹ := by
      have hklt : (k:ℝ) < (Real.sqrt δ)⁻¹ := by
        rw [lt_inv_comm₀ hs (by positivity)] at hinv
        exact hinv
      exact_mod_cast le_trans hklt.le (Nat.le_ceil _)
    simp only [Finset.mem_Icc, mem_iUnion, exists_prop]
    exact ⟨k, ⟨hk, hkle⟩, by constructor <;> linarith⟩

/-- **The boundary set is small, at rate `√δ`.**  This is the trigger window of DIRECTION item 3,
made quantitative at depth one: `volume (boundaryBad δ) ≤ 6 √δ`. -/
theorem volume_boundaryBad_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    volume (boundaryBad δ) ≤ ENNReal.ofReal (6 * Real.sqrt δ) := by
  classical
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  set K : ℕ := Nat.ceil (Real.sqrt δ)⁻¹ with hK
  have hcover := boundaryBad_subset hδ hδ1
  refine le_trans (measure_mono hcover) ?_
  refine le_trans (measure_union_le _ _) ?_
  have h1 : volume (Ioo (0:ℝ) (2 * Real.sqrt δ)) = ENNReal.ofReal (2 * Real.sqrt δ) := by
    rw [Real.volume_Ioo]; ring_nf
  have h2 : volume (⋃ k ∈ Finset.Icc 1 K, Ioo ((k:ℝ)⁻¹ - δ) ((k:ℝ)⁻¹ + δ))
      ≤ ∑ _k ∈ Finset.Icc 1 K, ENNReal.ofReal (2 * δ) := by
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Real.volume_Ioo]
    exact le_of_eq (by ring_nf)
  have hcard : (Finset.Icc 1 K).card = K := by simp
  have h3 : ∑ _k ∈ Finset.Icc 1 K, ENNReal.ofReal (2 * δ)
      = (K : ℕ) • ENNReal.ofReal (2 * δ) := by
    rw [Finset.sum_const, hcard]
  -- `K ≤ 1/√δ + 1`, so `K · 2δ ≤ 4√δ`
  have hKr : (K : ℝ) ≤ (Real.sqrt δ)⁻¹ + 1 := by
    have := Nat.ceil_lt_add_one (a := (Real.sqrt δ)⁻¹) (by positivity)
    linarith
  have hds : δ ≤ Real.sqrt δ := by
    have hsle : Real.sqrt δ ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hδ1
    nlinarith [Real.sq_sqrt hδ.le, hs, hsle]
  have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ.le
  have hKbound : (K : ℝ) * (2 * δ) ≤ 4 * Real.sqrt δ := by
    have hstep : (K : ℝ) * (2 * δ) ≤ ((Real.sqrt δ)⁻¹ + 1) * (2 * δ) := by
      apply mul_le_mul_of_nonneg_right hKr (by linarith)
    have hinv : (Real.sqrt δ)⁻¹ * (2 * δ) = 2 * Real.sqrt δ := by
      field_simp
      nlinarith [hsq]
    nlinarith [hstep, hinv, hds]
  calc volume (Ioo (0:ℝ) (2 * Real.sqrt δ))
        + volume (⋃ k ∈ Finset.Icc 1 K, Ioo ((k:ℝ)⁻¹ - δ) ((k:ℝ)⁻¹ + δ))
      ≤ ENNReal.ofReal (2 * Real.sqrt δ) + (K : ℕ) • ENNReal.ofReal (2 * δ) := by
        rw [h1, ← h3]; exact add_le_add le_rfl h2
    _ = ENNReal.ofReal (2 * Real.sqrt δ) + ENNReal.ofReal ((K : ℝ) * (2 * δ)) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (2 * Real.sqrt δ) + ENNReal.ofReal (4 * Real.sqrt δ) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hKbound)
    _ = ENNReal.ofReal (6 * Real.sqrt δ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-! ## Digit agreement off the boundary set

This is what the estimate is for.  Outside `boundaryBad δ` the first CF digit is LOCALLY
CONSTANT at scale `δ`, so merging (`abs_sub_runWord_le`) transfers directly: two output points
within `δ` of each other have the same first digit unless one of them is in a set of measure
`6√δ`.
-/

/-- `cfDigit x 0 = ⌊x⁻¹⌋₊`, unfolded. -/
theorem cfDigit_zero (x : ℝ) : cfDigit x 0 = ⌊x⁻¹⌋₊ := rfl

/-- The depth-one cylinder containing `u`: `1/(n+1) < u ≤ 1/n` for `n = ⌊1/u⌋₊ ≥ 1`. -/
theorem floor_inv_spec {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 ≤ ⌊u⁻¹⌋₊ ∧ ((⌊u⁻¹⌋₊ : ℝ) + 1)⁻¹ < u ∧ u ≤ ((⌊u⁻¹⌋₊ : ℝ))⁻¹ := by
  have hinv : 1 < u⁻¹ := by
    rw [lt_inv_comm₀ one_pos hu0]; simpa using hu1
  have hn1 : 1 ≤ ⌊u⁻¹⌋₊ := Nat.one_le_floor_iff _ |>.2 hinv.le
  have hnr : (1:ℝ) ≤ (⌊u⁻¹⌋₊ : ℝ) := by exact_mod_cast hn1
  have hfl : ((⌊u⁻¹⌋₊ : ℕ) : ℝ) ≤ u⁻¹ := Nat.floor_le (by positivity)
  have hfu : u⁻¹ < (⌊u⁻¹⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (u⁻¹)
    exact_mod_cast this
  refine ⟨hn1, ?_, ?_⟩
  · rw [inv_lt_comm₀ (by linarith) hu0]; exact hfu
  · rw [le_inv_comm₀ hu0 (by linarith)]; exact hfl

/-- If `1/(n+1) < v ≤ 1/n` with `n ≥ 1` then `cfDigit v 0 = n`. -/
theorem cfDigit_zero_eq_of_mem {v : ℝ} {n : ℕ} (hn : 1 ≤ n) (hv0 : 0 < v)
    (hlo : ((n : ℝ) + 1)⁻¹ < v) (hhi : v ≤ ((n : ℝ))⁻¹) : cfDigit v 0 = n := by
  have hnr : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) ≤ v⁻¹ := by rwa [le_inv_comm₀ (by linarith) hv0]
  have h2 : v⁻¹ < (n : ℝ) + 1 := (inv_lt_comm₀ (by linarith) hv0).1 hlo
  rw [cfDigit_zero]
  exact Nat.floor_eq_on_Ico _ _ ⟨h1, h2⟩

/-- **Digit agreement off the boundary set.**  If `u` is not within `δ` of any endpoint `1/k`
and `|u − v| < δ`, then `u` and `v` have the same first CF digit.  With
`volume_boundaryBad_le`, the exceptional `u` form a set of measure at most `6√δ`. -/
theorem cfDigit_zero_eq_of_not_boundaryBad {δ u v : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hbad : u ∉ boundaryBad δ) (hv0 : 0 < v) (huv : |u - v| < δ) :
    cfDigit v 0 = cfDigit u 0 := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hn1, hlo, hhi⟩ := floor_inv_spec hu0 hu1
  set n : ℕ := ⌊u⁻¹⌋₊ with hn
  have hnr : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- `u` is `δ`-far from BOTH endpoints of its own cylinder
  have hfar : ∀ k : ℕ, 1 ≤ k → δ ≤ |u - (k:ℝ)⁻¹| := by
    intro k hk
    by_contra hcon
    exact hbad ⟨⟨hu0, hu1⟩, k, hk, not_le.1 hcon⟩
  have hfar1 : δ ≤ |u - (n:ℝ)⁻¹| := hfar n hn1
  have hfar2 : δ ≤ |u - ((n:ℝ) + 1)⁻¹| := by
    have h := hfar (n + 1) (by omega)
    rwa [Nat.cast_add, Nat.cast_one] at h
  have hup : u ≤ (n:ℝ)⁻¹ - δ := by
    rcases abs_cases (u - (n:ℝ)⁻¹) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hfar1; linarith
    · rw [he] at hfar1; linarith
  have hdown : ((n:ℝ) + 1)⁻¹ + δ ≤ u := by
    rcases abs_cases (u - ((n:ℝ) + 1)⁻¹) with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hfar2; linarith
    · rw [he] at hfar2; linarith
  obtain ⟨h1, h2⟩ := abs_lt.1 huv
  rw [show cfDigit u 0 = n from rfl]
  refine cfDigit_zero_eq_of_mem hn1 hv0 ?_ ?_
  · linarith
  · linarith


section Audit

#print axioms boundaryBad_subset
#print axioms volume_boundaryBad_le
#print axioms cfDigit_zero_eq_of_not_boundaryBad

end Audit

end NormalNumbers.VandeheyS7
