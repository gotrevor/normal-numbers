/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Word
import NormalNumbers.CFDefs
import NormalNumbers.CFPin

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

/-- The interval version: `v` lies strictly inside `u`'s own depth-one cylinder.  Strict on both
sides, which is what keeps `gaussMap v ≠ 0` at the next step. -/
theorem cylinder_of_not_boundaryBad {δ u v : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hbad : u ∉ boundaryBad δ) (huv : |u - v| < δ) :
    1 ≤ cfDigit u 0 ∧ ((cfDigit u 0 : ℝ) + 1)⁻¹ < v ∧ v < ((cfDigit u 0 : ℝ))⁻¹ := by
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
  exact ⟨hn1, by linarith, by linarith⟩

/-- **Digit agreement off the boundary set.**  If `u` is not within `δ` of any endpoint `1/k`
and `|u − v| < δ`, then `u` and `v` have the same first CF digit.  With
`volume_boundaryBad_le`, the exceptional `u` form a set of measure at most `6√δ`. -/
theorem cfDigit_zero_eq_of_not_boundaryBad {δ u v : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hbad : u ∉ boundaryBad δ) (hv0 : 0 < v) (huv : |u - v| < δ) :
    cfDigit v 0 = cfDigit u 0 := by
  obtain ⟨hn1, hlo, hhi⟩ := cylinder_of_not_boundaryBad hu hbad huv
  exact cfDigit_zero_eq_of_mem hn1 hv0 hlo hhi.le

/-! ## One Gauss step: the scale degrades by the square of the digit

To go from depth one to depth `m`, iterate.  Two points in the SAME depth-one cylinder have
`gaussMap u − gaussMap v = u⁻¹ − v⁻¹` exactly — the integer part cancels because it is the same
integer — and therefore

    |gaussMap u − gaussMap v|  =  |u − v| / (u v)  ≤  (n+1)² |u − v| ,

`n` being the shared digit.  So each Gauss step costs a factor `(digit+1)²`, and a depth-`m`
agreement needs `δ` smaller than `∏ (aᵢ+1)^{-2}`.  Merging supplies `δ = 1/(fib(n-1)fib(n))`,
exponentially small, which is the right order of magnitude to pay this.
-/

/-- In a depth-one cylinder the integer part of `x⁻¹` is constant, so `gaussMap` is just
inversion. -/
theorem gaussMap_eq_sub {u : ℝ} {n : ℕ} (hn : 1 ≤ n) (hu0 : 0 < u)
    (hlo : ((n : ℝ) + 1)⁻¹ < u) (hhi : u ≤ ((n : ℝ))⁻¹) :
    gaussMap u = u⁻¹ - (n : ℝ) := by
  have hnr : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) ≤ u⁻¹ := by rwa [le_inv_comm₀ (by linarith) hu0]
  have h2 : u⁻¹ < (n : ℝ) + 1 := (inv_lt_comm₀ (by linarith) hu0).1 hlo
  have hfloor : ⌊u⁻¹⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hne : u ≠ 0 := hu0.ne'
  rw [gaussMap, if_neg hne, Int.fract, hfloor]
  norm_num

/-- **One Gauss step costs a factor `(n+1)²`.**  The integer part cancels exactly. -/
theorem abs_gaussMap_sub_le {u v : ℝ} {n : ℕ} (hn : 1 ≤ n) (hu0 : 0 < u) (hv0 : 0 < v)
    (hul : ((n : ℝ) + 1)⁻¹ < u) (huh : u ≤ ((n : ℝ))⁻¹)
    (hvl : ((n : ℝ) + 1)⁻¹ < v) (hvh : v ≤ ((n : ℝ))⁻¹) :
    |gaussMap u - gaussMap v| ≤ ((n : ℝ) + 1) ^ 2 * |u - v| := by
  have hnr : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : gaussMap u - gaussMap v = u⁻¹ - v⁻¹ := by
    rw [gaussMap_eq_sub hn hu0 hul huh, gaussMap_eq_sub hn hv0 hvl hvh]; ring
  have hid : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by field_simp
  rw [hd, hid, abs_div, abs_of_pos (by positivity : (0:ℝ) < u * v), abs_sub_comm]
  rw [div_le_iff₀ (by positivity)]
  have huv : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ ≤ u * v :=
    mul_le_mul hul.le hvl.le (by positivity) hu0.le
  have hsq : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ = (((n : ℝ) + 1) ^ 2)⁻¹ := by
    rw [← mul_inv]; ring_nf
  rw [hsq] at huv
  have hpos : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  have hstep : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 * (u * v) := by
    have := mul_le_mul_of_nonneg_left huv hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at this
  nlinarith [abs_nonneg (u - v), hstep]

/-! ## Depth `m`: the full digit-agreement theorem

Iterating.  The shift identity is DEFINITIONAL here — `cfDigit x i = cfDigit (gaussMap^[i] x) 0`
holds by `rfl`, because `cfDigit x n = ⌊(gaussMap^[n] x)⁻¹⌋₊` — so the induction carries only the
metric invariant `|gaussMap^[i] u − gaussMap^[i] v| < δ · scale u i`, where `scale` accumulates
the one-step costs of `abs_gaussMap_sub_le`.
-/

/-- The accumulated expansion cost of the first `i` Gauss steps along `u`. -/
noncomputable def scale (u : ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, ((cfDigit u j : ℝ) + 1) ^ 2

@[simp] theorem scale_zero (u : ℝ) : scale u 0 = 1 := by simp [scale]

theorem scale_succ (u : ℝ) (i : ℕ) :
    scale u (i + 1) = scale u i * ((cfDigit u i : ℝ) + 1) ^ 2 := by
  simp [scale, Finset.prod_range_succ]

theorem scale_pos (u : ℝ) (i : ℕ) : 0 < scale u i :=
  Finset.prod_pos fun j _ => by positivity

/-- The shift identity, definitionally. -/
theorem cfDigit_eq_iterate (x : ℝ) (i : ℕ) : cfDigit x i = cfDigit (gaussMap^[i] x) 0 := rfl

/-- **Digit agreement to depth `m`.**  If at every level `i < m` the point `gaussMap^[i] u` is in
`(0,1)` and avoids the boundary set at the ACCUMULATED scale `δ · scale u i`, then `v` matches
`u` in all of its first `m` digits.  The exceptional set is a finite union of depth-one bad sets
pulled back along `gaussMap`. -/
theorem cfDigit_agree_depth {u v δ : ℝ} (huv : |u - v| < δ) (hv0 : 0 < v) (m : ℕ)
    (hgood : ∀ i < m, gaussMap^[i] u ∈ Ioo (0:ℝ) 1 ∧
      gaussMap^[i] u ∉ boundaryBad (δ * scale u i)) :
    ∀ i < m, cfDigit v i = cfDigit u i := by
  -- the metric invariant, carried up the orbit
  have aux : ∀ i, i ≤ m →
      |gaussMap^[i] u - gaussMap^[i] v| < δ * scale u i ∧ 0 < gaussMap^[i] v := by
    intro i
    induction i with
    | zero => intro _; exact ⟨by simpa using huv, by simpa using hv0⟩
    | succ i ih =>
        intro hle
        have hi : i < m := by omega
        obtain ⟨hdist, hvpos⟩ := ih (by omega)
        obtain ⟨hui, hbad⟩ := hgood i hi
        obtain ⟨hn1, hlo, hhi⟩ := cylinder_of_not_boundaryBad hui hbad hdist
        obtain ⟨-, hulo, huhi⟩ := floor_inv_spec hui.1 hui.2
        set n : ℕ := cfDigit (gaussMap^[i] u) 0 with hn
        have hnr : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hstep := abs_gaussMap_sub_le hn1 hui.1 hvpos hulo huhi hlo hhi.le
        have hfac : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
        constructor
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', scale_succ]
          have : ((n : ℝ) + 1) ^ 2 * |gaussMap^[i] u - gaussMap^[i] v|
              < ((n : ℝ) + 1) ^ 2 * (δ * scale u i) :=
            by exact mul_lt_mul_of_pos_left hdist hfac
          have hcd : cfDigit u i = n := rfl
          rw [hcd]
          linarith [hstep, this]
        · rw [Function.iterate_succ_apply']
          rw [gaussMap_eq_sub hn1 hvpos hlo hhi.le]
          have : (n : ℝ) < (gaussMap^[i] v)⁻¹ := by
            rw [lt_inv_comm₀ (by linarith) hvpos]; exact hhi
          linarith
  intro i hi
  obtain ⟨hdist, hvpos⟩ := aux i (le_of_lt hi)
  obtain ⟨hui, hbad⟩ := hgood i hi
  rw [cfDigit_eq_iterate v i, cfDigit_eq_iterate u i]
  exact cfDigit_zero_eq_of_not_boundaryBad hui hbad hvpos hdist

/-! ## The exceptional set has small Gauss measure

`cfDigit_agree_depth` asks `gaussMap^[i] u` to avoid `boundaryBad` at each level `i < m`.  The
set of `u` that fail is `⋃_{i<m} (gaussMap^[i])⁻¹ (boundaryBad ε)`, and two facts bound it:

* **`gaussMeasure` is `gaussMap`-invariant**, so each pullback has the SAME mass as
  `boundaryBad ε` — there is no Jacobian to track (`gaussMeasure_preimage_iterate`, already in
  `CFPin`);
* the density is at most `1/log 2`, so `volume_boundaryBad_le` transfers.

The result is `gaussMeasure_exceptional_le`: mass at most `m · 6√ε / log 2`.  Linear in `m` and
`√ε` — and merging supplies `ε` exponentially small in the word length, so this is summable.

The scale `ε = δ · scale u i` still depends on `u`, which is why the statement here is for a
FIXED `ε`: the remaining step is a cutoff `scale u m ≤ S` on a set of large measure, which is
where the Khinchin integral `∫ log(1+a) dγ < ∞` enters.  That is the next node, and it is
deliberately separated from this one, which carries no arithmetic at all.
-/

/-- `boundaryBad δ`, reindexed as an explicit countable union of intervals. -/
theorem boundaryBad_eq_iUnion (δ : ℝ) :
    boundaryBad δ = Ioo (0:ℝ) 1 ∩
      ⋃ k : ℕ, Ioo ((((k : ℝ) + 1))⁻¹ - δ) ((((k : ℝ) + 1))⁻¹ + δ) := by
  ext x
  simp only [boundaryBad, mem_setOf_eq, mem_inter_iff, mem_iUnion, mem_Ioo]
  constructor
  · rintro ⟨hx, k, hk, hclose⟩
    refine ⟨hx, k - 1, ?_⟩
    have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      have : (k - 1 : ℕ) + 1 = k := by omega
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    rw [hcast]
    obtain ⟨h1, h2⟩ := abs_lt.1 hclose
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hx, k, h1, h2⟩
    refine ⟨hx, k + 1, by omega, ?_⟩
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast, abs_lt]
    exact ⟨by linarith, by linarith⟩

theorem measurableSet_boundaryBad (δ : ℝ) : MeasurableSet (boundaryBad δ) := by
  rw [boundaryBad_eq_iUnion]
  exact measurableSet_Ioo.inter (MeasurableSet.iUnion fun _ => measurableSet_Ioo)

/-- The Gauss mass of the boundary set, from the Lebesgue bound and the density window. -/
theorem gaussMeasure_boundaryBad_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    gaussMeasure (boundaryBad δ)
      ≤ ENNReal.ofReal (Real.log 2)⁻¹ * ENNReal.ofReal (6 * Real.sqrt δ) :=
  le_trans (gaussMeasure_le_volume _ (measurableSet_boundaryBad δ))
    (by gcongr; exact volume_boundaryBad_le hδ hδ1)

/-- **The exceptional set of `cfDigit_agree_depth`, at a fixed scale, has small Gauss mass.**
Invariance means each level contributes the same, so the bound is linear in the depth. -/
theorem gaussMeasure_exceptional_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ) :
    gaussMeasure (⋃ i ∈ Finset.range m, (gaussMap^[i]) ⁻¹' boundaryBad ε)
      ≤ m * (ENNReal.ofReal (Real.log 2)⁻¹ * ENNReal.ofReal (6 * Real.sqrt ε)) := by
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_)
    (le_of_eq (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]))
  rw [gaussMeasure_preimage_iterate (measurableSet_boundaryBad ε) i]
  exact gaussMeasure_boundaryBad_le hε hε1


section Audit

#print axioms boundaryBad_subset
#print axioms volume_boundaryBad_le
#print axioms cfDigit_zero_eq_of_not_boundaryBad
#print axioms gaussMap_eq_sub
#print axioms abs_gaussMap_sub_le
#print axioms cfDigit_agree_depth
#print axioms gaussMeasure_exceptional_le

end Audit

end NormalNumbers.VandeheyS7
