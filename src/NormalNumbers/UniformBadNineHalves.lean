/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadBelowFive

/-!
# Below exponent `5`: the next gate for `c⋆`

Proved so far: `5/2 ≤ c⋆ ≤ 124/25` (`five_halves_le_cStar`, `cStar_le_124_25`).  `cStar_le_four` is a
recorded wall (it needs an exact joint `{2, 3, 5}` core; Maze rows "counted medium bases over an
exact {2,3} core at c = 4" and "adaptive split cores for the Newhouse thick core").

The `cStar_le_five` engine has slack only `0.013` at its base-`3` kill levels, so lowering the
exponent needs a new ingredient, not retuned constants.  The candidates, in the order the lap-8 and
lap-10 probes suggest:
* base `3` handled exactly alongside base `2` (the joint recursion `joint23_rec.js` dies at level 91
  at `c = 4` but lives at `c = 4.25`), with the bases `b ≥ 5` still counted;
* finer kill-level bookkeeping (non-integer exponents change the windows' cell spans).

Frozen 2026-10-07 by the operator (Ren) after `cStar_le_five` landed.
-/

namespace NormalNumbers.UniformBadThreshold

/-- **Headline (frozen 2026-10-07): `c⋆ ≤ 9/2`.**  Believed true (95%: the finite systems put `c⋆`
near `5/2`, `CStarLeThirteenFifths`); no proof mechanism known (c⋆ lap 13: every local engine
tried stalls near `c ≈ 4.55`, `not_perStageCert`, Maze row "local per-window engines at c = 9/2").

English proof sketch.  Run the two-rate counting engine of `cStar_le_five` at exponent `9/2` with
base `3` made exact as well as base `2`: the joint `{2, 3}` survivor tree grows at a rate that the
lap-8 probe keeps alive down to `c ≈ 4.25`, and the bases `b ≥ 5` (perfect powers free) are charged
to alive ancestors at their kill levels, whose total weight `Σ_{b ≥ 5} b^{−9/2}`-type series is small.
The risk is the exact joint `{2, 3}` core: a counting lower bound for its growth that is uniform over
all levels (the `jointCoreSubEigen` question of `UniformBadJoint`, at `9/2` instead of `4`). -/
theorem cStar_le_nine_halves : cStar ≤ 9 / 2 := by
  sorry

/-! ## The wall of the two-rate engine at `9/2` (c⋆ lap 11)

The engine of `cStar_le_five` / `cStar_le_124_25` certifies nothing at `9/2`, even with every base
`b ≥ 5` dropped and the most optimistic level products.  At `c = 9/2`:

* base `2` must forbid the binary patterns of lengths `5, 7, 8`
  (`2^{−9/2} = 0.0000101101…₂`), each charged at least `cnt (k + 1 − ℓ)`;
* base `3` has `K_3 ≤ 3^{9/2} < 141`, so its lag is at most `⌊log₂(3·139/4)⌋ = 6` and a base-`3`
  kill level costs `4 cnt (k − 5)`;
* the base-`3` kill levels `⌈log₂(3^{n+1}·140)⌉ − 2` put between `⌊(l+1)/2⌋` and `⌊(l+1)/2⌋ + 1`
  of them in any `l ∈ [4, 7]` consecutive levels (probe `scripts/cstar_models/obst45.py`, `n < 3000`), so a
  two-rate product over `l` levels is at most `nhF gA gB l`.

`NineHalvesBalance` is then necessary for any two-rate certificate of this shape, and it fails
(`not_nineHalvesBalance`; best numerical slack `−0.048`).  Bases `b ≥ 5` only make it worse.
-/

theorem poly_U (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 1) :
    2 * y - 1 < y ^ 5 + y ^ 7 + y ^ 8 + 4 * y ^ 6 := by
  have hm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → u ^ 5 + u ^ 7 + u ^ 8 + 4 * u ^ 6 ≤ v ^ 5 + v ^ 7 + v ^ 8 + 4 * v ^ 6 := by
    intro u v hu huv; gcongr
  have hp : 0 < y ^ 5 + y ^ 7 + y ^ 8 + 4 * y ^ 6 := by positivity
  rcases le_or_gt y (1 / 2) with h | g0
  · linarith
  rcases le_or_gt y (221 / 400) with l1 | g1
  · have := hm (1 / 2) y (by norm_num) g0.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (237 / 400) with l2 | g2
  · have := hm (221 / 400) y (by norm_num) g1.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (257 / 400) with l3 | g3
  · have := hm (237 / 400) y (by norm_num) g2.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (293 / 400) with l4 | g4
  · have := hm (257 / 400) y (by norm_num) g3.le; norm_num at this ⊢; linarith
  · have := hm (293 / 400) y (by norm_num) g4.le; norm_num at this ⊢; linarith

theorem poly_L1 (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 10 / 19) :
    2 * y - 1 < y ^ 5 + y ^ 7 + y ^ 8 := by
  have hm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → u ^ 5 + u ^ 7 + u ^ 8 ≤ v ^ 5 + v ^ 7 + v ^ 8 := by
    intro u v hu huv; gcongr
  have hp : 0 < y ^ 5 + y ^ 7 + y ^ 8 := by positivity
  rcases le_or_gt y (1 / 2) with h | g0
  · linarith
  rcases le_or_gt y (13 / 25) with l1 | g1
  · have := hm (1 / 2) y (by norm_num) g0.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (21 / 40) with l2 | g2
  · have := hm (13 / 25) y (by norm_num) g1.le; norm_num at this ⊢; linarith
  · have := hm (21 / 40) y (by norm_num) g2.le; norm_num at this ⊢; linarith

theorem poly_L2 (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 1) :
    2 * y - 1 < 100 / 361 * y ^ 3 + 1000 / 6859 * y ^ 4 + 1000 / 6859 * y ^ 5 + 400 / 361 * y ^ 4 := by
  have hm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → 100 / 361 * u ^ 3 + 1000 / 6859 * u ^ 4 + 1000 / 6859 * u ^ 5 + 400 / 361 * u ^ 4 ≤ 100 / 361 * v ^ 3 + 1000 / 6859 * v ^ 4 + 1000 / 6859 * v ^ 5 + 400 / 361 * v ^ 4 := by
    intro u v hu huv; gcongr
  have hp : 0 < 100 / 361 * y ^ 3 + 1000 / 6859 * y ^ 4 + 1000 / 6859 * y ^ 5 + 400 / 361 * y ^ 4 := by positivity
  rcases le_or_gt y (1 / 2) with h | g0
  · linarith
  rcases le_or_gt y (223 / 400) with l1 | g1
  · have := hm (1 / 2) y (by norm_num) g0.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (47 / 80) with l2 | g2
  · have := hm (223 / 400) y (by norm_num) g1.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (243 / 400) with l3 | g3
  · have := hm (47 / 80) y (by norm_num) g2.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (31 / 50) with l4 | g4
  · have := hm (243 / 400) y (by norm_num) g3.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (63 / 100) with l5 | g5
  · have := hm (31 / 50) y (by norm_num) g4.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (16 / 25) with l6 | g6
  · have := hm (63 / 100) y (by norm_num) g5.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (259 / 400) with l7 | g7
  · have := hm (16 / 25) y (by norm_num) g6.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (131 / 200) with l8 | g8
  · have := hm (259 / 400) y (by norm_num) g7.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (53 / 80) with l9 | g9
  · have := hm (131 / 200) y (by norm_num) g8.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (67 / 100) with l10 | g10
  · have := hm (53 / 80) y (by norm_num) g9.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (271 / 400) with l11 | g11
  · have := hm (67 / 100) y (by norm_num) g10.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (137 / 200) with l12 | g12
  · have := hm (271 / 400) y (by norm_num) g11.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (277 / 400) with l13 | g13
  · have := hm (137 / 200) y (by norm_num) g12.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (7 / 10) with l14 | g14
  · have := hm (277 / 400) y (by norm_num) g13.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (71 / 100) with l15 | g15
  · have := hm (7 / 10) y (by norm_num) g14.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (18 / 25) with l16 | g16
  · have := hm (71 / 100) y (by norm_num) g15.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (293 / 400) with l17 | g17
  · have := hm (18 / 25) y (by norm_num) g16.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (3 / 4) with l18 | g18
  · have := hm (293 / 400) y (by norm_num) g17.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (309 / 400) with l19 | g19
  · have := hm (3 / 4) y (by norm_num) g18.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (161 / 200) with l20 | g20
  · have := hm (309 / 400) y (by norm_num) g19.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (43 / 50) with l21 | g21
  · have := hm (161 / 200) y (by norm_num) g20.le; norm_num at this ⊢; linarith
  rcases le_or_gt y (193 / 200) with l22 | g22
  · have := hm (43 / 50) y (by norm_num) g21.le; norm_num at this ⊢; linarith
  · have := hm (193 / 200) y (by norm_num) g22.le; norm_num at this ⊢; linarith


/-- The most optimistic two-rate product over `l ∈ [4, 7]` consecutive levels at `c = 9/2`:
`gB` on as few levels as the base-`3` kill pattern allows (`⌊(l+1)/2⌋`) when `gB ≤ gA`, on as many
(`⌊(l+1)/2⌋ + 1`) otherwise. -/
noncomputable def nhF (gA gB : ℝ) (l : ℕ) : ℝ :=
  if gB ≤ gA then gA ^ (l - (l + 1) / 2) * gB ^ ((l + 1) / 2)
  else gA ^ (l - ((l + 1) / 2 + 1)) * gB ^ ((l + 1) / 2 + 1)

/-- The per-level balance a two-rate counting certificate needs at `c = 9/2`, with only the
base-`2` patterns (lengths `5, 7, 8`) and base `3` (lag `6`, four cells) charged. -/
def NineHalvesBalance (gA gB : ℝ) : Prop :=
  1 / nhF gA gB 4 + 1 / nhF gA gB 6 + 1 / nhF gA gB 7 ≤ 2 - gA ∧
    1 / nhF gA gB 4 + 1 / nhF gA gB 6 + 1 / nhF gA gB 7 + 4 / nhF gA gB 5 ≤ 2 - gB

/-- **The two-rate counting engine has no certificate at `9/2`.**  Off a base-`3` level the
balance forces `gA < 19/10` (base `2` alone grows at most `≈ 1.8865`), and then the base-`3`
levels cannot balance for any `gB`. -/
@[blueprint (title := "The two-rate counting engine of c⋆ ≤ 5 has no certificate at c = 9/2")]
theorem not_nineHalvesBalance {gA gB : ℝ} (hA : 1 ≤ gA) (hB : 1 ≤ gB) :
    ¬ NineHalvesBalance gA gB := by
  rintro ⟨hoff, hon⟩
  have hA0 : 0 < gA := by linarith
  have hB0 : 0 < gB := by linarith
  have hx0 : 0 < gA⁻¹ := inv_pos.2 hA0
  have hy0 : 0 < gB⁻¹ := inv_pos.2 hB0
  have hx1 : gA⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have hy1 : gB⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB
  have ex : gA⁻¹ * gA = 1 := inv_mul_cancel₀ hA0.ne'
  have ey : gB⁻¹ * gB = 1 := inv_mul_cancel₀ hB0.ne'
  have e1 : ∀ a b : ℕ, 1 / (gA ^ a * gB ^ b) = gA⁻¹ ^ a * gB⁻¹ ^ b := by
    intro a b; rw [one_div, mul_inv, inv_pow, inv_pow]
  have e4 : ∀ a b : ℕ, 4 / (gA ^ a * gB ^ b) = 4 * (gA⁻¹ ^ a * gB⁻¹ ^ b) := by
    intro a b; rw [div_eq_mul_inv, mul_inv, inv_pow, inv_pow]
  set x := gA⁻¹ with hx
  set y := gB⁻¹ with hy
  by_cases h : gB ≤ gA
  · have f : ∀ l, nhF gA gB l = gA ^ (l - (l + 1) / 2) * gB ^ ((l + 1) / 2) := fun l => by
      simp [nhF, h]
    rw [f, f, f] at hoff
    rw [f, f, f, f] at hon
    norm_num only at hoff hon
    rw [e1, e1, e1] at hoff
    rw [e1, e1, e1, e4] at hon
    have hxy : x ≤ y := inv_anti₀ hB0 h
    -- off-level: `x⁴ + x⁶ + x⁷ ≤ 2 − 1/x`, so `x > 10/19`
    have hx10 : 10 / 19 < x := by
      by_contra hc
      have hc' : x ≤ 10 / 19 := not_lt.1 hc
      have p := poly_L1 x hx0 hc'
      have m1 : x ^ 2 * x ^ 2 ≤ x ^ 2 * y ^ 2 := by gcongr
      have m2 : x ^ 3 * x ^ 3 ≤ x ^ 3 * y ^ 3 := by gcongr
      have m3 : x ^ 3 * x ^ 4 ≤ x ^ 3 * y ^ 4 := by gcongr
      have hk : x * (x ^ 2 * x ^ 2 + x ^ 3 * x ^ 3 + x ^ 3 * x ^ 4) ≤ x * (2 - gA) :=
        mul_le_mul_of_nonneg_left (by linarith) hx0.le
      have : x * (2 - gA) = 2 * x - 1 := by rw [mul_sub, ex]; ring
      rw [this] at hk
      nlinarith
    -- base-`3` level
    have a2 : (100 / 361 : ℝ) ≤ x ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) hx10.le 2; norm_num at this; linarith
    have a3 : (1000 / 6859 : ℝ) ≤ x ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hx10.le 3; norm_num at this; linarith
    have p := poly_L2 y hy0 hy1
    have m1 : 100 / 361 * y ^ 2 ≤ x ^ 2 * y ^ 2 := by gcongr
    have m2 : 1000 / 6859 * y ^ 3 ≤ x ^ 3 * y ^ 3 := by gcongr
    have m3 : 1000 / 6859 * y ^ 4 ≤ x ^ 3 * y ^ 4 := by gcongr
    have m4 : 100 / 361 * y ^ 3 ≤ x ^ 2 * y ^ 3 := by gcongr
    have hk : y * (100 / 361 * y ^ 2 + 1000 / 6859 * y ^ 3 + 1000 / 6859 * y ^ 4 +
        4 * (100 / 361 * y ^ 3)) ≤ y * (2 - gB) := mul_le_mul_of_nonneg_left (by linarith) hy0.le
    have : y * (2 - gB) = 2 * y - 1 := by rw [mul_sub, ey]; ring
    rw [this] at hk
    nlinarith
  · have f : ∀ l, nhF gA gB l = gA ^ (l - ((l + 1) / 2 + 1)) * gB ^ ((l + 1) / 2 + 1) :=
      fun l => by simp [nhF, h]
    rw [f, f, f, f] at hon
    norm_num only at hon
    rw [e1, e1, e1, e4] at hon
    have hyx : y ≤ x := inv_anti₀ hA0 (le_of_lt (not_le.1 h))
    have p := poly_U y hy0 hy1
    have m1 : y * y ^ 3 ≤ x ^ 1 * y ^ 3 := by rw [pow_one]; gcongr
    have m2 : y ^ 2 * y ^ 4 ≤ x ^ 2 * y ^ 4 := by gcongr
    have m3 : y ^ 2 * y ^ 5 ≤ x ^ 2 * y ^ 5 := by gcongr
    have m4 : y * y ^ 4 ≤ x ^ 1 * y ^ 4 := by rw [pow_one]; gcongr
    have hk : y * (y * y ^ 3 + y ^ 2 * y ^ 4 + y ^ 2 * y ^ 5 + 4 * (y * y ^ 4)) ≤ y * (2 - gB) :=
      mul_le_mul_of_nonneg_left (by linarith) hy0.le
    have : y * (2 - gB) = 2 * y - 1 := by rw [mul_sub, ey]; ring
    rw [this] at hk
    nlinarith


/-! ## The per-stage engine at `9/2` (c⋆ lap 13)

The two-rate engine fixes one lag and four cells for every base-`3` window.  The **per-stage**
engine chooses, for each base-`3` stage `n`, the ancestor level `anc3 n` (the largest dyadic cell
narrower than the gap `3^{−n}(1 − 2/140)` between windows of radius `1/(140·3ⁿ)`, so it meets at
most one window) and the kill depth `depth3 n ∈ [1, 20]` minimizing `cells3 n m · (4/7)^m`, where
`cells3 n m = ⌊2^{anc3 n + m + 1}/(140·3ⁿ)⌋ + 2` bounds the cells of level `anc3 n + m` that the
window touches.  Its Rosenfeld balance at level `k` (`bal`) charges each base-`2` pattern length
`ℓ ∈ {5, 7, 8, 10, 12, 13}` once against level `k + 1 − ℓ` and each base-`3` window against its
ancestor; a growth certificate is a rate sequence `g` with `g k ≤ bal g k`.

**Even with only bases `2` and `3`, and the first `40` levels growing at the full rate `2`, no
certificate reaches level `182`** (`not_perStageCert`): the greedy recursion `Q` (rates rounded
up, so it dominates every certificate) falls to `Q 181 ≈ 0.705`.  Numerically the same engine with
all bases `b < 300` survives at `c = 4.6` (min rate `1.59`) and dies at `4.55`; the Lebesgue- and
Parry-measure precharge variants stall at the same place (`scripts/cstar_models/eng2.py`,
`leb2.py`, `hyb.py`, `nupre.py`).  Base `3` needs its charge cut by about `30%`
(`eng5.py`), i.e. information about where its windows fall relative to the alive cells, which is
the exact joint `{2, 3}` core (`SmallBaseTreeCore`).
-/

namespace PerStage

/-- Base-`2` pattern lengths at `c = 9/2` (`2^{−9/2} = 0.0000101101010…₂`, cut at `13`). -/
def pat92 : List ℕ := [5, 7, 8, 10, 12, 13]

/-- The ancestor level of base-`3` stage `n`: least `a` with `138 · 2^a > 140 · 3ⁿ`. -/
def anc3 (n : ℕ) : ℕ := Nat.log 2 (140 * 3 ^ n / 138) + 1

/-- Cells of level `anc3 n + m` touched by the closed window of width `2/(140·3ⁿ)`. -/
def cells3 (n m : ℕ) : ℕ := 2 ^ (anc3 n + m + 1) / (140 * 3 ^ n) + 2

/-- The kill depth: the `m ∈ [1, 20]` minimizing `cells3 n m · (4/7)^m` (first minimizer). -/
def depth3 (n : ℕ) : ℕ :=
  ((List.range 20).map (· + 1)).foldl
    (fun best m => if ((cells3 n m * 4 ^ m : ℕ) : ℚ) / 7 ^ m <
        ((cells3 n best * 4 ^ best : ℕ) : ℚ) / 7 ^ best then m else best) 1

/-- The kill level of base-`3` stage `n`. -/
def kill3 (n : ℕ) : ℕ := anc3 n + depth3 n

/-- The per-stage balance at level `k`: the largest rate `g k` the engine can certify there. -/
def bal {F : Type*} [Field F] (g : ℕ → F) (k : ℕ) : F :=
  2 - (∑ l ∈ pat92.toFinset.filter (· ≤ k + 1), 1 / ∏ j ∈ Finset.Ico (k + 1 - l) k, g j)
    - ∑ n ∈ (Finset.range 120).filter (fun n => kill3 n = k + 1),
        (cells3 n (depth3 n) : F) / ∏ j ∈ Finset.Ico (anc3 n) k, g j

/-- A growth certificate of the per-stage engine on the levels `[40, 182)`. -/
def Cert (g : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ g k ∧ g k ≤ 2) ∧ ∀ k, 40 ≤ k → k < 182 → g k ≤ bal g k

/-- Round up to a multiple of `2^{−40}`. -/
def roundUp (x : ℚ) : ℚ := ((x.num * 2 ^ 40 + x.den - 1) / x.den : ℤ) / 2 ^ 40

/-- The greedy recursion, rates rounded up: `2` below level `40`, then `bal` rounded up. -/
def Qarr : Array ℚ :=
  (List.range 182).foldl
    (fun acc k => acc.push (if k < 40 then 2 else roundUp (bal (fun j => acc.getD j 2) k))) #[]

def Q (k : ℕ) : ℚ := Qarr.getD k 2

theorem Q_low : ∀ k ∈ List.range 40, Q k = 2 := by native_decide

theorem bal_Q_le : ∀ k ∈ List.range' 40 142, bal Q k ≤ Q k := by native_decide

theorem Q_dies : Q 181 < 1 := by native_decide

theorem cast_bal (q : ℕ → ℚ) (k : ℕ) : ((bal q k : ℚ) : ℝ) = bal (fun j => (q j : ℝ)) k := by
  simp [bal]

theorem bal_mono {g h : ℕ → ℝ} {k : ℕ} (hpos : ∀ j < k, 0 < g j) (hle : ∀ j < k, g j ≤ h j) :
    bal g k ≤ bal h k := by
  unfold bal
  have hP : ∀ i, (0 : ℝ) < ∏ j ∈ Finset.Ico i k, g j := fun i =>
    Finset.prod_pos fun j hj => hpos j (Finset.mem_Ico.1 hj).2
  have hPle : ∀ i, ∏ j ∈ Finset.Ico i k, g j ≤ ∏ j ∈ Finset.Ico i k, h j := fun i =>
    Finset.prod_le_prod (fun j hj => (hpos j (Finset.mem_Ico.1 hj).2).le)
      fun j hj => hle j (Finset.mem_Ico.1 hj).2
  have h1 : ∑ l ∈ pat92.toFinset.filter (· ≤ k + 1), 1 / ∏ j ∈ Finset.Ico (k + 1 - l) k, h j ≤
      ∑ l ∈ pat92.toFinset.filter (· ≤ k + 1), 1 / ∏ j ∈ Finset.Ico (k + 1 - l) k, g j :=
    Finset.sum_le_sum fun l _ => one_div_le_one_div_of_le (hP _) (hPle _)
  have h2 : ∑ n ∈ (Finset.range 120).filter (fun n => kill3 n = k + 1),
        (cells3 n (depth3 n) : ℝ) / ∏ j ∈ Finset.Ico (anc3 n) k, h j ≤
      ∑ n ∈ (Finset.range 120).filter (fun n => kill3 n = k + 1),
        (cells3 n (depth3 n) : ℝ) / ∏ j ∈ Finset.Ico (anc3 n) k, g j :=
    Finset.sum_le_sum fun n _ => div_le_div_of_nonneg_left (by positivity) (hP _) (hPle _)
  linarith

end PerStage

open PerStage in
/-- **The per-stage counting engine has no certificate at `9/2`**, even charging only bases `2`
and `3` and letting the first `40` levels grow at rate `2`: every certificate `g` stays below the
greedy recursion `Q` (`bal_mono`), which drops below `1` at level `181`. -/
@[blueprint (title := "The per-stage counting engine has no certificate at c = 9/2, even with only bases 2 and 3")]
theorem not_perStageCert : ¬ ∃ g, Cert g := by
  rintro ⟨g, hb, hbal⟩
  have key : ∀ k, k < 182 → g k ≤ Q k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases h40 : k < 40
      · rw [Q_low k (List.mem_range.2 h40)]
        push_cast
        exact (hb k).2
      · have hmono : bal g k ≤ bal (fun j => (Q j : ℝ)) k :=
          bal_mono (fun j _ => by linarith [(hb j).1]) fun j hj => ih j hj (by omega)
        have hc := bal_Q_le k (List.mem_range'_1.2 ⟨by omega, by omega⟩)
        have hc' : bal (fun j => (Q j : ℝ)) k ≤ (Q k : ℝ) := by
          rw [← cast_bal]; exact_mod_cast hc
        linarith [hbal k (by omega) hk]
  have h1 := key 181 (by norm_num)
  have h2 : (Q 181 : ℝ) < 1 := by exact_mod_cast Q_dies
  linarith [(hb 181).1]

end NormalNumbers.UniformBadThreshold
