/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadCount

/-!
# The exact small-base core: containment kills and a weighted sub-eigenvector

**Containment kills.**  For a finite set `S` of bases and an integer exponent `c`, a dyadic cell is
`winBad` when it lies inside a closed window `[A/bⁿ − b^{−n−c}, A/bⁿ + b^{−n−c}]` of some `b ∈ S`.
This is the least pruning that still works: a point inside an *open* window has all its small
cells inside the window, so a point lying in an alive cell of every level avoids every open window
(`dnear_ge_of_alive_all`), i.e. `‖bⁿξ‖ ≥ b^{−c}`.

**Weighted growth.**  The core is certified by a nonnegative weight on cells whose alive children
carry at least `Λ` times the parent's weight (`SubEigen`).  The weight then grows like `Λᵏ`, so
every level has an alive cell (`cnt_pos_of_subEigen`) and the core has a good point
(`exists_good_of_subEigen`).

**The `{2, 3}` core at `c = 4`** (`jointCoreSubEigen_four`, believed).  Probe 2026-10-07
(`scripts/cstar_models/abs23.js`): a finite abstraction of the joint system (binary run state,
the ternary trailing-run states of the one or two ternary units the cell meets, the offset `u` of
the cell in ternary units, the cell length `ρ ∈ [1/3, 1)` in ternary units), with worst-case
transitions over boxes in `(u, ρ)`, has a sub-eigenvector with ratio `≥ 1.669` (81 `u`-bins,
16 `ρ`-bins, 150 iterations; `1.539` at 27 bins, `≈ 1.65–1.73` and still rising at 243 bins).
Pure binary is `1.8393`.  So base 3 can be made exact against base 2 at the price of `≈ 0.17` of
growth.  The obstruction moved to the medium bases (see `PENDING_WORK.md`, c⋆ lap 4): charged by
counting at `c = 4` the bases `b ≥ 5` cost `0.73 / 0.32 / 0.17` per level at growth
`1.5 / 1.6 / 1.7` even with uniform weights, and the certificate weights are far from uniform
(ten percent of boxes have weight `0`; a threshold `δ ≥ 0.2` collapses the abstraction).
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

namespace Count

/-- A level-`k` dyadic cell lies inside a closed window of radius `b^{−n−c}` around `A/bⁿ` for
some base `b ∈ S`. -/
def winBad (c : ℕ) (S : Finset ℕ) (k a : ℕ) : Prop :=
  ∃ b ∈ S, ∃ n A : ℕ, cell k a ⊆
    Set.Icc ((A : ℝ) / (b : ℝ) ^ n - 1 / (b : ℝ) ^ (n + c))
      ((A : ℝ) / (b : ℝ) ^ n + 1 / (b : ℝ) ^ (n + c))

/-- A point in an alive cell of every level avoids every open window: `‖bⁿξ‖ ≥ b^{−c}`. -/
theorem dnear_ge_of_alive_all {Bad : ℕ → ℕ → Prop} {c : ℕ} {S : Finset ℕ}
    (hBad : ∀ k a, winBad c S k a → Bad k a) {ξ : ℝ}
    (hξ : ∀ k, ∃ a, Alive Bad k a ∧ ξ ∈ cell k a) {b : ℕ} (hbS : b ∈ S) (hb : 2 ≤ b) (n : ℕ) :
    ((b : ℝ) ^ c)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hBc : (0 : ℝ) < (b : ℝ) ^ c := by positivity
  obtain ⟨a0, -, h0⟩ := hξ 0
  have hξ0 : 0 ≤ ξ := le_trans (by positivity) h0.1
  set x := (b : ℝ) ^ n * ξ with hx
  have hx0 : 0 ≤ x := by positivity
  have hr0 : 0 ≤ round x := by
    have : (0 : ℝ) ≤ round x := by
      have hB1 : ((b : ℝ) ^ c)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b)))
      have h1 : |x - round x| < 1 := lt_of_lt_of_le hlt hB1
      have := (abs_lt.1 h1).2
      have h2 : (-1 : ℝ) < round x := by linarith
      have h3 : (-1 : ℤ) < round x := by exact_mod_cast h2
      exact_mod_cast (show (0 : ℤ) ≤ round x by omega)
    exact_mod_cast this
  set A : ℕ := (round x).toNat with hA
  have hAx : ((A : ℤ) : ℝ) = ((round x : ℤ) : ℝ) := by rw [hA, Int.toNat_of_nonneg hr0]
  have hAx' : (A : ℝ) = ((round x : ℤ) : ℝ) := by exact_mod_cast hAx
  -- distance of ξ to the centre, in units of the radius
  set r : ℝ := 1 / (b : ℝ) ^ (n + c) with hr
  have hd : |ξ - (A : ℝ) / (b : ℝ) ^ n| < r := by
    have e1 : ξ - (A : ℝ) / (b : ℝ) ^ n = (x - round x) / (b : ℝ) ^ n := by
      rw [hAx']; field_simp; rw [hx]; ring
    have e2 : r = ((b : ℝ) ^ c)⁻¹ / (b : ℝ) ^ n := by
      rw [hr, pow_add]; field_simp
    rw [e1, e2, abs_div, abs_of_pos hBn]
    exact div_lt_div_of_pos_right hlt hBn
  set ε := r - |ξ - (A : ℝ) / (b : ℝ) ^ n| with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hεpos (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨a, ha, hξa⟩ := hξ (k + 1)
  have hsub : cell (k + 1) a ⊆
      Set.Icc ((A : ℝ) / (b : ℝ) ^ n - r) ((A : ℝ) / (b : ℝ) ^ n + r) := by
    intro y hy
    have hlen : |y - ξ| ≤ (1 / 2 : ℝ) ^ k := by
      obtain ⟨y1, y2⟩ := hy
      obtain ⟨z1, z2⟩ := hξa
      have e : ((a : ℝ) + 1) / 2 ^ (k + 1) - (a : ℝ) / 2 ^ (k + 1) = (1 / 2) ^ (k + 1) := by
        rw [one_div_pow]; field_simp; ring
      have : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2) ^ k := pow_le_pow_of_le_one (by norm_num)
        (by norm_num) (by omega)
      rw [abs_le]; constructor <;> linarith
    have := abs_sub_le y ξ ((A : ℝ) / (b : ℝ) ^ n)
    have h3 : |y - (A : ℝ) / (b : ℝ) ^ n| ≤ r := by linarith
    obtain ⟨h4, h5⟩ := abs_le.1 h3
    exact ⟨by linarith, by linarith⟩
  exact ha.2 (hBad _ _ ⟨b, hbS, n, A, hsub⟩)

open Classical in
/-- A weighted certificate for the core: nonnegative weights, a positive root, and alive children
carrying at least `Λ` times the weight of their alive parent. -/
def SubEigen (Bad : ℕ → ℕ → Prop) (Λ : ℝ) : Prop :=
  ∃ w : ℕ → ℕ → ℝ, (∀ k a, 0 ≤ w k a) ∧ 0 < w 0 0 ∧
    ∀ k a, Alive Bad k a →
      Λ * w k a ≤ (if Alive Bad (k + 1) (2 * a) then w (k + 1) (2 * a) else 0) +
        (if Alive Bad (k + 1) (2 * a + 1) then w (k + 1) (2 * a + 1) else 0)

open Classical in
/-- Regrouping the alive cells of level `k + 1` by their parents. -/
theorem sum_aliveSet_succ (Bad : ℕ → ℕ → Prop) (f : ℕ → ℝ) (k : ℕ) :
    ∑ a' ∈ aliveSet Bad (k + 1), f a' =
      ∑ a ∈ aliveSet Bad k, ((if Alive Bad (k + 1) (2 * a) then f (2 * a) else 0) +
        (if Alive Bad (k + 1) (2 * a + 1) then f (2 * a + 1) else 0)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun a' => a' / 2) (t := aliveSet Bad k)
    (fun a' ha' => (mem_aliveSet Bad).2 (show Alive Bad (k + 1) a' from (mem_aliveSet Bad).1 ha').1)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hlt := alive_lt Bad ((mem_aliveSet Bad).1 ha)
  have e : (aliveSet Bad (k + 1)).filter (fun a' => a' / 2 = a) =
      ((({2 * a} : Finset ℕ).filter (Alive Bad (k + 1))) ∪
        (({2 * a + 1} : Finset ℕ).filter (Alive Bad (k + 1)))) := by
    ext a'
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, mem_aliveSet]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (by omega : a' = 2 * a ∨ a' = 2 * a + 1) with rfl | rfl
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr ⟨rfl, h1⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact ⟨h, by omega⟩
  rw [e, Finset.sum_union]
  · simp only [Finset.sum_filter, Finset.sum_singleton]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_singleton] at hx hx'
    omega

theorem cnt_pos_of_subEigen {Bad : ℕ → ℕ → Prop} {Λ : ℝ} (hΛ : 0 < Λ) (h : SubEigen Bad Λ) :
    ∀ k, 0 < cnt Bad k := by
  obtain ⟨w, hw0, hroot, hstep⟩ := h
  set W : ℕ → ℝ := fun k => ∑ a ∈ aliveSet Bad k, w k a with hW
  have hgrow : ∀ k, Λ * W k ≤ W (k + 1) := by
    intro k
    simp only [hW]
    rw [sum_aliveSet_succ Bad (w (k + 1)) k, Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hstep k a ((mem_aliveSet Bad).1 ha)
  have hpos : ∀ k, 0 < W k := by
    intro k
    induction k with
    | zero =>
      have : aliveSet Bad 0 = {0} := by
        ext a; rw [mem_aliveSet]; simp [Alive]
      simp only [hW, this, Finset.sum_singleton]; exact hroot
    | succ k ih => exact lt_of_lt_of_le (mul_pos hΛ ih) (hgrow k)
  intro k
  by_contra h0
  have : aliveSet Bad k = ∅ := Finset.card_eq_zero.1 (by unfold cnt at h0; omega)
  have := hpos k
  simp [hW, *] at this

/-- **Core lemma.**  A weighted certificate for a pruning that contains the containment kills of
`S` yields a point with `‖bⁿξ‖ ≥ b^{−c}` for every `b ∈ S` and every `n`. -/
theorem exists_good_of_subEigen {Bad : ℕ → ℕ → Prop} {c : ℕ} {S : Finset ℕ} {Λ : ℝ}
    (hBad : ∀ k a, winBad c S k a → Bad k a) (hΛ : 0 < Λ) (h : SubEigen Bad Λ) :
    ∃ ξ : ℝ, ∀ b ∈ S, 2 ≤ b → ∀ n : ℕ, ((b : ℝ) ^ c)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  obtain ⟨ξ, hξ⟩ := exists_mem_cells Bad (cnt_pos_of_subEigen hΛ h)
  exact ⟨ξ, fun b hb hb2 n => dnear_ge_of_alive_all hBad hξ hb hb2 n⟩

/-- **Crux node: the exact `{2, 3}` core at `c = 4`.**  Believed 80%.  The containment-kill tree of
bases `2, 3` at exponent `4` carries a weighted sub-eigenvector of ratio `33/20`.

Evidence: the worst-case box abstraction of `scripts/cstar_models/abs23.js` (`node abs23.js 81 8
8 150`) has minimal ratio `1.669 > 1.65`; it is pessimistic (every box quantity is replaced by its
worst case over the box), so the true system grows faster (exact joint simulation of the
meet-kill system, a stronger pruning: `1.808`).  For comparison the binary run-free automaton
alone has ratio `1.8393` (tribonacci).  What is missing is a certified
transcription: rational box bounds and a Lean check that every concrete cell maps into a box
whose transitions the abstraction over-approximates. -/
theorem jointCoreSubEigen_four : SubEigen (winBad 4 {2, 3}) (33 / 20) := by
  sorry

end Count

end NormalNumbers.UniformBadThreshold
