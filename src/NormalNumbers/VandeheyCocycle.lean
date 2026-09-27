/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyAutomaton

/-!
# The class cocycle — the actual crux of Vandehey 2017, Theorem 1.1

`VandeheyAutomaton.lean` reduces Theorem 1.1 to a joint (window, state) frequency for the
det-`±D` transducer, *provided* the transducer has a synchronizing word.  A decidable probe
(`probes/cf_transducer_sync.py`, `probes/cf_transducer_class.py`,
`PROBE-2026-09-27-transducer-not-synchronizing.md`) shows **it does not**, and identifies
the obstruction exactly:

> mergeability of two transducer states is *equality of the row lattice `ℤ²M` up to
> scaling* — an invariant that ingest (`M ↦ M·B_a`) and emit (`M ↦ B_d⁻¹·M`) cannot change,
> because both act by matrices of determinant `±1`.

So the state space is an extension
`state = (class ∈ ℙ¹(ℤ/D)) × (fiber, which *is* mergeable inside a class)`, and the class
component is the mod-`D` reduction `c_i = c₀ · B_{a₁} ⋯ B_{a_i}` of the CF matrix product.
Each `B_a` is invertible mod `D`, so the class never forgets its past and **no word
synchronizes it**.  The missing ingredient is therefore exactly:

> **(Crux)** along a CF-normal orbit the class cocycle equidistributes, jointly with digit
> windows.

This is precisely the content Vandehey buys from the Pyatetskii-Shapiro criterion in the
Moshchevitin–Shkredov form — the step Airey–Mance refuted.  This module builds the
replacement, which needs no hot-spot criterion: a Cesàro average of the shift identity
`P_{i+k} = P_i · Q_i^{(k)}` (where `Q_i^{(k)}` depends only on the window at `i`) turns a
cocycle average into a *window* average, which CF-normality evaluates outright.

## This section: the engine

`cesaro_shift_bound` is the elementary inequality that does the work, and it is where the
non-synchronizing cocycle is tamed:

> `‖∑_{i<n} a i‖ ≤ ∑_{i<n} ‖(1/K) ∑_{k<K} a (i+k)‖ + 2 C K`   for `‖a‖ ≤ C`.

Averaging a bounded sequence against its own shifts costs only the `O(K)` boundary, so a
sum one cannot control termwise is dominated by a sum of *local* `K`-averages.  Applied with
`a i = f(window at i) · χ(P_i)` and `‖χ(P_i)‖ = 1`, the left side is the object we want and
the right side is a window average — exactly the shape `tendsto_window_mem_freq` eats.
-/

namespace NormalNumbers

open Filter Finset

namespace VandeheyCocycle

/-! ## The Cesàro shift engine -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Shifting the window of summation by `k` costs at most `2 C k`. -/
lemma norm_sum_shift_sub_le {a : ℕ → E} {C : ℝ} (hC : ∀ i, ‖a i‖ ≤ C) (n k : ℕ) :
    ‖(∑ i ∈ range n, a (i + k)) - ∑ i ∈ range n, a i‖ ≤ 2 * C * k := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hshift : ∑ i ∈ range n, a (i + k) = ∑ i ∈ Finset.Ico k (n + k), a i := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have hsplit₁ : (∑ i ∈ Finset.Ico 0 k, a i) + ∑ i ∈ Finset.Ico k (n + k), a i
      = ∑ i ∈ Finset.Ico 0 (n + k), a i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega)
  have hsplit₂ : (∑ i ∈ Finset.Ico 0 n, a i) + ∑ i ∈ Finset.Ico n (n + k), a i
      = ∑ i ∈ Finset.Ico 0 (n + k), a i :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le n) (by omega)
  have hrange : ∀ m : ℕ, ∑ i ∈ Finset.Ico 0 m, a i = ∑ i ∈ range m, a i := by
    intro m; rw [Finset.range_eq_Ico]
  have hkey : (∑ i ∈ range n, a (i + k)) - ∑ i ∈ range n, a i
      = (∑ i ∈ Finset.Ico n (n + k), a i) - ∑ i ∈ Finset.Ico 0 k, a i := by
    rw [hshift]
    rw [hrange] at hsplit₂
    linear_combination (norm := abel) hsplit₁ - hsplit₂
  rw [hkey]
  have h1 : ‖∑ i ∈ Finset.Ico n (n + k), a i‖ ≤ C * k := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ C fun i _ => hC i) ?_
    simp [mul_comm]
  have h2 : ‖∑ i ∈ Finset.Ico 0 k, a i‖ ≤ C * k := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ C fun i _ => hC i) ?_
    simp [mul_comm]
  calc ‖(∑ i ∈ Finset.Ico n (n + k), a i) - ∑ i ∈ Finset.Ico 0 k, a i‖
      ≤ ‖∑ i ∈ Finset.Ico n (n + k), a i‖ + ‖∑ i ∈ Finset.Ico 0 k, a i‖ :=
        norm_sub_le _ _
    _ ≤ C * k + C * k := add_le_add h1 h2
    _ = 2 * C * k := by ring

/-- **The Cesàro shift engine.**  A bounded sequence's partial sum is dominated by the sum
of its own local `K`-averages, up to an `O(K)` boundary term.

This is the whole reason a *non-synchronizing* cocycle can still be handled: the local
`K`-average of `a i = f(window) · χ(P_i)` factors as `χ(P_i)` (a unit) times a quantity
depending only on the length-`(K + |window|)` window at `i`, so the right-hand side is a
plain window average — which CF-normality evaluates. -/
theorem cesaro_shift_bound {a : ℕ → E} {C : ℝ} (hC : ∀ i, ‖a i‖ ≤ C) (n : ℕ) {K : ℕ}
    (hK : 0 < K) :
    ‖∑ i ∈ range n, a i‖
      ≤ (∑ i ∈ range n, ‖(K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k)‖) + 2 * C * K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set S : E := ∑ i ∈ range n, a i with hS
  set T : ℕ → E := fun k => ∑ i ∈ range n, a (i + k) with hT
  set A : E := (K : ℝ)⁻¹ • ∑ k ∈ range K, T k with hA
  -- `A` is the sum of the local `K`-averages
  have havg : A = ∑ i ∈ range n, (K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k) := by
    rw [hA, hT, Finset.sum_comm, Finset.smul_sum]
  -- `A` is close to `S`
  have hdiff : ‖A - S‖ ≤ 2 * C * K := by
    have hsum : ∑ k ∈ range K, (T k - S) = (∑ k ∈ range K, T k) - (K : ℕ) • S := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hKS : (K : ℝ)⁻¹ • ((K : ℕ) • S) = S := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (ne_of_gt hKR), one_smul]
    have hrw : A - S = (K : ℝ)⁻¹ • ∑ k ∈ range K, (T k - S) := by
      rw [hsum, smul_sub, hKS, hA]
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hb : ‖∑ k ∈ range K, (T k - S)‖ ≤ (K : ℝ) * (2 * C * K) := by
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * C * K) fun k hk => ?_) ?_
      · refine le_trans (norm_sum_shift_sub_le hC n k) ?_
        have hkK : (k : ℝ) ≤ K := by exact_mod_cast le_of_lt (Finset.mem_range.mp hk)
        nlinarith
      · simp [Finset.card_range, nsmul_eq_mul]
    calc (K : ℝ)⁻¹ * ‖∑ k ∈ range K, (T k - S)‖
        ≤ (K : ℝ)⁻¹ * ((K : ℝ) * (2 * C * K)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * C * K := by field_simp
  have hSA : S = A - (A - S) := by abel
  calc ‖S‖ = ‖A - (A - S)‖ := by rw [← hSA]
    _ ≤ ‖A‖ + ‖A - S‖ := norm_sub_le _ _
    _ ≤ (∑ i ∈ range n, ‖(K : ℝ)⁻¹ • ∑ k ∈ range K, a (i + k)‖) + 2 * C * K := by
        refine add_le_add ?_ hdiff
        rw [havg]
        exact norm_sum_le _ _

/-! ## The cocycle along the CF expansion

The transducer's class component is `c_i = c₀ · g(a₁) ⋯ g(a_i)` for `g` sending a CF digit
to the image of `B_a = [[0,1],[1,a]]` in the finite group `PGL₂(ℤ/D)` — only `a mod D`
matters, as the probe's tables show.  Everything below is stated for an arbitrary monoid so
that the concrete `PGL₂(ℤ/D)` instance is a plug-in, and so the Wall-side automata of
`WallCrux.lean` can reuse it.
-/

variable {G : Type*} [Monoid G]

/-- The cocycle after `i` CF digits of `x`: `g(a₁) ⋯ g(a_i)`. -/
noncomputable def cocycleOf (g : ℕ → G) (x : ℝ) (i : ℕ) : G :=
  ((VandeheyAut.cfWord x i).map g).prod

/-- The cocycle increment over the digits at positions `i, …, i+k−1`.  This is a function of
the **window** alone — which is the entire point. -/
noncomputable def windowProd (g : ℕ → G) (x : ℝ) (i k : ℕ) : G :=
  ((VandeheyAut.cfWindow x i k).map g).prod

@[simp] lemma cocycleOf_zero (g : ℕ → G) (x : ℝ) : cocycleOf g x 0 = 1 := by
  simp [cocycleOf, VandeheyAut.cfWord]

@[simp] lemma windowProd_zero (g : ℕ → G) (x : ℝ) (i : ℕ) : windowProd g x i 0 = 1 := by
  simp [windowProd]

/-- `windowProd` depends only on the window, as a list of digits. -/
lemma windowProd_eq_of_window_eq {g : ℕ → G} {x y : ℝ} {i j k : ℕ}
    (h : VandeheyAut.cfWindow x i k = VandeheyAut.cfWindow y j k) :
    windowProd g x i k = windowProd g y j k := by
  simp [windowProd, h]

/-- **The shift identity.**  `P_{i+k} = P_i · Q_i^{(k)}`, with the increment a function of
the length-`k` window at `i`.  This is what makes `cesaro_shift_bound` bite: averaging the
cocycle against its own shifts replaces a global product by a *local* one. -/
theorem cocycleOf_add (g : ℕ → G) (x : ℝ) (i k : ℕ) :
    cocycleOf g x (i + k) = cocycleOf g x i * windowProd g x i k := by
  rw [cocycleOf, cocycleOf, windowProd, VandeheyAut.cfWord_add, List.map_append,
    List.prod_append]

/-- The increment splits along a subdivision of the window. -/
theorem windowProd_add (g : ℕ → G) (x : ℝ) (i k l : ℕ) :
    windowProd g x i (k + l) = windowProd g x i k * windowProd g x (i + k) l := by
  rw [windowProd, windowProd, windowProd, VandeheyAut.cfWindow_add, List.map_append,
    List.prod_append]

/-- The cocycle depends on the digit map only through the digits it reads. -/
lemma cocycleOf_congr {g h : ℕ → G} {x : ℝ} {i : ℕ}
    (hgh : ∀ j < i, g (cfDigit x j) = h (cfDigit x j)) :
    cocycleOf g x i = cocycleOf h x i := by
  simp only [cocycleOf, VandeheyAut.cfWord, List.map_map]
  refine congrArg List.prod (List.map_congr_left ?_)
  intro j hj
  exact hgh j (List.mem_range.mp hj)

end VandeheyCocycle

end NormalNumbers
