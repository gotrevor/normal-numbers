/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AbelianWindowBlocks

/-!
# C4: an INFINITE exact window set

`probes/c4_block_iid.py` locates a block-i.i.d. witness for `S = {odd lengths}` (verified exactly
up to `L = 41`).  Take blocks of `q = 2` bits driven by a base-`8` normal sequence `c`, with the
"sorted" table

  digit `d < 2 ↦ 00`,  `2 ≤ d < 6 ↦ 10`,  `6 ≤ d ↦ 11`,

so that a block's one-count is `zdig d ∈ {0,1,2}` with the exact Binomial(2,1/2) frequencies
`2/8, 4/8, 2/8`, while the two bit marginals are `P(bit₀ = 1) = 3/4` and `P(bit₁ = 1) = 1/4`.

*Why odd works and even fails.*  A length-`L` window at offset `r ∈ {0,1}` is a whole number of
blocks plus edges.  For `L = 2a+1` the two offsets contribute weight gf `u^{2a}·(1/4 + 3x/4)` and
`u^{2a}·(3/4 + x/4)` where `u = (1+x)/2`; their average is `u^{2a}·(1+x)/2 = u^L`.  In counts this
is exactly PASCAL'S RULE.  For `L = 2a` the offsets contribute `u^{2a}` and
`u^{2a-2}(3/4+x/4)(1/4+3x/4)`, whose average differs already at `j = 0`: `7/(8·4^a)` against the
required `8/(8·4^a)`.

This file develops the counting.  `Zgf` is the digit-sum generating function; everything else is
bookkeeping on top of `Zgf_eq`.
-/

open Filter Finset Topology Polynomial

namespace NormalNumbers.Abelian

open NormalNumbers NormalNumbers.PowerBase NormalNumbers.Walsh

/-- One-count of the two-bit block assigned to the base-eight digit `d`. -/
def zdig (d : ℕ) : ℕ := (if 2 ≤ d then 1 else 0) + (if 6 ≤ d then 1 else 0)

/-- Total one-count of the blocks spelled by a base-eight word. -/
def zsumW (v : List ℕ) : ℕ := (v.map zdig).sum

/-- The generating function of the block one-count over all base-eight words of length `m`. -/
noncomputable def Zgf (m : ℕ) : ℝ[X] := ∑ k ∈ range (8 ^ m), X ^ (zsumW (wordOf 8 m k))

theorem Zgf_zero : Zgf 0 = 1 := by
  simp [Zgf, zsumW]

theorem Zgf_succ (m : ℕ) : Zgf (m + 1) = Zgf m * (∑ d ∈ range 8, X ^ zdig d) := by
  classical
  have hR : Zgf m * (∑ d ∈ range 8, (X : ℝ[X]) ^ zdig d)
      = ∑ p ∈ (range (8 ^ m)) ×ˢ (range 8),
          X ^ (zsumW (wordOf 8 m p.1) + zdig p.2) := by
    rw [Zgf, Finset.sum_mul, Finset.sum_product]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by rw [pow_add])
  rw [hR, Zgf]
  have hpow : (8 : ℕ) ^ (m + 1) = 8 ^ m * 8 := by ring
  rw [hpow]
  refine Finset.sum_nbij' (i := fun k => (k / 8, k % 8)) (j := fun p => p.1 * 8 + p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
    · exact Nat.div_lt_of_lt_mul (by omega)
    · exact Nat.mod_lt _ (by norm_num)
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_range] at h1 h2 ⊢
    calc p.1 * 8 + p.2 < p.1 * 8 + 8 := by omega
      _ = (p.1 + 1) * 8 := by ring
      _ ≤ 8 ^ m * 8 := Nat.mul_le_mul_right 8 (by omega)
  · intro k _
    exact Nat.div_add_mod' k 8
  · intro p hp
    obtain ⟨-, h2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_range] at h2
    have h3 : (p.1 * 8 + p.2) / 8 = p.1 := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by norm_num : 0 < 8),
        Nat.div_eq_of_lt h2]
      omega
    have h4 : (p.1 * 8 + p.2) % 8 = p.2 := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h2
    exact Prod.ext h3 h4
  · intro k hk
    rw [Finset.mem_range] at hk
    have hd : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hk8 : k / 8 * 8 + k % 8 = k := Nat.div_add_mod' k 8
    have hw : wordOf 8 (m + 1) k = wordOf 8 m (k / 8) ++ [k % 8] := by
      conv_lhs => rw [← hk8]
      exact wordOf_append 8 m (k / 8) (k % 8) (by norm_num) hd
    rw [hw, zsumW, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rfl

theorem Zgf_eq (m : ℕ) : Zgf m = C ((2 : ℝ) ^ m) * (1 + X) ^ (2 * m) := by
  have hd : (∑ d ∈ range 8, (X : ℝ[X]) ^ zdig d) = C (2 : ℝ) * (1 + X) ^ 2 := by
    rw [Polynomial.C_ofNat 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zdig]
    norm_num
    ring
  induction m with
  | zero => simp [Zgf_zero]
  | succ m ih =>
      rw [Zgf_succ, ih, hd, show (2 : ℝ) ^ (m + 1) = 2 ^ m * 2 from pow_succ 2 m, C_mul,
        show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
      ring

/-- **The digit-sum count.**  Exactly `2 ^ m · C(2m, j)` of the `8 ^ m` base-eight words of
length `m` spell blocks with total one-count `j`. -/
theorem zcount_eq (m j : ℕ) :
    ((range (8 ^ m)).filter (fun k => zsumW (wordOf 8 m k) = j)).card
      = 2 ^ m * (2 * m).choose j := by
  classical
  have hcoeff : (Zgf m).coeff j
      = (((range (8 ^ m)).filter (fun k => zsumW (wordOf 8 m k) = j)).card : ℝ) := by
    rw [Zgf, Polynomial.finsetSum_coeff]
    have hterm : ∀ k ∈ range (8 ^ m),
        ((X : ℝ[X]) ^ (zsumW (wordOf 8 m k))).coeff j
          = if zsumW (wordOf 8 m k) = j then (1 : ℝ) else 0 := by
      intro k _
      rw [Polynomial.coeff_X_pow]
      by_cases h : zsumW (wordOf 8 m k) = j
      · simp [h]
      · rw [if_neg (fun hc => h hc.symm), if_neg h]
    rw [Finset.sum_congr rfl hterm, Finset.card_filter]
    push_cast
    rfl
  have hval : (Zgf m).coeff j = (2 : ℝ) ^ m * ((2 * m).choose j : ℝ) := by
    rw [Zgf_eq, Polynomial.coeff_C_mul, add_comm (1 : ℝ[X]) X,
      Polynomial.coeff_X_add_one_pow]
  rw [hcoeff] at hval
  exact_mod_cast hval

end NormalNumbers.Abelian
