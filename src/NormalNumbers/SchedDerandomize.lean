/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ComputableNormalB
import NormalNumbers.VisitDeviationW

/-!
# Derandomization along a slow schedule from a second-moment bound

`ComputableNormalB.exists_computable_absNormal` with polynomial Fourier decay replaced by a
frequency-wise second-moment bound `𝔼‖Σ_{k<N} e(h 2ᵏ G)‖² ≤ κ |h| N² W(N)`, base `2` only, along a
primitive-recursive schedule `N_j` with `N_{j+1}/N_j → 1` at resolution `n_j → ∞`.  Extra clopen
tests (`bad'`) are avoided as well (`exists_computable_normal_sched`).
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.SchedDerandomize

open Derandomize DecayAeNormal VisitDeviation ComputableNormal
open ComputableNormalB (orbit_mem_iff_b top_iff top_of_floor_ne orbit_mem_of_top
  list_sum_range_map visitCount_eq_sum two_pow_ge exists_pos_of_sum_pos)

/-! ## The tests -/

section Tests

variable (Ψ : ℕ → ℕ → List Bool → ℕ)

/-- Approximate depth-`r` digit block at orbit index `E`. -/
def dA (b E r : ℕ) (p : List Bool) : ℕ := Ψ b (E + r) p % b ^ r

/-- Approximate visit count of the cell `(ℓ, v)` among the first `N` orbit points. -/
def Vc (b ℓ v N : ℕ) (p : List Bool) : ℕ :=
  ((List.range N).map fun k => if dA Ψ b k ℓ p = v then 1 else 0).sum

/-- Approximate visits to the top depth-`n` cell among the first `n^14 + n` orbit points. -/
def Tc (b n N : ℕ) (p : List Bool) : ℕ :=
  ((List.range (N + n)).map fun j => if dA Ψ b j n p = b ^ n - 1 then 1 else 0).sum

/-- `|Vc/N − b^{-ℓ}| > 3/(4n)`, `N = n^14`. -/
def fails (b n N ℓ v : ℕ) (p : List Bool) : Prop :=
  3 * N * b ^ ℓ < 4 * n * (Vc Ψ b ℓ v (N) p * b ^ ℓ - N +
    (N - Vc Ψ b ℓ v (N) p * b ^ ℓ))

/-- `Tc > N/(4n)`. -/
def failsTop (b n N : ℕ) (p : List Bool) : Prop := N < 4 * n * Tc Ψ b n N p

instance (b n N ℓ v : ℕ) (p : List Bool) : Decidable (fails Ψ b n N ℓ v p) := by
  unfold fails; infer_instance

instance (b n N : ℕ) (p : List Bool) : Decidable (failsTop Ψ b n N p) := by
  unfold failsTop; infer_instance

/-- Number of failing base-`2` tests at resolution `n`, count `N`. -/
def levelBad (n N : ℕ) (p : List Bool) : ℕ :=
  (if failsTop Ψ 2 n N p then 1 else 0) +
  ((List.range (n + 1)).map fun ℓ => if 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n then
    ((List.range (2 ^ ℓ)).map fun v => if fails Ψ 2 n N ℓ v p then 1 else 0).sum else 0).sum

end Tests

/-! ## Counting -/

section Count

variable (Ψ : ℕ → ℕ → List Bool → ℕ) (A : List Bool → ℝ)

/-- **Block counts: true vs approximate, error at most the top count.** -/
theorem abs_Vtrue_sub_Vc_le {N : ℕ} (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (p : List Bool) (ha : 0 ≤ A p) (hax : A p ≤ x)
    (n : ℕ) (hη : (x - A p) * (b : ℝ) ^ (N + 2 * n) ≤ 1) {ℓ v : ℕ} (hℓn : ℓ ≤ n) :
    |(visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (N) : ℝ) -
      (Vc Ψ b ℓ v (N) p : ℝ)| ≤ Tc Ψ b n N p := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hx0 : 0 ≤ x := ha.trans hax
  set t : ℕ → ℕ := fun j => if dA Ψ b j n p = b ^ n - 1 then 1 else 0 with ht
  -- termwise
  have hterm : ∀ k < N, |(if orbit b x k ∈ Set.Ico ((v : ℝ) / (b : ℝ) ^ ℓ)
      ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) then (1 : ℝ) else 0) -
      (if dA Ψ b k ℓ p = v then (1 : ℝ) else 0)| ≤ (t (ℓ + k) : ℝ) := by
    intro k hk
    have hiff := orbit_mem_iff_b b hb x hx0 k ℓ v
    by_cases hfl : ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ = ⌊A p * (b : ℝ) ^ (k + ℓ)⌋₊
    · have hd : dA Ψ b k ℓ p = ⌊x * (b : ℝ) ^ (k + ℓ)⌋₊ % b ^ ℓ := by
        rw [dA, hΨ, hfl]
      have hPQ : orbit b x k ∈ Set.Ico ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) ↔
          dA Ψ b k ℓ p = v := by rw [hiff, hd]
      have ht0 : (0 : ℝ) ≤ t (ℓ + k) := by positivity
      by_cases hQ : dA Ψ b k ℓ p = v
      · rw [if_pos (hPQ.2 hQ), if_pos hQ]; simpa using ht0
      · rw [if_neg (fun h => hQ (hPQ.1 h)), if_neg hQ]; simpa using ht0
    · have htop := top_of_floor_ne b hb ha hax (k + ℓ) n ?_ hfl
      · have : t (ℓ + k) = 1 := by
          simp only [ht, dA, hΨ, show ℓ + k + n = k + ℓ + n by ring]
          rw [if_pos htop]
        rw [this]
        split_ifs <;> norm_num
      · have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
        have hpow : (b : ℝ) ^ (k + ℓ) * (b : ℝ) ^ n ≤ (b : ℝ) ^ (N + 2 * n) := by
          rw [← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
        rw [le_div_iff₀ hbn]
        have h0 : 0 ≤ x - A p := by linarith
        calc (x - A p) * (b : ℝ) ^ (k + ℓ) * (b : ℝ) ^ n
            = (x - A p) * ((b : ℝ) ^ (k + ℓ) * (b : ℝ) ^ n) := by ring
          _ ≤ (x - A p) * (b : ℝ) ^ (N + 2 * n) := by gcongr
          _ ≤ 1 := hη
  rw [visitCount_eq_sum, Vc, list_sum_range_map, Tc, list_sum_range_map]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.1 hk)).trans ?_
  calc ∑ k ∈ Finset.range (N), (t (ℓ + k) : ℝ)
      ≤ ∑ j ∈ Finset.range (ℓ + N), (t j : ℝ) := by
        rw [Finset.sum_range_add]; simp only [le_add_iff_nonneg_left]; positivity
    _ ≤ ∑ j ∈ Finset.range (N + n), (t j : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          fun _ _ _ => by positivity
    _ = _ := by simp only [ht]; push_cast; rfl

/-- **Top count ≤ true visits near `0` and near `1`.** -/
theorem Tc_le {N : ℕ} (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (p : List Bool) (ha : 0 ≤ A p) (hax : A p ≤ x)
    (n : ℕ) (hη : (x - A p) * (b : ℝ) ^ (N + 2 * n) ≤ 1) :
    (Tc Ψ b n N p : ℝ) ≤ visitCount (orbit b x) 0 (1 / (b : ℝ) ^ n) (N + n) +
      visitCount (orbit b x) (1 - 1 / (b : ℝ) ^ n) 1 (N + n) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  rw [Tc, list_sum_range_map, visitCount_eq_sum, visitCount_eq_sum]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  by_cases h1 : dA Ψ b j n p = b ^ n - 1
  swap
  · rw [if_neg h1]; split_ifs <;> norm_num
  rw [if_pos h1]
  have hη' : (x - A p) * (b : ℝ) ^ j ≤ 1 / (b : ℝ) ^ n := by
    have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    have hpow : (b : ℝ) ^ j * (b : ℝ) ^ n ≤ (b : ℝ) ^ (N + 2 * n) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
    rw [le_div_iff₀ hbn]
    have h0 : 0 ≤ x - A p := by linarith
    calc (x - A p) * (b : ℝ) ^ j * (b : ℝ) ^ n = (x - A p) * ((b : ℝ) ^ j * (b : ℝ) ^ n) := by ring
      _ ≤ (x - A p) * (b : ℝ) ^ (N + 2 * n) := by gcongr
      _ ≤ 1 := hη
  have htop : ⌊A p * (b : ℝ) ^ (j + n)⌋₊ % b ^ n = b ^ n - 1 := by
    rw [dA, hΨ] at h1; exact h1
  rcases orbit_mem_of_top b hb ha hax j n hη' htop with h | h
  · rw [if_pos h]; split_ifs <;> norm_num
  · rw [if_pos h]; split_ifs <;> norm_num

end Count

/-! ## Test outcomes -/

section Outcomes

variable (Ψ : ℕ → ℕ → List Bool → ℕ)

theorem fails_iff_b {b n N ℓ v : ℕ} {p : List Bool} (hn : 1 ≤ n) (hb : 1 ≤ b) (hN1 : 1 ≤ N) :
    fails Ψ b n N ℓ v p ↔
      3 / (4 * (n : ℝ)) < |(Vc Ψ b ℓ v (N) p : ℝ) / (N : ℕ) - 1 / (b : ℝ) ^ ℓ| := by
  unfold fails
  have key : ((4 * n * (Vc Ψ b ℓ v (N) p * b ^ ℓ - N +
      (N - Vc Ψ b ℓ v (N) p * b ^ ℓ)) : ℕ) : ℝ) =
      4 * n * |(Vc Ψ b ℓ v (N) p : ℝ) * (b : ℝ) ^ ℓ - (N : ℝ)| := by
    rw [Nat.cast_mul (4 * n), cast_absdiff]; push_cast; ring
  rw [← @Nat.cast_lt ℝ, key]
  push_cast
  set V : ℝ := (Vc Ψ b ℓ v (N) p : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hP : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have eq : V / (N : ℝ) - 1 / (b : ℝ) ^ ℓ =
      (V * (b : ℝ) ^ ℓ - (N : ℝ)) / ((N : ℝ) * (b : ℝ) ^ ℓ) := by
    field_simp
  rw [eq, abs_div, abs_of_pos (show (0:ℝ) < (N : ℝ) * (b : ℝ) ^ ℓ by positivity),
    div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

theorem failsTop_iff_b {b n N : ℕ} {p : List Bool} :
    failsTop Ψ b n N p ↔ ((N : ℕ) : ℝ) < 4 * n * (Tc Ψ b n N p : ℝ) := by
  unfold failsTop
  rw [← @Nat.cast_lt ℝ]; push_cast; rfl

theorem eta_le (A : List Bool → ℝ) {n N : ℕ} (x : ℝ) (p : List Bool)
    (hax : A p ≤ x) (hxa : x ≤ A p + (1 / 2 : ℝ) ^ (N + 2 * n)) :
    (x - A p) * ((2 : ℕ) : ℝ) ^ (N + 2 * n) ≤ 1 := by
  have h0 : 0 ≤ x - A p := by linarith
  calc (x - A p) * ((2 : ℕ) : ℝ) ^ (N + 2 * n)
      ≤ (1 / 2 : ℝ) ^ (N + 2 * n) * 2 ^ (N + 2 * n) := by push_cast; gcongr; linarith
    _ = 1 := by rw [← mul_pow]; norm_num

/-- Passing the tests: every tested block has true frequency within `1/n`. -/
theorem good_of_pass {N : ℕ} (A : List Bool → ℝ) (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    {b n ℓ v : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hℓn : ℓ ≤ n) (x : ℝ) (p : List Bool)
    (ha : 0 ≤ A p) (hax : A p ≤ x) (hη : (x - A p) * (b : ℝ) ^ (N + 2 * n) ≤ 1)
    (htop : ¬ failsTop Ψ b n N p) (hf : ¬ fails Ψ b n N ℓ v p) :
    |(visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (N) : ℝ) /
      ((N : ℕ) : ℝ) - 1 / (b : ℝ) ^ ℓ| ≤ 1 / (n : ℝ) := by
  rw [fails_iff_b Ψ hn (by omega) hN1, not_lt] at hf
  rw [failsTop_iff_b, not_lt] at htop
  have hd := abs_Vtrue_sub_Vc_le Ψ A hΨ b hb x p ha hax n hη hℓn (v := v)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  set Vt := (visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (N) : ℝ)
  set V := (Vc Ψ b ℓ v (N) p : ℝ)
  set T := (Tc Ψ b n N p : ℝ)
  have hT : T / ((N : ℕ) : ℝ) ≤ 1 / (4 * (n : ℝ)) := by
    rw [div_le_div_iff₀ hN (by positivity)]; linarith
  have hd' : |Vt / ((N : ℕ) : ℝ) - V / ((N : ℕ) : ℝ)| ≤ T / ((N : ℕ) : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hN]; exact div_le_div_of_nonneg_right hd hN.le
  have e : 1 / (n : ℝ) = 3 / (4 * n) + 1 / (4 * n) := by field_simp; ring
  rw [e]
  calc |Vt / ((N : ℕ) : ℝ) - 1 / (b : ℝ) ^ ℓ|
      ≤ |V / ((N : ℕ) : ℝ) - 1 / (b : ℝ) ^ ℓ| + |Vt / ((N : ℕ) : ℝ) - V / ((N : ℕ) : ℝ)| := by
        have := abs_sub_le (Vt / ((N : ℕ) : ℝ)) (V / ((N : ℕ) : ℝ)) (1 / (b : ℝ) ^ ℓ)
        linarith
    _ ≤ _ := by gcongr; exact hd'.trans hT

/-- Failing a block test without failing the top test: true deviation `> 1/(2n)`. -/
theorem dev_of_fails {N : ℕ} (A : List Bool → ℝ) (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    {b n ℓ v : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hℓn : ℓ ≤ n) (x : ℝ) (p : List Bool)
    (ha : 0 ≤ A p) (hax : A p ≤ x) (hη : (x - A p) * (b : ℝ) ^ (N + 2 * n) ≤ 1)
    (htop : ¬ failsTop Ψ b n N p) (hf : fails Ψ b n N ℓ v p) :
    1 / (2 * (n : ℝ)) <
      |(visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (N) : ℝ) /
        ((N : ℕ) : ℝ) - 1 / (b : ℝ) ^ ℓ| := by
  rw [fails_iff_b Ψ hn (by omega) hN1] at hf
  rw [failsTop_iff_b, not_lt] at htop
  have hd := abs_Vtrue_sub_Vc_le Ψ A hΨ b hb x p ha hax n hη hℓn (v := v)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hN1
  set Vt := (visitCount (orbit b x) ((v : ℝ) / (b : ℝ) ^ ℓ) ((v + 1 : ℝ) / (b : ℝ) ^ ℓ) (N) : ℝ)
  set V := (Vc Ψ b ℓ v (N) p : ℝ)
  set T := (Tc Ψ b n N p : ℝ)
  have hT : T / ((N : ℕ) : ℝ) ≤ 1 / (4 * (n : ℝ)) := by
    rw [div_le_div_iff₀ hN (by positivity)]; linarith
  have hd' : |Vt / ((N : ℕ) : ℝ) - V / ((N : ℕ) : ℝ)| ≤ T / ((N : ℕ) : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hN]; exact div_le_div_of_nonneg_right hd hN.le
  have e : 3 / (4 * (n : ℝ)) = 1 / (2 * n) + 1 / (4 * n) := by field_simp; ring
  rw [e] at hf
  have := abs_sub_le (V / ((N : ℕ) : ℝ)) (Vt / ((N : ℕ) : ℝ)) (1 / (b : ℝ) ^ ℓ)
  have hc := abs_sub_comm (V / ((N : ℕ) : ℝ)) (Vt / ((N : ℕ) : ℝ))
  linarith

/-- Failing the top test: many true visits near `0` or near `1`. -/
theorem tail_of_failsTop {N : ℕ} (A : List Bool → ℝ) (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊)
    {b n : ℕ} (hb : 2 ≤ b) (x : ℝ) (p : List Bool)
    (ha : 0 ≤ A p) (hax : A p ≤ x) (hη : (x - A p) * (b : ℝ) ^ (N + 2 * n) ≤ 1)
    (htop : failsTop Ψ b n N p) :
    ((N : ℕ) : ℝ) < 8 * n * visitCount (orbit b x) 0 (1 / (b : ℝ) ^ n) (N + n) ∨
    ((N : ℕ) : ℝ) < 8 * n * visitCount (orbit b x) (1 - 1 / (b : ℝ) ^ n) 1 (N + n) := by
  rw [failsTop_iff_b] at htop
  have h := Tc_le Ψ A hΨ b hb x p ha hax n hη
  by_contra hc
  push Not at hc
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [hc.1, hc.2, mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 4 * n)]

end Outcomes


/-! ## Probability bounds from a second moment -/

/-- `Σ_{h ∈ ℤ} √|h| / h²` (the `h = 0` term is `0`). -/
noncomputable def Zc : ℝ := ∑' h : ℤ, Real.sqrt |(h : ℝ)| / (h : ℝ) ^ 2

theorem summable_Zc : Summable fun h : ℤ => Real.sqrt |(h : ℝ)| / (h : ℝ) ^ 2 := by
  refine (Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)).congr fun h => ?_
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have ha : 0 < |(h : ℝ)| := abs_pos.2 (by exact_mod_cast hh)
    rw [Real.sqrt_eq_rpow, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_sub ha]
    norm_num

theorem Zc_nonneg : 0 ≤ Zc := tsum_nonneg fun h => by positivity

theorem hasSum_plB_w (ρ : ℝ) (hρ : 0 < ρ) (K : ℝ) (hK : 0 ≤ K) :
    HasSum (fun h : ℤ => plB ρ h * Real.sqrt (K * |(h : ℝ)|))
      (2 / (ρ * Real.pi ^ 2) * Real.sqrt K * Zc) := by
  have := (summable_Zc.hasSum).mul_left (2 / (ρ * Real.pi ^ 2) * Real.sqrt K)
  refine this.congr_fun fun h => ?_
  unfold plB
  rw [Real.sqrt_mul hK]
  have := Real.pi_pos.ne'
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · field_simp

variable (G : (ℕ → Bool) → ℝ)

/-- Block deviation `> 1/(2n)` at count `N`. -/
theorem block_prob_w (hG : Measurable G) {κ Wv : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ Wv) {N : ℕ}
    (hN : 1 ≤ N)
    (hsm : ∀ h : ℤ, h ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤ κ * |(h : ℝ)| * N ^ 2 * Wv)
    {n ℓ v : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hv : v < 2 ^ ℓ) :
    coins.real {ω | 1 / (2 * (n : ℝ)) <
      |(visitCount (orbit 2 (G ω)) ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) N : ℝ) /
        (N : ℝ) - 1 / 2 ^ ℓ|} ≤ 144 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hvR : (v : ℝ) + 1 ≤ 2 ^ ℓ := by exact_mod_cast hv
  have hP2 : (2 : ℝ) ≤ 2 ^ ℓ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
  set ρ : ℝ := 1 / (6 * (n : ℝ))
  have hρ : 0 < ρ := by positivity
  set w : ℤ → ℝ := fun h => Real.sqrt (κ * Wv * |(h : ℝ)|)
  have hsm' : ∀ h : ℤ, h ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤ (w h) ^ 2 * (N : ℝ) ^ 2 := by
    intro h hh
    rw [Real.sq_sqrt (by positivity)]
    refine (hsm h hh).trans (le_of_eq ?_); ring
  have hS := hasSum_plB_w ρ hρ (κ * Wv) (by positivity)
  have e1 : (v + 1 : ℝ) / 2 ^ ℓ - (v : ℝ) / 2 ^ ℓ = 1 / 2 ^ ℓ := by ring
  have hdev := visit_deviation_w coins G hG N hN w (fun h => Real.sqrt_nonneg _) hsm'
    ((v : ℝ) / 2 ^ ℓ) ((v + 1 : ℝ) / 2 ^ ℓ) ρ ρ
    (by positivity) (by gcongr; linarith) (by rw [div_le_one hP]; exact hvR)
    (by rw [e1, div_le_div_iff₀ hP (by norm_num)]; linarith)
    hρ (by simp only [ρ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    hρ hS.summable
  rw [e1, hS.tsum_eq] at hdev
  have e2 : 2 * ρ + ρ = 1 / (2 * (n : ℝ)) := by simp only [ρ]; field_simp; ring
  rw [e2] at hdev
  refine hdev.trans ?_
  have hpi : 1 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three; nlinarith
  have hZ := Zc_nonneg
  have hsq := Real.sqrt_nonneg (κ * Wv)
  simp only [ρ]
  rw [show 2 * (2 / (1 / (6 * (n : ℝ)) * Real.pi ^ 2) * Real.sqrt (κ * Wv) * Zc / (1 / (6 * (n : ℝ))))
      = 144 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc / Real.pi ^ 2 by
    field_simp; ring]
  exact div_le_self (by positivity) hpi

/-- Visits to a short cell exceeding `N/(8n)` among `N + n` points. -/
theorem tail_prob_w (hG : Measurable G) {κ Wv : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ Wv) {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (hsm : ∀ h : ℤ, h ≠ 0 → ∫ ω, ‖∑ k ∈ Finset.range (N + n), ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤
      κ * |(h : ℝ)| * ((N + n : ℕ) : ℝ) ^ 2 * Wv)
    (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hlen : c - a ≤ 1 / (32 * (n : ℝ))) :
    coins.real {ω | (N : ℝ) < 8 * n * visitCount (orbit 2 (G ω)) a c (N + n)} ≤
      36864 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 1 ≤ N + n := by omega
  set ρ : ℝ := 1 / (96 * (n : ℝ))
  have hρ : 0 < ρ := by positivity
  set w : ℤ → ℝ := fun h => Real.sqrt (κ * Wv * |(h : ℝ)|)
  have hsm' : ∀ h : ℤ, h ≠ 0 → ∫ ω, ‖∑ k ∈ Finset.range (N + n), ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤
      (w h) ^ 2 * ((N + n : ℕ) : ℝ) ^ 2 := by
    intro h hh
    rw [Real.sq_sqrt (by positivity)]
    refine (hsm h hh).trans (le_of_eq ?_); ring
  have hS := hasSum_plB_w ρ hρ (κ * Wv) (by positivity)
  have hdev := visit_deviation_w coins G hG (N + n) hN1 w (fun h => Real.sqrt_nonneg _) hsm' a c ρ ρ
    ha hac hc (hlen.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith))
    hρ (by simp only [ρ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith) hρ
    hS.summable
  rw [hS.tsum_eq] at hdev
  have hsub : {ω | (N : ℝ) < 8 * n * visitCount (orbit 2 (G ω)) a c (N + n)} ⊆
      {ω | 2 * ρ + ρ <
        |(visitCount (orbit 2 (G ω)) a c (N + n) : ℝ) / ((N + n : ℕ) : ℝ) - (c - a)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    set V := (visitCount (orbit 2 (G ω)) a c (N + n) : ℝ)
    have hNn : (0 : ℝ) < ((N + n : ℕ) : ℝ) := by positivity
    have hle : ((N + n : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      push_cast; have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      linarith
    have h1 : 1 / (16 * (n : ℝ)) < V / ((N + n : ℕ) : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hNn]
      nlinarith
    have e : 2 * ρ + ρ = 1 / (32 * (n : ℝ)) := by simp only [ρ]; field_simp; ring
    rw [e, lt_abs]; left
    have : 1 / (16 * (n : ℝ)) = 1 / (32 * (n : ℝ)) + 1 / (32 * (n : ℝ)) := by
      field_simp; ring
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hdev.trans ?_)
  have hpi : 1 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three; nlinarith
  have hZ := Zc_nonneg
  simp only [ρ]
  rw [show 2 * (2 / (1 / (96 * (n : ℝ)) * Real.pi ^ 2) * Real.sqrt (κ * Wv) * Zc / (1 / (96 * (n : ℝ))))
      = 36864 * (n : ℝ) ^ 2 * Real.sqrt (κ * Wv) * Zc / Real.pi ^ 2 by
    field_simp; ring]
  exact div_le_self (by positivity) hpi

section Level

variable (Ψ : ℕ → ℕ → List Bool → ℕ)

theorem levelBad_pos_cases {n N : ℕ} {p : List Bool} (h : 0 < levelBad Ψ n N p) :
    failsTop Ψ 2 n N p ∨ ∃ ℓ ∈ (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n),
        ∃ v ∈ Finset.range (2 ^ ℓ), fails Ψ 2 n N ℓ v p := by
  rw [levelBad] at h
  by_cases ht : failsTop Ψ 2 n N p
  · exact Or.inl ht
  · right
    rw [if_neg ht, zero_add, list_sum_range_map] at h
    obtain ⟨ℓ, hℓ, hpos⟩ := exists_pos_of_sum_pos h
    split_ifs at hpos with hc
    · rw [list_sum_range_map] at hpos
      obtain ⟨v, hv, hpos⟩ := exists_pos_of_sum_pos hpos
      split_ifs at hpos with hf
      · exact ⟨ℓ, Finset.mem_filter.2 ⟨hℓ, hc⟩, v, hv, hf⟩
      · exact absurd hpos (lt_irrefl 0)
    · exact absurd hpos (lt_irrefl 0)

theorem pass_of_levelBad_zero {n N : ℕ} {p : List Bool} (h : levelBad Ψ n N p = 0) :
    ¬ failsTop Ψ 2 n N p ∧ ∀ ℓ, 1 ≤ ℓ → 2 ^ ℓ ≤ n → ∀ v, v < 2 ^ ℓ → ¬ fails Ψ 2 n N ℓ v p := by
  rw [levelBad, Nat.add_eq_zero_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ht => by rw [if_pos ht] at h1; exact one_ne_zero h1, fun ℓ hℓ hℓn v hv hf => ?_⟩
  rw [list_sum_range_map, Finset.sum_eq_zero_iff] at h2
  have hℓle : ℓ ≤ n := (Nat.lt_two_pow_self).le.trans hℓn
  have h3 := h2 ℓ (Finset.mem_range.2 (by omega))
  rw [if_pos ⟨hℓ, hℓn⟩, list_sum_range_map, Finset.sum_eq_zero_iff] at h3
  have h4 := h3 v (Finset.mem_range.2 hv)
  rw [if_pos hf] at h4
  exact one_ne_zero h4

end Level

theorem eta_le' (A : List Bool → ℝ) {n N D : ℕ} (hD : N + 2 * n ≤ D) (x : ℝ) (p : List Bool)
    (hax : A p ≤ x) (hxa : x ≤ A p + (1 / 2 : ℝ) ^ D) :
    (x - A p) * ((2 : ℕ) : ℝ) ^ (N + 2 * n) ≤ 1 := by
  refine eta_le A x p hax (hxa.trans ?_)
  have := pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hD
  linarith

/-- **Level mass.** -/
theorem level_bound_w (Ψ : ℕ → ℕ → List Bool → ℕ) (A : List Bool → ℝ)
    (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊) (hA0 : ∀ p, 0 ≤ A p)
    (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hAG : ∀ ω D, A (pre ω D) ≤ G ω ∧ G ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D)
    {κ Wv : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ Wv) {n N D : ℕ} (hn : 8 ≤ n) (hnN : n ≤ N)
    (hD : N + 2 * n ≤ D)
    (hsm1 : ∀ h : ℤ, h ≠ 0 →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤ κ * |(h : ℝ)| * N ^ 2 * Wv)
    (hsm2 : ∀ h : ℤ, h ≠ 0 → ∫ ω, ‖∑ k ∈ Finset.range (N + n), ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤
      κ * |(h : ℝ)| * ((N + n : ℕ) : ℝ) ^ 2 * Wv) :
    coins.real {ω | 0 < levelBad Ψ n N (pre ω D)} ≤
      74016 * (n : ℝ) ^ 3 * Real.sqrt (κ * Wv) * Zc := by
  set L := (Finset.range (n + 1)).filter (fun ℓ => 1 ≤ ℓ ∧ 2 ^ ℓ ≤ n)
  set T0 : Set (ℕ → Bool) := {ω | (N : ℝ) <
    8 * n * visitCount (orbit 2 (G ω)) 0 (1 / ((2 : ℕ) : ℝ) ^ n) (N + n)}
  set T1 : Set (ℕ → Bool) := {ω | (N : ℝ) <
    8 * n * visitCount (orbit 2 (G ω)) (1 - 1 / ((2 : ℕ) : ℝ) ^ n) 1 (N + n)}
  set Dv : ℕ → ℕ → Set (ℕ → Bool) := fun ℓ v => {ω | 1 / (2 * (n : ℝ)) <
      |(visitCount (orbit 2 (G ω)) ((v : ℝ) / ((2 : ℕ) : ℝ) ^ ℓ) ((v + 1 : ℝ) / ((2 : ℕ) : ℝ) ^ ℓ) N : ℝ) /
        (N : ℝ) - 1 / ((2 : ℕ) : ℝ) ^ ℓ|}
  have hn1 : 1 ≤ n := by omega
  have hN1 : 1 ≤ N := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsub : {ω | 0 < levelBad Ψ n N (pre ω D)} ⊆
      (T0 ∪ T1) ∪ ⋃ ℓ ∈ L, ⋃ v ∈ Finset.range (2 ^ ℓ), Dv ℓ v := by
    intro ω hω
    have hcase := levelBad_pos_cases Ψ hω
    have hax := (hAG ω D).1
    have hη := eta_le' A hD (G ω) (pre ω D) hax (hAG ω D).2
    simp only [Set.mem_iUnion, Set.mem_union]
    by_cases ht : failsTop Ψ 2 n N (pre ω D)
    · left
      exact tail_of_failsTop Ψ A hΨ le_rfl (G ω) (pre ω D) (hA0 _) hax hη ht
    · right
      rcases hcase with h | ⟨ℓ, hℓ, v, hv, hf⟩
      · exact absurd h ht
      have hℓ' := Finset.mem_filter.1 hℓ
      refine ⟨ℓ, hℓ, v, hv, ?_⟩
      exact dev_of_fails Ψ A hΨ le_rfl hn1 hN1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ'.1)) (G ω)
        (pre ω D) (hA0 _) hax hη ht hf
  set X := Real.sqrt (κ * Wv) * Zc
  have hX : 0 ≤ X := mul_nonneg (Real.sqrt_nonneg _) Zc_nonneg
  have hbn : (32 * (n : ℝ)) ≤ ((2 : ℕ) : ℝ) ^ n := by exact_mod_cast two_pow_ge n hn
  have hP : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ n := by positivity
  have hsmall : 1 / ((2 : ℕ) : ℝ) ^ n ≤ 1 / (32 * (n : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) hbn
  have hle1 : 1 / ((2 : ℕ) : ℝ) ^ n ≤ 1 := hsmall.trans (by
    rw [div_le_one (by positivity)]; linarith)
  have hT0 : coins.real T0 ≤ 36864 * (n : ℝ) ^ 2 * X := by
    have := tail_prob_w G hGm hκ hW hn1 hnN hsm2 0 (1 / ((2 : ℕ) : ℝ) ^ n) le_rfl (by positivity) hle1
      (by rw [sub_zero]; exact hsmall)
    simpa [T0, X, mul_assoc] using this
  have hT1 : coins.real T1 ≤ 36864 * (n : ℝ) ^ 2 * X := by
    have := tail_prob_w G hGm hκ hW hn1 hnN hsm2 (1 - 1 / ((2 : ℕ) : ℝ) ^ n) 1 (sub_nonneg.2 hle1)
      (by linarith [hP.le, one_div_pos.2 hP]) le_rfl (by rw [sub_sub_cancel]; exact hsmall)
    simpa [T1, X, mul_assoc] using this
  have hDv : ∀ ℓ ∈ L, ∀ v ∈ Finset.range (2 ^ ℓ), coins.real (Dv ℓ v) ≤ 144 * (n : ℝ) ^ 2 * X := by
    intro ℓ hℓ v hv
    have := block_prob_w G hGm hκ hW hN1 hsm1 hn1 (Finset.mem_filter.1 hℓ).2.1
      (Finset.mem_range.1 hv)
    simpa [Dv, X, mul_assoc] using this
  have hblocks : (∑ ℓ ∈ L, ((2 ^ ℓ : ℕ) : ℝ)) ≤ 2 * n := by
    have := sum_blocks_le n
    exact_mod_cast this
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans ?_)
  have h1 : coins.real (T0 ∪ T1) ≤ 2 * (36864 * (n : ℝ) ^ 2 * X) :=
    (measureReal_union_le _ _).trans (by linarith)
  have h2 : coins.real (⋃ ℓ ∈ L, ⋃ v ∈ Finset.range (2 ^ ℓ), Dv ℓ v) ≤
      2 * n * (144 * (n : ℝ) ^ 2 * X) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ ℓ ∈ L, coins.real (⋃ v ∈ Finset.range (2 ^ ℓ), Dv ℓ v)
        ≤ ∑ ℓ ∈ L, ((2 ^ ℓ : ℕ) : ℝ) * (144 * (n : ℝ) ^ 2 * X) := by
          refine Finset.sum_le_sum fun ℓ hℓ => (measureReal_biUnion_finset_le _ _).trans ?_
          calc ∑ v ∈ Finset.range (2 ^ ℓ), coins.real (Dv ℓ v)
              ≤ ∑ v ∈ Finset.range (2 ^ ℓ), 144 * (n : ℝ) ^ 2 * X :=
                Finset.sum_le_sum fun v hv => hDv ℓ hℓ v hv
            _ = _ := by simp
      _ = (∑ ℓ ∈ L, ((2 ^ ℓ : ℕ) : ℝ)) * (144 * (n : ℝ) ^ 2 * X) := by rw [Finset.sum_mul]
      _ ≤ _ := by gcongr
  have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
  have : coins.real (T0 ∪ T1) + coins.real (⋃ ℓ ∈ L, ⋃ v ∈ Finset.range (2 ^ ℓ), Dv ℓ v) ≤
      73728 * (n : ℝ) ^ 3 * X + 288 * (n : ℝ) ^ 3 * X := by
    have e2 : 2 * n * (144 * (n : ℝ) ^ 2 * X) = 288 * (n : ℝ) ^ 3 * X := by ring
    nlinarith [mul_le_mul_of_nonneg_right hn2 hX]
  calc _ ≤ _ := this
    _ = 74016 * (n : ℝ) ^ 3 * Real.sqrt (κ * Wv) * Zc := by simp only [X]; ring

end NormalNumbers.SchedDerandomize
