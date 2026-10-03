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

/-! ## Primitive recursiveness of the tests -/

section Primrec

variable (Ψ : ℕ → ℕ → List Bool → ℕ)
  (hΨp : Primrec fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2)

include hΨp

variable {α : Type*} [Primcodable α]

theorem sprimrec_dA {fb fE fr : α → ℕ} {fp : α → List Bool} (hb : Primrec fb) (hE : Primrec fE)
    (hr : Primrec fr) (hp : Primrec fp) :
    Primrec fun a => dA Ψ (fb a) (fE a) (fr a) (fp a) :=
  Primrec.nat_mod.comp (hΨp.comp (Primrec.pair hb (Primrec.pair (Primrec.nat_add.comp hE hr) hp)))
    (primrec_pow.comp hb hr)

theorem sprimrec_Vc {fb fl fv fN : α → ℕ} {fp : α → List Bool} (hb : Primrec fb)
    (hl : Primrec fl) (hv : Primrec fv) (hN : Primrec fN) (hp : Primrec fp) :
    Primrec fun a => Vc Ψ (fb a) (fl a) (fv a) (fN a) (fp a) := by
  have hg : Primrec₂ fun (a : α) (k : ℕ) => if dA Ψ (fb a) k (fl a) (fp a) = fv a then 1 else 0 :=
    (Primrec.ite (Primrec.eq.comp (sprimrec_dA Ψ hΨp (hb.comp Primrec.fst) Primrec.snd
      (hl.comp Primrec.fst) (hp.comp Primrec.fst)) (hv.comp Primrec.fst))
      (Primrec.const 1) (Primrec.const 0)).to₂
  exact primrec_sum_map (Primrec.list_range.comp hN) hg

theorem sprimrec_Tc {fb fn fN : α → ℕ} {fp : α → List Bool} (hb : Primrec fb) (hn : Primrec fn)
    (hN : Primrec fN) (hp : Primrec fp) : Primrec fun a => Tc Ψ (fb a) (fn a) (fN a) (fp a) := by
  have hg : Primrec₂ fun (a : α) (j : ℕ) =>
      if dA Ψ (fb a) j (fn a) (fp a) = fb a ^ fn a - 1 then 1 else 0 :=
    (Primrec.ite (Primrec.eq.comp (sprimrec_dA Ψ hΨp (hb.comp Primrec.fst) Primrec.snd
      (hn.comp Primrec.fst) (hp.comp Primrec.fst))
      (Primrec.nat_sub.comp (primrec_pow.comp (hb.comp Primrec.fst) (hn.comp Primrec.fst))
        (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0)).to₂
  exact primrec_sum_map (Primrec.list_range.comp (Primrec.nat_add.comp hN hn)) hg

theorem sprimrec_fails {fb fn fN fl fv : α → ℕ} {fp : α → List Bool} (hb : Primrec fb)
    (hn : Primrec fn) (hN : Primrec fN) (hl : Primrec fl) (hv : Primrec fv) (hp : Primrec fp) :
    PrimrecPred fun a => fails Ψ (fb a) (fn a) (fN a) (fl a) (fv a) (fp a) := by
  have hP : Primrec fun a => fb a ^ fl a := primrec_pow.comp hb hl
  have hV := sprimrec_Vc Ψ hΨp hb hl hv hN hp
  have hVP := Primrec.nat_mul.comp hV hP
  have lhs := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 3) hN) hP
  have rhs := Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) hn)
    (Primrec.nat_add.comp (Primrec.nat_sub.comp hVP hN) (Primrec.nat_sub.comp hN hVP))
  exact (Primrec.nat_lt.comp lhs rhs).of_eq fun a => by unfold fails; rfl

theorem sprimrec_failsTop {fb fn fN : α → ℕ} {fp : α → List Bool} (hb : Primrec fb)
    (hn : Primrec fn) (hN : Primrec fN) (hp : Primrec fp) :
    PrimrecPred fun a => failsTop Ψ (fb a) (fn a) (fN a) (fp a) := by
  exact (Primrec.nat_lt.comp hN (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) hn)
    (sprimrec_Tc Ψ hΨp hb hn hN hp))).of_eq fun a => by unfold failsTop; rfl

attribute [local irreducible] fails failsTop in
theorem sprimrec_levelBad {fn fN : α → ℕ} {fp : α → List Bool}
    (hn : Primrec fn) (hN : Primrec fN) (hp : Primrec fp) :
    Primrec fun a => levelBad Ψ (fn a) (fN a) (fp a) := by
  have htop : Primrec fun a => if failsTop Ψ 2 (fn a) (fN a) (fp a) then 1 else 0 :=
    Primrec.ite (sprimrec_failsTop Ψ hΨp (Primrec.const 2) hn hN hp) (Primrec.const 1)
      (Primrec.const 0)
  have hin : Primrec fun y : α × ℕ =>
      ((List.range (2 ^ y.2)).map fun v =>
        if fails Ψ 2 (fn y.1) (fN y.1) y.2 v (fp y.1) then 1 else 0).sum := by
    have hfv : Primrec₂ fun (y : α × ℕ) (v : ℕ) =>
        if fails Ψ 2 (fn y.1) (fN y.1) y.2 v (fp y.1) then 1 else 0 :=
      (Primrec.ite (sprimrec_fails Ψ hΨp (Primrec.const 2)
        (hn.comp (Primrec.fst.comp Primrec.fst)) (hN.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd
        (hp.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 1) (Primrec.const 0)).to₂
    exact primrec_sum_map (Primrec.list_range.comp
      (primrec_pow.comp (Primrec.const 2) Primrec.snd)) hfv
  have hcond : PrimrecPred fun y : α × ℕ => 1 ≤ y.2 ∧ 2 ^ y.2 ≤ fn y.1 :=
    PrimrecPred.and (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
      (Primrec.nat_le.comp (primrec_pow.comp (Primrec.const 2) Primrec.snd)
        (hn.comp Primrec.fst))
  have hg : Primrec₂ fun (a : α) (ℓ : ℕ) => if 1 ≤ ℓ ∧ 2 ^ ℓ ≤ fn a then
      ((List.range (2 ^ ℓ)).map fun v =>
        if fails Ψ 2 (fn a) (fN a) ℓ v (fp a) then 1 else 0).sum else 0 :=
    (Primrec.ite hcond hin (Primrec.const 0)).to₂
  exact (Primrec.nat_add.comp htop
    (primrec_sum_map (Primrec.list_range.comp (Primrec.succ.comp hn)) hg)).of_eq
    fun a => rfl

end Primrec

/-! ## Assembly -/

theorem pre_take' (ω : ℕ → Bool) {m n : ℕ} (h : m ≤ n) : (pre ω n).take m = pre ω m := by
  simp only [pre]
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem dens_eq_real (bad : ℕ → List Bool → Bool) (d : ℕ → ℕ) (j : ℕ) :
    dens bad d j [] = coins.real {ω | bad j (pre ω (d j)) = true} := by
  unfold dens
  simp only [List.length_nil, Nat.sub_zero]
  rw [← coins_pre, measureReal_def]
  congr 2
  ext ω
  simp [badAt, List.take_of_length_le (le_of_eq (length_pre ω _))]

/-- **Derandomization along a slow schedule.** -/
theorem exists_computable_normal_sched (Ψ : ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2) (A : List Bool → ℝ)
    (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊) (hA0 : ∀ p, 0 ≤ A p)
    (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hAG : ∀ ω D, A (pre ω D) ≤ G ω ∧ G ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D)
    {κ : ℝ} (hκ : 0 ≤ κ) (W : ℕ → ℝ) (hW0 : ∀ N, 0 ≤ W N) (hWa : Antitone W)
    (hsm : ∀ h : ℤ, h ≠ 0 → ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * 2 ^ k * G ω)‖ ^ 2 ∂coins ≤ κ * |(h : ℝ)| * N ^ 2 * W N)
    (Ns nr : ℕ → ℕ) (hNs : Primrec Ns) (hnr : Primrec nr) (hNtop : Tendsto Ns atTop atTop)
    (hrat : ∀ a : ℝ, 1 < a → ∀ᶠ j in atTop, (Ns (j + 1) : ℝ) ≤ a * Ns j)
    (hnrtop : Tendsto nr atTop atTop)
    (hev : ∀ᶠ j in atTop, 8 ≤ nr j ∧ nr j ≤ Ns j ∧
      (nr j : ℝ) ^ 6 * W (Ns j) ≤ 1 / ((j : ℝ) + 1) ^ 4)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧ IsNormal 2 (G e) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hev
  set B : ℝ := 74016 * Real.sqrt κ * Zc + 1 with hBdef
  have hB0 : 0 < B := by have := Zc_nonneg; positivity
  set j₁ : ℕ := j₀ + ⌈4 * B⌉₊ + 2 with hj₁def
  have hj₁B : 4 * B ≤ (j₁ : ℝ) := by
    have := Nat.le_ceil (4 * B); rw [hj₁def]; push_cast; linarith
  set D1 : ℕ → ℕ := fun J => Ns J + 2 * nr J with hD1
  set bad : ℕ → List Bool → Bool := fun j p =>
    decide (0 < levelBad Ψ (nr (j + j₁)) (Ns (j + j₁)) (p.take (D1 (j + j₁)))) ||
      bad' (j + j₁) (p.take (d' (j + j₁))) with hbaddef
  set d : ℕ → ℕ := fun j => max (D1 (j + j₁)) (d' (j + j₁)) with hddef
  have hJ1 : Primrec fun j : ℕ => j + j₁ := Primrec.nat_add.comp Primrec.id (Primrec.const _)
  have hD1p : Primrec D1 := Primrec.nat_add.comp hNs (Primrec.nat_mul.comp (Primrec.const 2) hnr)
  have hbad : Primrec₂ bad := by
    have h1 : PrimrecPred fun x : ℕ × List Bool =>
        0 < levelBad Ψ (nr (x.1 + j₁)) (Ns (x.1 + j₁)) (x.2.take (D1 (x.1 + j₁))) :=
      Primrec.nat_lt.comp (Primrec.const 0) (sprimrec_levelBad Ψ hΨp
        (hnr.comp (hJ1.comp Primrec.fst)) (hNs.comp (hJ1.comp Primrec.fst))
        (Primrec.list_take.comp (hD1p.comp (hJ1.comp Primrec.fst)) Primrec.snd))
    have h2 : Primrec fun x : ℕ × List Bool => bad' (x.1 + j₁) (x.2.take (d' (x.1 + j₁))) :=
      hbad'.comp (hJ1.comp Primrec.fst)
        (Primrec.list_take.comp (hd'.comp (hJ1.comp Primrec.fst)) Primrec.snd)
    exact (Primrec.or.comp h1.decide h2).to₂
  have hd : Primrec d := Primrec.nat_max.comp (hD1p.comp hJ1) (hd'.comp hJ1)
  have hdj : ∀ j, dens bad d j [] ≤ B / ((j : ℝ) + ((j₁ + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j
    set J := j + j₁ with hJ
    obtain ⟨hn8, hnN, hW6⟩ := hj₀ J (by omega)
    rw [dens_eq_real]
    have hsub : {ω | bad j (pre ω (d j)) = true} ⊆
        {ω | 0 < levelBad Ψ (nr J) (Ns J) (pre ω (D1 J))} ∪ {ω | bad' J (pre ω (d' J)) = true} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, hbaddef, Bool.or_eq_true, decide_eq_true_eq] at hω
      rw [pre_take' ω (le_max_left _ _), pre_take' ω (le_max_right _ _)] at hω
      exact hω
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans ?_)
    have hN1 : 1 ≤ Ns J := by omega
    have hW := hW0 (Ns J)
    have hL := level_bound_w Ψ A hΨ hA0 G hGm hAG hκ hW (n := nr J) (N := Ns J) (D := D1 J) hn8
      hnN le_rfl (fun h hh => hsm h hh _ hN1) (fun h hh => (hsm h hh _ (by omega)).trans (by
        have := hWa (show Ns J ≤ Ns J + nr J by omega)
        have : 0 ≤ κ * |(h : ℝ)| * ((Ns J + nr J : ℕ) : ℝ) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (hWa (by omega)) this))
    have hJR : ((j : ℝ) + ((j₁ + 1 : ℕ) : ℝ)) = (J : ℝ) + 1 := by rw [hJ]; push_cast; ring
    rw [hJR]
    have hJ0 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
    have hsq : (nr J : ℝ) ^ 3 * Real.sqrt (W (Ns J)) ≤ 1 / ((J : ℝ) + 1) ^ 2 := by
      have e1 : (nr J : ℝ) ^ 3 * Real.sqrt (W (Ns J)) = Real.sqrt ((nr J : ℝ) ^ 6 * W (Ns J)) := by
        rw [Real.sqrt_mul (by positivity), show (nr J : ℝ) ^ 6 = ((nr J : ℝ) ^ 3) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      have e2 : Real.sqrt (1 / ((J : ℝ) + 1) ^ 4) = 1 / ((J : ℝ) + 1) ^ 2 := by
        rw [show 1 / ((J : ℝ) + 1) ^ 4 = (1 / ((J : ℝ) + 1) ^ 2) ^ 2 by rw [div_pow, one_pow, ← pow_mul],
          Real.sqrt_sq (by positivity)]
      rw [e1, ← e2]; exact Real.sqrt_le_sqrt hW6
    have hlev : 74016 * (nr J : ℝ) ^ 3 * Real.sqrt (κ * W (Ns J)) * Zc ≤
        74016 * Real.sqrt κ * Zc / ((J : ℝ) + 1) ^ 2 := by
      rw [Real.sqrt_mul hκ]
      have hZ := Zc_nonneg
      have hk := Real.sqrt_nonneg κ
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 74016 * Real.sqrt κ * Zc)
      rw [mul_one_div, le_div_iff₀ (by positivity)] at this
      nlinarith
    have hm := hmass J
    have hJ1R : ((J : ℝ) + 1) = (J : ℝ) + 1 := rfl
    calc _ ≤ 74016 * Real.sqrt κ * Zc / ((J : ℝ) + 1) ^ 2 + 1 / ((J : ℝ) + 1) ^ 2 :=
          add_le_add (hL.trans hlev) hm
      _ = B / ((J : ℝ) + 1) ^ 2 := by rw [hBdef]; ring
  have hnn : ∀ j, 0 ≤ dens bad d j [] := fun j => dens_nonneg j []
  obtain ⟨hs0, ht0⟩ := tsum_tail_le _ hnn B hB0.le 0 (j₁ + 1) (by omega) (fun j _ => hdj j)
  simp only [zero_le, if_true, Nat.cast_zero, zero_add] at hs0 ht0
  have hj₁pos : (0 : ℝ) < j₁ := by have : 0 < j₁ := by omega
                                   exact_mod_cast this
  have htot : ∑' j, dens bad d j [] ≤ 1 / 4 := by
    refine ht0.trans ?_
    push_cast
    rw [show (j₁ : ℝ) + 1 - 1 = j₁ by ring, div_le_div_iff₀ hj₁pos (by norm_num)]
    linarith
  set c : ℕ := ⌈B⌉₊ + 1 with hcdef
  have hcB : B ≤ (c : ℝ) := by rw [hcdef]; push_cast; linarith [Nat.le_ceil B]
  set J : ℕ → ℕ := fun k => c * 8 ^ (k + 1) with hJdef
  have hJp : Primrec J :=
    Primrec.nat_mul.comp (Primrec.const _) (primrec_pow.comp (Primrec.const 8) Primrec.succ)
  have htail : ∀ k, ∑' j, (if J k < j then dens bad d j [] else 0) ≤ (1 / 8 : ℝ) ^ (k + 1) := by
    intro k
    obtain ⟨_, ht⟩ := tsum_tail_le _ hnn B hB0.le (J k + 1) (j₁ + 1) (by omega) (fun j _ => hdj j)
    have e : (fun j => if J k < j then dens bad d j [] else 0) =
        fun j => if J k + 1 ≤ j then dens bad d j [] else 0 := by
      funext j; simp only [Nat.lt_iff_add_one_le]
    rw [e]
    refine ht.trans ?_
    have h8 : (0 : ℝ) < 8 ^ (k + 1) := by positivity
    have hJR : ((J k : ℕ) : ℝ) = c * 8 ^ (k + 1) := by simp [hJdef]
    have hden : (0 : ℝ) < ((J k + 1 : ℕ) : ℝ) + ((j₁ + 1 : ℕ) : ℝ) - 1 := by
      push_cast; rw [hJR]
      have : (0 : ℝ) ≤ c * 8 ^ (k + 1) := by positivity
      linarith
    rw [div_pow, one_pow, div_le_div_iff₀ hden h8]
    push_cast; rw [hJR]
    have : (1 : ℝ) ≤ 8 ^ (k + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨e, hce, hav⟩ := exists_primrec_avoid bad hbad d hd J hJp hs0 htot htail
  have hpass : ∀ J', j₁ ≤ J' → levelBad Ψ (nr J') (Ns J') (pre e (D1 J')) = 0 ∧
      bad' J' (pre e (d' J')) = false := by
    intro J' hJ'
    have h := hav (J' - j₁)
    simp only [hbaddef, hddef, Nat.sub_add_cancel hJ', Bool.or_eq_false_iff,
      decide_eq_false_iff_not, not_lt, Nat.le_zero] at h
    rw [pre_take' e (le_max_left _ _), pre_take' e (le_max_right _ _)] at h
    exact h
  refine ⟨e, hce, ?_, j₁, fun j hj => (hpass j hj).2⟩
  rw [isNormal_iff_equidistributed_orbit 2 le_rfl]
  refine equidistributed_of_badic 2 le_rfl _ fun ℓ hℓ v hv => ?_
  refine tendsto_div_of_monotone_of_exists_subseq_tendsto_div _ _
    (fun m n h => by exact_mod_cast visitCount_mono_n _ _ _ h) fun a ha =>
      ⟨Ns, hrat a ha, hNtop, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_one_div_atTop_nhds_zero_nat.comp hnrtop)
  filter_upwards [eventually_ge_atTop (max j₀ j₁), hnrtop.eventually_ge_atTop (2 ^ ℓ)] with J' hJ' hℓn
  obtain ⟨hn8, hnN, -⟩ := hj₀ J' (le_of_max_le_left hJ')
  obtain ⟨hlev, -⟩ := hpass J' (le_of_max_le_right hJ')
  obtain ⟨htop, hp⟩ := pass_of_levelBad_zero Ψ hlev
  have hℓle : ℓ ≤ nr J' := (Nat.lt_two_pow_self).le.trans hℓn
  have hax := (hAG e (D1 J')).1
  simp only [Real.norm_eq_abs, abs_abs, Function.comp]
  exact good_of_pass Ψ A hΨ le_rfl (by omega) (by omega) hℓle (G e) _ (hA0 _) hax
    (eta_le A (G e) _ hax (hAG e _).2) htop (hp ℓ hℓ hℓn v hv)

end NormalNumbers.SchedDerandomize
