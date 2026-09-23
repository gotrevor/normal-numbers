/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PrimeModelFamilyGraded
import NormalNumbers.PrimeModelFamilyConsumer

/-!
# A double-exponential block criterion for `SqrtFreshMassZero`

Theorem C′ (`isNormal_subsetLambert_of_sqrtFreshMassZero`) asks that the *square-root fresh
reciprocal mass* `r_P(N) = ∑_{p ∈ P, √N < p ≤ N} 1/p` vanish.  In the `t = log log x`
coordinate used throughout Astra §10, the window `(√N, N]` has **constant** length
`log log N − log log √N = log 2`.  That is the structural reason the criterion is so permissive:
a prime set whose reciprocal mass is concentrated in bursts of vanishing `t`-width and vanishing
mass satisfies it, because a fixed-length `t`-window meets at most boundedly many bursts.

This module turns that observation into a checkable, entirely elementary criterion.  Put

    B_n = ( 2^{2^n}, 2^{2^{n+2}} ]      (`dblBlock`, a `t`-window of length `2 log 2`)

Every `(√N, N]` is contained in some `B_n` with `n = ⌊log₂ ⌊log₂ ⌊√N⌋⌋⌋ → ∞`: the double
logarithm of `√N` pins the block, and `N < (⌊√N⌋+1)²` lets the right end be squared once.
Hence `dblBlockMass P n → 0` already forces `SqrtFreshMassZero P`, and with `DivergentRecip P`
the Lambert constant `subsetLambert P 4` is normal in base 4.

This is exactly the hypothesis Astra §10 verifies for the prime-burst example (blocks starting
at `t_n = exp(n²)` of `t`-width `1/n` and mass `O(1/n)`, whose gaps dwarf any fixed window), so
Theorem C′ covers that example directly — the §10 consumer is not needed for it.
-/

open Finset Filter Topology
open scoped BigOperators

namespace NormalNumbers.PrimeModel.SqrtFresh

open NormalNumbers.G4Sparse NormalNumbers.PrimeModel.DensityMass
open NormalNumbers.PrimeLambert
open NormalNumbers.PrimeModel.FamilyIter

variable (P : ℕ → Prop) [DecidablePred P]

/-- The reciprocal mass of `P` in the double-exponential block `(2^{2^n}, 2^{2^{n+2}}]`. -/
noncomputable def dblBlockMass (n : ℕ) : ℝ :=
  recipSumIoc P (2 ^ 2 ^ n) (2 ^ 2 ^ (n + 2))

/-- The block index attached to `N`: `⌊log₂ ⌊log₂ ⌊√N⌋⌋⌋`. -/
noncomputable def dblIdx (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (Nat.sqrt N))

theorem dblIdx_mono : Monotone dblIdx := fun a b hab =>
  Nat.log_mono_right (Nat.log_mono_right (Nat.sqrt_le_sqrt hab))

theorem dblIdx_tendsto : Tendsto dblIdx atTop atTop := by
  refine tendsto_atTop_atTop.2 fun k => ⟨(2 ^ 2 ^ 2 ^ k) ^ 2, fun N hN => ?_⟩
  refine le_trans ?_ (dblIdx_mono hN)
  have hs : Nat.sqrt ((2 ^ 2 ^ 2 ^ k) ^ 2) = 2 ^ 2 ^ 2 ^ k := by
    exact Nat.sqrt_eq' _
  have hl1 : Nat.log 2 (2 ^ 2 ^ 2 ^ k) = 2 ^ 2 ^ k := Nat.log_pow (by norm_num) _
  have hl2 : Nat.log 2 (2 ^ 2 ^ k) = 2 ^ k := Nat.log_pow (by norm_num) _
  have : dblIdx ((2 ^ 2 ^ 2 ^ k) ^ 2) = 2 ^ k := by
    rw [dblIdx, hs, hl1, hl2]
  rw [this]
  exact Nat.le_of_lt (Nat.lt_two_pow_self)

/-- **The containment.**  For `N ≥ 16`, `(√N, N] ⊆ (2^{2^{n}}, 2^{2^{n+2}}]` with
`n = dblIdx N`. -/
theorem sqrt_window_subset {N : ℕ} (hN : 16 ≤ N) :
    2 ^ 2 ^ dblIdx N ≤ Nat.sqrt N ∧ N ≤ 2 ^ 2 ^ (dblIdx N + 2) := by
  set s : ℕ := Nat.sqrt N with hsdef
  have hs4 : 4 ≤ s := by
    have h1 : Nat.sqrt 16 ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN
    have h2 : Nat.sqrt 16 = 4 := by norm_num
    omega
  set m : ℕ := Nat.log 2 s with hmdef
  have hm2 : 2 ≤ m := by
    have : Nat.log 2 4 ≤ Nat.log 2 s := Nat.log_mono_right hs4
    have h4 : Nat.log 2 4 = 2 := by norm_num
    omega
  set n : ℕ := Nat.log 2 m with hndef
  -- lower end
  have hpm : 2 ^ n ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hms : 2 ^ m ≤ s := Nat.pow_log_le_self 2 (by omega)
  have hlow : 2 ^ 2 ^ n ≤ s := le_trans (Nat.pow_le_pow_right (by norm_num) hpm) hms
  -- upper end
  have hmlt : m < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hslt : s < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
  have hstep : (2 : ℕ) ^ (m + 1) ≤ 2 ^ 2 ^ (n + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hs1 : s + 1 ≤ 2 ^ 2 ^ (n + 1) := by omega
  have hNlt : N < (s + 1) * (s + 1) := by
    have := Nat.lt_succ_sqrt' N
    rw [pow_two] at this
    simpa [hsdef, Nat.succ_eq_add_one] using this
  have hsq : (2 : ℕ) ^ 2 ^ (n + 1) * 2 ^ 2 ^ (n + 1) = 2 ^ 2 ^ (n + 2) := by
    rw [← pow_add]
    congr 1
    rw [pow_succ, pow_succ]
    ring
  have hup : N ≤ 2 ^ 2 ^ (n + 2) := by
    have : (s + 1) * (s + 1) ≤ 2 ^ 2 ^ (n + 1) * 2 ^ 2 ^ (n + 1) :=
      Nat.mul_le_mul hs1 hs1
    omega
  exact ⟨hlow, hup⟩

/-- **The criterion.**  Vanishing double-exponential block mass forces `SqrtFreshMassZero`. -/
theorem sqrtFreshMassZero_of_dblBlockMass
    (h : Tendsto (dblBlockMass P) atTop (𝓝 0)) : SqrtFreshMassZero P := by
  rw [SqrtFreshMassZero]
  refine squeeze_zero' (Eventually.of_forall fun N => recipSumIoc_nonneg P _ _)
    (g := fun N : ℕ => dblBlockMass P (dblIdx N)) ?_ (h.comp dblIdx_tendsto)
  filter_upwards [eventually_ge_atTop 16] with N hN
  obtain ⟨hlow, hup⟩ := sqrt_window_subset hN
  calc recipSumIoc P (Nat.sqrt N) N
      ≤ recipSumIoc P (2 ^ 2 ^ dblIdx N) N := recipSumIoc_mono_left P hlow
    _ ≤ recipSumIoc P (2 ^ 2 ^ dblIdx N) (2 ^ 2 ^ (dblIdx N + 2)) := recipSumIoc_mono_right P hup
    _ = dblBlockMass P (dblIdx N) := rfl

/-! ### The converse: the criterion is an equivalence -/

/-- The block `(2^{2^n}, 2^{2^{n+2}}]` is exactly **two** root-chain steps wide, so its mass is
at most `2 ρ` whenever the square-root fresh mass is `≤ ρ` from `2^{2^n}` on. -/
theorem dblBlockMass_le_of_bound {ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ}
    (h : ∀ q, 2 ^ 2 ^ n ≤ q → recipSumIoc P (Nat.sqrt q) q ≤ ρ) :
    dblBlockMass P n ≤ 2 * ρ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hy2 : 2 ≤ (2 : ℕ) ^ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
  have hM : (2 : ℕ) ^ 2 ^ n < 2 ^ 2 ^ (n + 2) := by
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have key := recipSumIoc_le_rootChain P hρ hy2 (le_refl _) hM h
  -- the chain length is exactly `⌈log 4 / log 2⌉ = 2`
  have hlogy : Real.log ((2 ^ 2 ^ n : ℕ) : ℝ) = (2 ^ n : ℝ) * Real.log 2 := by
    push_cast [Real.log_pow]
    ring
  have hlogM : Real.log ((2 ^ 2 ^ (n + 2) : ℕ) : ℝ) = (2 ^ (n + 2) : ℝ) * Real.log 2 := by
    push_cast [Real.log_pow]
    ring
  have hratio : Real.log ((2 ^ 2 ^ (n + 2) : ℕ) : ℝ) / Real.log ((2 ^ 2 ^ n : ℕ) : ℝ) = 4 := by
    rw [hlogy, hlogM]
    have hp : (2 : ℝ) ^ (n + 2) = 4 * 2 ^ n := by ring
    rw [hp]
    field_simp
  have hceil : ⌈Real.log (Real.log ((2 ^ 2 ^ (n + 2) : ℕ) : ℝ)
      / Real.log ((2 ^ 2 ^ n : ℕ) : ℝ)) / Real.log 2⌉₊ = 2 := by
    rw [hratio]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h4, mul_div_assoc, div_self (ne_of_gt hlog2), mul_one]
    exact Nat.ceil_ofNat 2
  rw [dblBlockMass]
  calc recipSumIoc P (2 ^ 2 ^ n) (2 ^ 2 ^ (n + 2)) ≤ ρ * (⌈_⌉₊ : ℝ) := key
    _ = 2 * ρ := by rw [hceil]; push_cast; ring

/-- **The criterion is an equivalence.** -/
theorem dblBlockMass_tendsto_iff :
    Tendsto (dblBlockMass P) atTop (𝓝 0) ↔ SqrtFreshMassZero P := by
  refine ⟨sqrtFreshMassZero_of_dblBlockMass P, fun hS => ?_⟩
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((tendsto_order.1 hS).2 (ε / 4) (by linarith))
  have hTle : ∃ n₀ : ℕ, T ≤ 2 ^ 2 ^ n₀ := by
    refine ⟨T, le_trans (le_of_lt Nat.lt_two_pow_self) ?_⟩
    exact Nat.pow_le_pow_right (by norm_num) (le_of_lt Nat.lt_two_pow_self)
  obtain ⟨n₀, hn₀⟩ := hTle
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hmono : (2 : ℕ) ^ 2 ^ n₀ ≤ 2 ^ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hb := dblBlockMass_le_of_bound P (ρ := ε / 4) (by linarith)
    (n := n) (fun q hq => (hT q (by omega)).le)
  have hnn : 0 ≤ dblBlockMass P n := recipSumIoc_nonneg P _ _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith

/-- **Theorem C′ off the block criterion.** -/
theorem isNormal_subsetLambert_of_dblBlockMass
    (h : Tendsto (dblBlockMass P) atTop (𝓝 0)) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  NormalNumbers.PrimeModel.FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero P
    (sqrtFreshMassZero_of_dblBlockMass P h) hP

end NormalNumbers.PrimeModel.SqrtFresh
