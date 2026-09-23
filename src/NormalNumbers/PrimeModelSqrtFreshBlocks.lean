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

/-- **Theorem C′ off the block criterion.** -/
theorem isNormal_subsetLambert_of_dblBlockMass
    (h : Tendsto (dblBlockMass P) atTop (𝓝 0)) (hP : DivergentRecip P) :
    IsNormal 4 (subsetLambert P 4) :=
  NormalNumbers.PrimeModel.FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero P
    (sqrtFreshMassZero_of_dblBlockMass P h) hP

end NormalNumbers.PrimeModel.SqrtFresh
