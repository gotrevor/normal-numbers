/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyAtomFreq

/-!
# Entropy expedition — the scale bands

`certified_granule_exceeds_previous_scale` forbids *normality* of any concatenation of certified
granules.  What it does not forbid is convergence of the prefix frequencies **along a
subsequence of cutoffs** — at the end of each scale's contribution, where the history is
negligible and the new content is certified as a whole.

Reading a scale "as a whole" in position order requires the scales to occupy *ordered* bands.
They do not: scale `i`'s sampled positions start near `0`.  The fix is to drop, at each scale,
the windows below the previous scale's ceiling.  This module proves that this drops almost
nothing: the multiplier `d_α` is at most `gridDm`, which is `exp(logP₀Nat K) ≤ 2^{2·2^{21K²}}`,
while the sample range jumps from `X(K_i) = 2^{100·2^{m(K_i)}}` to `X(K_{i+1})` with
`2^{m(K_{i+1})} ≥ 2·2^{m(K_i)}` and `m(K) ≥ K³`.  So

    `6 · gridDm(K_{i+1}) · X(K_i)  <  X(K_{i+1})`,

i.e. the previous scale's entire position range, inflated by the largest possible multiplier, is
a vanishing part of the next scale's.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.PrimeLambert

/-- **`gridDm ≤ 2^{2·2^{21K²}}`**, from `log P₀ ≤ logP₀Nat K ≤ 2^{21K²}`. -/
lemma gridDm_le_two_pow {K : ℕ} (hK : 100 ≤ K) :
    gridDm K (N K) ≤ 2 ^ (2 * 2 ^ (21 * K ^ 2)) := by
  have h1 : gridDm K (N K) ≤ gridP₀Bound K (N K) := gridDm_le_gridP₀Bound K (N K) (by omega)
  have hpos : (0 : ℝ) < gridP₀Bound K (N K) := by
    have := gridDm_pos K (N K)
    exact_mod_cast (by omega : 0 < gridP₀Bound K (N K))
  have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp (logP₀Nat K) := by
    calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 (log_gridP₀Bound_le (by omega))
  have h3 : Real.exp (logP₀Nat K) ≤ (2 : ℝ) ^ (2 * logP₀Nat K) := exp_nat_le_two_pow _
  have h4 : (2 : ℝ) ^ (2 * logP₀Nat K) ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * K ^ 2)) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have := logP₀Nat_le_two_pow hK
    omega
  have h5 : (gridDm K (N K) : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * K ^ 2)) := by
    have hcast : (gridDm K (N K) : ℝ) ≤ (gridP₀Bound K (N K) : ℝ) := by exact_mod_cast h1
    linarith
  have : (gridDm K (N K) : ℝ) ≤ ((2 ^ (2 * 2 ^ (21 * K ^ 2)) : ℕ) : ℝ) := by
    push_cast
    exact h5
  exact_mod_cast this

/-- The exponent gap: `m(K_i) ≥ K_i³` already dwarfs `21·K_{i+1}² + 2`. -/
lemma exponent_gap (i : ℕ) :
    3 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i) < 100 * 2 ^ m (KK (i + 1)) := by
  have hK : 160000 ≤ KK i := KK_ge i
  have hsucc : KK (i + 1) = KK i + 4 := KK_succ i
  -- `m (KK i) ≥ KK i ³ ≥ 21·KK (i+1)² + 2`
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hbig : 21 * KK (i + 1) ^ 2 + 2 ≤ KK i ^ 3 := by
    rw [hsucc]
    nlinarith [hK]
  have hstep : 2 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := two_pow_m_step i
  have hmono : 2 ^ (21 * KK (i + 1) ^ 2 + 2) ≤ 2 ^ m (KK i) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (21 * KK (i + 1) ^ 2 + 2) = 4 * 2 ^ (21 * KK (i + 1) ^ 2) := by
    rw [pow_add]; ring
  have hone : 1 ≤ 2 ^ (21 * KK (i + 1) ^ 2) := Nat.one_le_two_pow
  omega

/-- The strengthened exponent gap, with room for the modulus term. -/
lemma exponent_gap_strong (i : ℕ) :
    4 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i) ≤ 99 * 2 ^ m (KK (i + 1)) := by
  have hK : 160000 ≤ KK i := KK_ge i
  have hsucc : KK (i + 1) = KK i + 4 := KK_succ i
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hbig : 21 * KK (i + 1) ^ 2 + 2 ≤ KK i ^ 3 := by
    rw [hsucc]
    nlinarith [hK]
  have hstep : 2 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := two_pow_m_step i
  have hmono : 2 ^ (21 * KK (i + 1) ^ 2 + 2) ≤ 2 ^ m (KK i) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ (21 * KK (i + 1) ^ 2 + 2) = 4 * 2 ^ (21 * KK (i + 1) ^ 2) := by
    rw [pow_add]; ring
  have hone : 1 ≤ 2 ^ (21 * KK (i + 1) ^ 2) := Nat.one_le_two_pow
  omega

/-- The modulus is tiny against the sample range. -/
lemma P₀_le_two_pow_band (i : ℕ) :
    ((gridAt (i + 1)).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m (KK (i + 1))) :=
  P₀_le_two_pow (show 100 ≤ KK (i + 1) by have := KK_ge (i + 1); omega)

/-- **The band gap.**  The previous scale's whole position range, inflated by the largest
multiplier the next scale's grid admits, is still a vanishing part of the next scale's range. -/
theorem band_gap (i : ℕ) :
    6 * gridDm (KK (i + 1)) (N (KK (i + 1))) * X (KK i) < X (KK (i + 1)) := by
  have hK1 : 100 ≤ KK (i + 1) := by have := KK_ge (i + 1); omega
  have hDm := gridDm_le_two_pow hK1
  have hX : ∀ j : ℕ, X (KK j) = 2 ^ (100 * 2 ^ m (KK j)) := fun _ => rfl
  have hgap := exponent_gap i
  calc 6 * gridDm (KK (i + 1)) (N (KK (i + 1))) * X (KK i)
      ≤ 2 ^ 3 * 2 ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) * 2 ^ (100 * 2 ^ m (KK i)) := by
        rw [hX i]
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ hDm)
        norm_num
    _ = 2 ^ (3 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i)) := by
        rw [← pow_add, ← pow_add]
    _ < 2 ^ (100 * 2 ^ m (KK (i + 1))) := Nat.pow_lt_pow_right (by norm_num) hgap
    _ = X (KK (i + 1)) := (hX (i + 1)).symm


/-! ### The band-gap inequality in the form the count consumes -/

set_option maxHeartbeats 1000000 in
/-- `12·gridDm(K_{i+1})·X(K_i) + 4·P₀_{i+1} ≤ X(K_{i+1})`. -/
theorem band_gap_strong (i : ℕ) :
    (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
        + 4 * ((gridAt (i + 1)).P₀ : ℝ)
      ≤ (X (KK (i + 1)) : ℝ) := by
  have hK1 : 100 ≤ KK (i + 1) := by have := KK_ge (i + 1); omega
  have hgap := exponent_gap_strong i
  have hstep := two_pow_m_step i
  have hXv : ∀ j : ℕ, ((X (KK j) : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m (KK j)) := by
    intro j
    show ((2 ^ (100 * 2 ^ m (KK j)) : ℕ) : ℝ) = _
    push_cast; ring
  -- first term
  have hA : (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
      ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := by
    have hDm : (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ)
        ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) := by
      have h := gridDm_le_two_pow hK1
      have : ((gridDm (KK (i + 1)) (N (KK (i + 1))) : ℕ) : ℝ)
          ≤ ((2 ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      exact this
    have h12 : (12 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) := by positivity
    calc (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) * (X (KK i) : ℝ)
        ≤ (2 : ℝ) ^ 4 * (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2))
            * (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by
          rw [hXv i]
          have hXpos : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by positivity
          have hDmpos : (0 : ℝ) ≤ (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ) :=
            Nat.cast_nonneg _
          have h1 : (12 : ℝ) * (gridDm (KK (i + 1)) (N (KK (i + 1))) : ℝ)
              ≤ (2 : ℝ) ^ 4 * (2 : ℝ) ^ (2 * 2 ^ (21 * KK (i + 1) ^ 2)) :=
            mul_le_mul h12 hDm hDmpos (by positivity)
          exact mul_le_mul_of_nonneg_right h1 hXpos
      _ = (2 : ℝ) ^ (4 + 2 * 2 ^ (21 * KK (i + 1) ^ 2) + 100 * 2 ^ m (KK i)) := by
          rw [← pow_add, ← pow_add]
      _ ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := pow_le_pow_right₀ (by norm_num) hgap
  -- second term
  have hB : 4 * ((gridAt (i + 1)).P₀ : ℝ) ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := by
    have hP := P₀_le_two_pow_band i
    have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    have hsum : 2 + 2 * 2 ^ m (KK (i + 1)) ≤ 99 * 2 ^ m (KK (i + 1)) := by
      have hone : 1 ≤ 2 ^ m (KK (i + 1)) := Nat.one_le_two_pow
      omega
    calc 4 * ((gridAt (i + 1)).P₀ : ℝ)
        ≤ (2 : ℝ) ^ 2 * (2 : ℝ) ^ (2 * 2 ^ m (KK (i + 1))) := by
          rw [← h4]
          exact mul_le_mul_of_nonneg_left hP (by norm_num)
      _ = (2 : ℝ) ^ (2 + 2 * 2 ^ m (KK (i + 1))) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) := pow_le_pow_right₀ (by norm_num) hsum
  have hfin : (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) + (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1)))
      ≤ (X (KK (i + 1)) : ℝ) := by
    rw [hXv (i + 1)]
    have h2 : (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1))) + (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1)))
        = (2 : ℝ) ^ (99 * 2 ^ m (KK (i + 1)) + 1) := by rw [pow_succ]; ring
    rw [h2]
    refine pow_le_pow_right₀ (by norm_num) ?_
    have hone : 1 ≤ 2 ^ m (KK (i + 1)) := Nat.one_le_two_pow
    omega
  linarith

end NormalNumbers.G4.Sched
