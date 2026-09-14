/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyGoodAtoms
import NormalNumbers.G4ScheduleFar

/-!
# Entropy expedition — the granularity wall between consecutive scales

`chunks_insufficient` (lap 54) refutes the chunking route using the *atom* count.  The atom
count is not the real obstruction: `G4EntropyGoodAtoms.card_good_ge` shows that the certifiable
granule can be taken as small as **one atom**, because a good atom's own window law carries its
own deficit.  Restricting instead in the *sample-time* direction has the same shape — a
sub-range of `P_K` of relative size `σ` inflates the deficit to `≈ (δ+1)/σ`, so `σ ≳ 1/m_K`
and a certified granule reads at least `|P_K|` digits (at least `|P_K|/m_K` sample times, each
contributing an `m_K`-bit window).

So the smallest digit count any certified granule at scale `i+1` can have is `≈ |P_{K_{i+1}}|`.
This module proves that this minimum already **exceeds everything scale `i` produces**:

    `|Atom_i| · |P_{K_i}| · m_i  <  |P_{K_{i+1}}|`.

The cause is not the atoms at all: `X(K) = 2^{100·2^{m(K)}}` with `m(K) ≥ K³`, so the number of
sample times jumps by a doubly exponential factor between consecutive scales, while the atom
count contributes only `2^{K³+K}`.

**Consequence.**  Any construction that reads `G₄`'s sampled digits in position order as a
concatenation of *certified* granules has, at the first granule of scale `i+1`, already made
everything read before it negligible.  The prefix frequencies therefore cannot converge, for
*any* choice of granules — this closes the whole family of routes, not just the chunking of
`chunks_insufficient`.  It is a statement about this mechanism's schedule, not about the
existence of a normal number read off `G₄`.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The schedule parameter `m` grows between consecutive scales -/

lemma m₁_lt_m₁_add_four {K : ℕ} (hK : 1 ≤ K) : m₁ K < m₁ (K + 4) := by
  have h1 : (8 : ℕ) ^ K < 8 ^ (K + 4) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : K ^ (2 * K + 1) ≤ (K + 4) ^ (2 * (K + 4) + 1) :=
    le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
  have hpos : 0 < (K + 4) ^ (2 * (K + 4) + 1) := Nat.pow_pos (by omega)
  unfold m₁
  calc 1000 * 8 ^ K * K ^ (2 * K + 1)
      ≤ 1000 * 8 ^ K * (K + 4) ^ (2 * (K + 4) + 1) := by
        exact Nat.mul_le_mul_left _ h2
    _ < 1000 * 8 ^ (K + 4) * (K + 4) ^ (2 * (K + 4) + 1) := by
        exact (Nat.mul_lt_mul_right hpos).2 (by omega)

lemma m_lt_m_add_four {K : ℕ} (hK : 1 ≤ K) : m K < m (K + 4) := by
  have h1 := m₁_lt_m₁_add_four hK
  have h2 : m₂ K ≤ m₂ (K + 4) := by
    unfold m₂
    have : K ^ 2 ≤ (K + 4) ^ 2 := Nat.pow_le_pow_left (by omega) _
    omega
  unfold m
  omega

lemma KK_succ (i : ℕ) : KK (i + 1) = KK i + 4 := by unfold KK kk; omega

lemma two_pow_m_step (i : ℕ) : 2 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := by
  have h : m (KK i) < m (KK (i + 1)) := by
    rw [KK_succ]
    exact m_lt_m_add_four (by have := KK_ge i; omega)
  calc 2 * 2 ^ m (KK i) = 2 ^ (m (KK i) + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ m (KK (i + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The two sides -/

/-- The scale-`i` sample is contained in `[0, X_K)`. -/
lemma card_PK_le (i : ℕ) : (PK i).card ≤ X (KK i) := by
  have : PK i ⊆ Finset.range (X (KK i)) := by
    intro n hn
    exact (Finset.mem_filter.1 hn).1
  simpa using Finset.card_le_card this

/-- The atom count is at most `2^{K³+K}`. -/
lemma card_Atom_le_two_pow (i : ℕ) :
    Fintype.card (gridAt i).Atom ≤ 2 ^ (KK i ^ 3 + KK i) := by
  rw [card_Atom_gridAt]
  have hb : KK i ^ 2 + 1 ≤ 2 ^ (KK i ^ 2 + 1) := le_of_lt (Nat.lt_two_pow_self)
  calc (KK i ^ 2 + 1) ^ KK i ≤ (2 ^ (KK i ^ 2 + 1)) ^ KK i := Nat.pow_le_pow_left hb _
    _ = 2 ^ ((KK i ^ 2 + 1) * KK i) := by rw [← pow_mul]
    _ = 2 ^ (KK i ^ 3 + KK i) := by ring_nf

/-- The whole digit output of scale `i` is at most `2^{K³ + 2K + 100·2^{m}}`. -/
lemma total_scale_le (i : ℕ) :
    (Fintype.card (gridAt i).Atom) * (PK i).card * kk i
      ≤ 2 ^ (KK i ^ 3 + 2 * KK i + 100 * 2 ^ m (KK i)) := by
  have h1 := card_Atom_le_two_pow i
  have h2 := card_PK_le i
  have h3 : kk i ≤ 2 ^ KK i := by
    have hk : kk i ≤ KK i := by unfold KK; omega
    exact hk.trans (le_of_lt Nat.lt_two_pow_self)
  have hX : X (KK i) = 2 ^ (100 * 2 ^ m (KK i)) := rfl
  calc (Fintype.card (gridAt i).Atom) * (PK i).card * kk i
      ≤ 2 ^ (KK i ^ 3 + KK i) * X (KK i) * 2 ^ KK i := by
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = 2 ^ ((KK i ^ 3 + KK i) + 100 * 2 ^ m (KK i) + KK i) := by
        rw [hX, ← pow_add, ← pow_add]
    _ = 2 ^ (KK i ^ 3 + 2 * KK i + 100 * 2 ^ m (KK i)) := by ring_nf

/-- **The scale-`i` sample is huge**: `|P_K| ≥ 2^{98·2^m}/2`, because `X = 2^{100·2^m}` and
`P₀ ≤ 2^{2·2^m}`. -/
lemma card_PK_ge (i : ℕ) :
    (2 : ℝ) ^ (98 * 2 ^ m (KK i)) / 2 ≤ ((PK i).card : ℝ) := by
  have hK100 : 100 ≤ KK i := by have := KK_ge i; omega
  have hhalf := card_apSample_ge_half (X (KK i)) (gridAt i).P₀ (gridAt i).b₀
    (gridAt i).P₀_pos (gridAt i).b₀_lt_P₀ (two_mul_P₀_le_X hK100)
  have hP₀ : ((gridAt i).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m (KK i)) := P₀_le_two_pow hK100
  have hP₀pos : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by
    have := (gridAt i).P₀_pos
    exact_mod_cast this
  have hXval : ((X (KK i) : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by
    show ((2 ^ (100 * 2 ^ m (KK i)) : ℕ) : ℝ) = _
    push_cast
    ring
  refine le_trans ?_ hhalf
  rw [hXval]
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have hsplit : (2 : ℝ) ^ (100 * 2 ^ m (KK i))
      = (2 : ℝ) ^ (98 * 2 ^ m (KK i)) * (2 : ℝ) ^ (2 * 2 ^ m (KK i)) := by
    rw [← pow_add]
    ring_nf
  rw [hsplit]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (98 * 2 ^ m (KK i)) := by positivity
  nlinarith [hP₀, hpos]

/-- **The granularity wall.**  Everything the scale-`i` sample produces — every atom, every
sample time, every digit of every window — is smaller than the number of sample times at scale
`i+1`, hence smaller than the **smallest certified granule** the next scale admits.

So a construction that reads sampled digits in position order as a concatenation of certified
granules cannot keep its prefix frequencies converging: the first granule of scale `i+1`
already dominates everything before it.  (An obstruction to the route, not a proof that no
normal number can be read off `G₄`'s sampled digits.) -/
theorem granule_exceeds_previous_scale (i : ℕ) :
    (Fintype.card (gridAt i).Atom : ℝ) * ((PK i).card : ℝ) * (kk i : ℝ)
      < ((PK (i + 1)).card : ℝ) := by
  set E : ℕ := KK i ^ 3 + 2 * KK i + 100 * 2 ^ m (KK i) with hE
  have hLHS : (Fintype.card (gridAt i).Atom : ℝ) * ((PK i).card : ℝ) * (kk i : ℝ)
      ≤ (2 : ℝ) ^ E := by
    have h := total_scale_le i
    have : ((Fintype.card (gridAt i).Atom * (PK i).card * kk i : ℕ) : ℝ) ≤ ((2 ^ E : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    linarith
  -- the exponent gap
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by have := KK_ge i; omega)
    unfold m
    omega
  have hlt : m (KK i) < 2 ^ m (KK i) := Nat.lt_two_pow_self
  have hKcube : KK i ≤ KK i ^ 3 := Nat.le_self_pow (by norm_num) _
  have hgap : E + 1 < 196 * 2 ^ m (KK i) := by
    rw [hE]; omega
  have hstep := two_pow_m_step i
  have hRHS : (2 : ℝ) ^ (196 * 2 ^ m (KK i)) / 2 ≤ ((PK (i + 1)).card : ℝ) := by
    refine le_trans ?_ (card_PK_ge (i + 1))
    have hexp : 196 * 2 ^ m (KK i) ≤ 98 * 2 ^ m (KK (i + 1)) := by omega
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hexp
    linarith
  have hmid : (2 : ℝ) ^ E < (2 : ℝ) ^ (196 * 2 ^ m (KK i)) / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have h2 : (2 : ℝ) ^ E * 2 = (2 : ℝ) ^ (E + 1) := by rw [pow_succ]
    rw [h2]
    exact pow_lt_pow_right₀ (by norm_num) hgap
  linarith

end NormalNumbers.G4.Sched
