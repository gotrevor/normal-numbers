/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBandTrunc

/-!
# The band floor raised to the **certificate floor**: a read with no uncertified head

The wall that blocked `IsNormal 2 fullReal` was the *head of each band*: a mid-band position
cutoff selects the truncated sample `n ≤ X'`, and `G4EntropyBandTrunc` certifies that truncation
only for `X' ≥ Xlo (KK i)`.  Band `i`'s own sample times start at `gridDm·bandLo i ≈
2·gridDm·X (KK (i−1))`, which is *far below* `Xlo (KK i) = 2^{50·2^{m (KK i)}}` (tower gap), so a
positive — indeed dominant — initial stretch of every band was uncertified, and the trivial
bound could not absorb it because band `i` dwarfs everything before it.

**`bandLo` is a free design parameter.**  Raising it to `bandLoH i := 2·Xlo (KK i)` deletes the
head entirely: every sample time of the raised band satisfies `n ≥ gridDm·2·Xlo (KK i) ≥
Xlo (KK i)`, so *every* mid-band truncation `X'` is above the certificate floor and
`G4EntropyBandTrunc`'s chain applies at it.

Nothing is lost:

* the raised band still keeps **at least half** the sample (`card_bandTH_ge`), because
  `X (KK i) = Xlo (KK i)²` — the dropped stretch is the square root of the range, and the gate
  `8·gridDm·Xlo + 4P₀ ≤ X` has `2^{49·2^{m}}` to spare (`head_gate`);
* the raised floor is still **above the previous band's ceiling**
  (`bandTop_le_bandLoH`), which is what makes the read strictly increasing: `bandTop i =
  2X (KK i) + kk i` has exponent `100·2^{m (KK i)}` while `bandLoH (i+1)` has
  `50·2^{m (KK (i+1))} ≥ 6400·2^{m (KK i)}`.

The cost is a *gap in positions* between `bandTop i` and `bandLoH (i+1)` that the read skips.
That is harmless: the read is a subsequence of `G₄`'s digits either way, and
`G4EntropyFullDensity.tendsto_density_fullPos` already records that the visited set has density
zero.

This module builds the raised band and its two structural facts; the read itself is assembled
downstream.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The raised floor -/

/-- The raised band floor: twice the level-`i` certificate floor. -/
noncomputable def bandLoH (i : ℕ) : ℕ := 2 * Xlo (KK i)

open Classical in
/-- The band-`i` sample times above the **raised** floor. -/
noncomputable def bandTH (i : ℕ) : Finset ℕ :=
  (PK i).filter (fun n => gridDm (KK i) (N (KK i)) * bandLoH i ≤ n)

lemma bandTH_subset (i : ℕ) : bandTH i ⊆ PK i := Finset.filter_subset _ _

/-- **Every sample time of the raised band is above the certificate floor.**  This is the whole
point: the truncated-scale chain of `G4EntropyBandTrunc` applies at every mid-band cutoff. -/
theorem Xlo_le_of_mem_bandTH (i : ℕ) {n : ℕ} (hn : n ∈ bandTH i) : Xlo (KK i) ≤ n := by
  classical
  have hmem : gridDm (KK i) (N (KK i)) * bandLoH i ≤ n := (Finset.mem_filter.1 hn).2
  have hDm : 1 ≤ gridDm (KK i) (N (KK i)) := gridDm_pos _ _
  have : bandLoH i ≤ gridDm (KK i) (N (KK i)) * bandLoH i :=
    Nat.le_mul_of_pos_left _ hDm
  have hb : bandLoH i = 2 * Xlo (KK i) := rfl
  omega

/-- **The raised floor still puts every atom's window above it.**  Copy of
`bandLo_le_pos_of_mem_bandT` at the raised threshold. -/
theorem bandLoH_le_pos_of_mem_bandTH (i : ℕ) {n : ℕ} (hn : n ∈ bandTH i)
    (α : (gridAt i).Atom) : bandLoH i ≤ 2 * kIdx (gridAt i) n α := by
  classical
  have hmem : gridDm (KK i) (N (KK i)) * bandLoH i ≤ n := (Finset.mem_filter.1 hn).2
  have hnPK : n ∈ PK i := (Finset.mem_filter.1 hn).1
  obtain ⟨hk, -⟩ := kIdx_spec (gridAt i) (X := X (KK i)) hnPK α
  have hd : (gridAt i).d α ≤ gridDm (KK i) (N (KK i)) :=
    gridOf.d_le (K := KK i) (N := N (KK i)) (hK := KK_one_le i) α
  have hdpos : 0 < (gridAt i).d α := (gridAt i).d_pos α
  have ht : (gridAt i).t α < (gridAt i).d α := (gridAt i).t_lt_d α
  have hmono : (gridAt i).d α * bandLoH i ≤ gridDm (KK i) (N (KK i)) * bandLoH i :=
    Nat.mul_le_mul_right _ hd
  have h1 : (gridAt i).d α * bandLoH i ≤ n := le_trans hmono hmem
  have h2 : n < (gridAt i).d α * (kIdx (gridAt i) n α + 1) := by
    have hexp : (gridAt i).d α * (kIdx (gridAt i) n α + 1)
        = (gridAt i).d α * kIdx (gridAt i) n α + (gridAt i).d α := by ring
    omega
  have hstrict : (gridAt i).d α * bandLoH i
      < (gridAt i).d α * (kIdx (gridAt i) n α + 1) := by omega
  have hlt : bandLoH i < kIdx (gridAt i) n α + 1 :=
    lt_of_mul_lt_mul_left hstrict (Nat.zero_le _)
  omega

/-! ### The raised floor clears the previous band's ceiling -/

/-- `2·X (KK i) + kk i ≤ 2·Xlo (KK (i+1))`: the raised floor of band `i+1` is still above
band `i`'s ceiling, so the bands' position ranges stay ordered. -/
theorem bandTop_le_bandLoH (i : ℕ) : bandTop i ≤ bandLoH (i + 1) := by
  have hstep := m_step_seven i
  have hone : (1 : ℕ) ≤ 2 ^ m (KK i) := Nat.one_le_two_pow
  have h128 : (2 : ℕ) ^ 7 * 2 ^ m (KK i) ≤ 2 ^ m (KK (i + 1)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h27 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hkk := kk_succ_le_X i
  have hexp : 100 * 2 ^ m (KK i) + 2 ≤ 50 * 2 ^ m (KK (i + 1)) := by omega
  have hX : X (KK i) = 2 ^ (100 * 2 ^ m (KK i)) := rfl
  have hXlo : Xlo (KK (i + 1)) = 2 ^ (50 * 2 ^ m (KK (i + 1))) := by
    show (2 ^ (2 ^ m (KK (i + 1)))) ^ 50 = _
    rw [← pow_mul]; ring_nf
  have hmain : 4 * X (KK i) ≤ Xlo (KK (i + 1)) := by
    rw [hX, hXlo, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbt : bandTop i = 2 * X (KK i) + kk i := rfl
  have hbl : bandLoH (i + 1) = 2 * Xlo (KK (i + 1)) := rfl
  omega

/-! ### The raised band still keeps half the sample -/

/-- **The head gate.**  `8·gridDm·Xlo (KK i) + 4·P₀ ≤ X (KK i)` — the dropped stretch is
essentially `√(X (KK i))`, with `2^{49·2^{m}}` to spare. -/
theorem head_gate (i : ℕ) :
    (8 : ℝ) * (gridDm (KK i) (N (KK i)) : ℝ) * (Xlo (KK i) : ℝ)
        + 4 * ((gridAt i).P₀ : ℝ)
      ≤ (X (KK i) : ℝ) := by
  have hK1 : 100 ≤ KK i := KK_hundred i
  have hcube : KK i ^ 3 ≤ m (KK i) := by
    have h1 := m₁_ge_cube (show 1 ≤ KK i by omega)
    unfold m
    omega
  have hKK : 160000 ≤ KK i := KK_ge i
  have honeM : (1 : ℕ) ≤ 2 ^ m (KK i) := Nat.one_le_two_pow
  have hsmall : 2 * 2 ^ (21 * KK i ^ 2) + 3 ≤ 49 * 2 ^ m (KK i) := by
    have hbig : 21 * KK i ^ 2 + 1 ≤ KK i ^ 3 := by nlinarith
    have h2 : (2 : ℕ) ^ (21 * KK i ^ 2 + 1) ≤ 2 ^ m (KK i) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (2 : ℕ) ^ (21 * KK i ^ 2 + 1) = 2 * 2 ^ (21 * KK i ^ 2) := by
      rw [pow_succ]; ring
    omega
  have hXv : ((X (KK i) : ℕ) : ℝ) = (2 : ℝ) ^ (100 * 2 ^ m (KK i)) := by
    show ((2 ^ (100 * 2 ^ m (KK i)) : ℕ) : ℝ) = _
    push_cast; ring
  have hXlov : ((Xlo (KK i) : ℕ) : ℝ) = (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := Xlo_cast (KK i)
  have hone : (1 : ℕ) ≤ 2 ^ m (KK i) := Nat.one_le_two_pow
  -- the first term
  have hA : (8 : ℝ) * (gridDm (KK i) (N (KK i)) : ℝ) * (Xlo (KK i) : ℝ)
      ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK i)) := by
    have hDm : (gridDm (KK i) (N (KK i)) : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ (21 * KK i ^ 2)) := by
      have h := gridDm_le_two_pow hK1
      have h' : ((gridDm (KK i) (N (KK i)) : ℕ) : ℝ)
          ≤ ((2 ^ (2 * 2 ^ (21 * KK i ^ 2)) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
    calc (8 : ℝ) * (gridDm (KK i) (N (KK i)) : ℝ) * (Xlo (KK i) : ℝ)
        ≤ (2 : ℝ) ^ 3 * (2 : ℝ) ^ (2 * 2 ^ (21 * KK i ^ 2)) * (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := by
          rw [hXlov, h8]
          have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (50 * 2 ^ m (KK i)) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDm (by positivity)) hp
      _ = (2 : ℝ) ^ (3 + 2 * 2 ^ (21 * KK i ^ 2) + 50 * 2 ^ m (KK i)) := by
          rw [← pow_add, ← pow_add]
      _ ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK i)) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- the second term
  have hB : 4 * ((gridAt i).P₀ : ℝ) ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK i)) := by
    have hP : ((gridAt i).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m (KK i)) := P₀_le_two_pow hK1
    calc 4 * ((gridAt i).P₀ : ℝ) ≤ (2 : ℝ) ^ 2 * (2 : ℝ) ^ (2 * 2 ^ m (KK i)) := by
          have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [this]
          exact mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (2 : ℝ) ^ (2 + 2 * 2 ^ m (KK i)) := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ (99 * 2 ^ m (KK i)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum : (2 : ℝ) ^ (99 * 2 ^ m (KK i)) + (2 : ℝ) ^ (99 * 2 ^ m (KK i))
      ≤ (X (KK i) : ℝ) := by
    rw [hXv]
    have he : (2 : ℝ) ^ (99 * 2 ^ m (KK i)) + (2 : ℝ) ^ (99 * 2 ^ m (KK i))
        = (2 : ℝ) ^ (99 * 2 ^ m (KK i) + 1) := by rw [pow_succ]; ring
    rw [he]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The raised band keeps at least half the sample.**  `card_bandT_ge`'s count with the
dropped stretch `n < gridDm·2·Xlo (KK i)` in place of `n < 3·gridDm·X (KK (i−1))`; `head_gate`
is the gate. -/
theorem card_bandTH_ge (i : ℕ) : ((PK i).card : ℝ) ≤ 2 * ((bandTH i).card : ℝ) := by
  classical
  set Dm : ℕ := gridDm (KK i) (N (KK i)) with hDm
  set M : ℕ := Dm * bandLoH i with hM
  have hP₀pos : 0 < (gridAt i).P₀ := (gridAt i).P₀_pos
  have hP₀R : (0 : ℝ) < ((gridAt i).P₀ : ℝ) := by exact_mod_cast hP₀pos
  have hdrop : (PK i).filter (fun n => ¬ Dm * bandLoH i ≤ n)
      ⊆ (PK i).filter (fun n => n < M) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, by have := hn.2; rw [hM]; omega⟩
  have hcount : (((PK i).filter (fun n => n < M)).card : ℝ)
      ≤ (M : ℝ) / ((gridAt i).P₀ : ℝ) + 1 := by
    have h := card_filter_lt_apSample_le (X (KK i)) (gridAt i).P₀ (gridAt i).b₀ M hP₀pos
    have hR : ((((PK i).filter (fun n => n < M)).card : ℕ) : ℝ)
        ≤ ((M / (gridAt i).P₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    refine hR.trans ?_
    push_cast
    have : ((M / (gridAt i).P₀ : ℕ) : ℝ) ≤ (M : ℝ) / ((gridAt i).P₀ : ℝ) := Nat.cast_div_le
    linarith
  have hbig : (X (KK i) : ℝ) / (2 * ((gridAt i).P₀ : ℝ)) ≤ ((PK i).card : ℝ) :=
    card_apSample_ge_half (X (KK i)) (gridAt i).P₀ (gridAt i).b₀ hP₀pos (gridAt i).b₀_lt_P₀
      (two_mul_P₀_le_X (KK_hundred i))
  have hMR : (M : ℝ) = 2 * (Dm : ℝ) * (Xlo (KK i) : ℝ) := by
    rw [hM, show bandLoH i = 2 * Xlo (KK i) from rfl]
    push_cast; ring
  have hhalf : 2 * ((M : ℝ) / ((gridAt i).P₀ : ℝ) + 1) ≤ ((PK i).card : ℝ) := by
    refine le_trans ?_ hbig
    rw [le_div_iff₀ (show (0:ℝ) < 2 * ((gridAt i).P₀ : ℝ) by linarith)]
    have hexp : 2 * ((M : ℝ) / ((gridAt i).P₀ : ℝ) + 1) * (2 * ((gridAt i).P₀ : ℝ))
        = 4 * (M : ℝ) + 4 * ((gridAt i).P₀ : ℝ) := by
      field_simp
      ring
    rw [hexp, hMR]
    linarith [head_gate i]
  have hsplit : ((PK i).card : ℝ)
      = ((bandTH i).card : ℝ)
        + (((PK i).filter (fun n => ¬ Dm * bandLoH i ≤ n)).card : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := PK i) (p := fun n => Dm * bandLoH i ≤ n)
    have hb : bandTH i = (PK i).filter (fun n => Dm * bandLoH i ≤ n) := rfl
    rw [hb, ← h]
    push_cast
    ring
  have hdropR : ((((PK i).filter (fun n => ¬ Dm * bandLoH i ≤ n)).card : ℕ) : ℝ)
      ≤ (((PK i).filter (fun n => n < M)).card : ℝ) :=
    Nat.cast_le.2 (Finset.card_le_card hdrop)
  linarith

lemma bandTH_nonempty (i : ℕ) : (bandTH i).Nonempty := by
  classical
  rw [← Finset.card_pos]
  have h := card_bandTH_ge i
  have hP : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have : (0 : ℝ) < ((bandTH i).card : ℝ) := by linarith
  exact_mod_cast this

end NormalNumbers.G4.Sched
