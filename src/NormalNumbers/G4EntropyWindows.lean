/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyMixture

/-!
# Entropy expedition — the sampled windows at one atom are pairwise disjoint

Lap 60 left a structural probe open: *are maximal runs of `IsSampled` exactly single windows?*
This module settles the same-atom half, affirmatively and with a large margin.

At a fixed atom `α`, two distinct sample times `n < n'` of `P_K` differ by at least the
progression modulus `P₀`, and `n = t_α + d_α·kIdx n α`, so the orbit indices differ by at least
`P₀/d_α ≥ d_α·freezeQ ≥ freezeQ`.  And `freezeQ` exceeds the index count `|Idx| = (K²+1)^K·N`
(it is divisible by a prime above `|Idx|`, by Bertrand), which already exceeds the window
length `m_K`.  So the windows `[2·kIdx, 2·kIdx + m_K)` are separated by more than their own
length:

    `2·kIdx n α + m_K ≤ 2·kIdx n' α`.

Consequence: a run of sampled positions can only be produced by windows at **different**
atoms — so any overlap in `IsSampled` is a genuine cross-atom collision, and a disjoint
sub-family of windows can be chosen atom by atom without any loss.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- `freezeQ` is divisible by a prime above `|Idx|`, hence exceeds it. -/
lemma card_Idx_lt_freezeQ (G : GridParams) (hpos : 0 < Fintype.card G.Idx) :
    Fintype.card G.Idx < G.freezeQ := by
  have hne : Fintype.card G.Idx ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ hne
  have hdvd : p ∣ G.freezeQ := G.prime_dvd_freezeQ_of_le hp hle
  exact lt_of_lt_of_le hlt (Nat.le_of_dvd G.freezeQ_pos hdvd)

/-- The index count at scale `i`. -/
lemma card_Idx_gridAt (i : ℕ) :
    Fintype.card (gridAt i).Idx = (KK i ^ 2 + 1) ^ KK i * N (KK i) := by
  rw [show (gridAt i) = gridOf (KK i) (N (KK i)) (KK_one_le i) from rfl, gridOf.card_Idx]

lemma card_Idx_gridAt_pos (i : ℕ) : 0 < Fintype.card (gridAt i).Idx := by
  rw [card_Idx_gridAt]
  have h1 : 0 < (KK i ^ 2 + 1) ^ KK i := Nat.pow_pos (by omega)
  have h2 : 0 < N (KK i) := by
    have := KK_ge i
    unfold N
    nlinarith
  exact Nat.mul_pos h1 h2

/-- The window length is below the index count. -/
lemma kk_le_card_Idx (i : ℕ) : kk i ≤ Fintype.card (gridAt i).Idx := by
  rw [card_Idx_gridAt]
  have h1 : 1 ≤ (KK i ^ 2 + 1) ^ KK i := Nat.one_le_pow _ _ (by omega)
  have h2 : kk i ≤ N (KK i) := by
    unfold N KK kk
    nlinarith [Nat.zero_le i]
  calc kk i ≤ N (KK i) := h2
    _ = 1 * N (KK i) := (one_mul _).symm
    _ ≤ (KK i ^ 2 + 1) ^ KK i * N (KK i) := Nat.mul_le_mul_right _ h1

/-- **Distinct sample times are `P₀` apart.** -/
lemma P₀_le_sub_of_mem (i : ℕ) {n n' : ℕ} (hn : n ∈ PK i) (hn' : n' ∈ PK i) (hlt : n < n') :
    (gridAt i).P₀ ≤ n' - n := by
  have h1 : n % (gridAt i).P₀ = (gridAt i).b₀ := (Finset.mem_filter.1 hn).2
  have h2 : n' % (gridAt i).P₀ = (gridAt i).b₀ := (Finset.mem_filter.1 hn').2
  have hdvd : (gridAt i).P₀ ∣ n' - n := by
    have : n ≡ n' [MOD (gridAt i).P₀] := by
      unfold Nat.ModEq
      rw [h1, h2]
    exact (Nat.modEq_iff_dvd' (le_of_lt hlt)).1 this
  exact Nat.le_of_dvd (by omega) hdvd

/-- **The windows at one atom are pairwise disjoint**, with a margin: consecutive sample times
push the orbit index by more than the window length. -/
theorem window_gap_same_atom (i : ℕ) (α : (gridAt i).Atom) {n n' : ℕ}
    (hn : n ∈ PK i) (hn' : n' ∈ PK i) (hlt : n < n') :
    2 * kIdx (gridAt i) n α + kk i ≤ 2 * kIdx (gridAt i) n' α := by
  have hd : 0 < (gridAt i).d α := (gridAt i).d_pos α
  obtain ⟨hk, -⟩ := kIdx_spec (gridAt i) (X := X (KK i)) hn α
  obtain ⟨hk', -⟩ := kIdx_spec (gridAt i) (X := X (KK i)) hn' α
  have hkle : kIdx (gridAt i) n α ≤ kIdx (gridAt i) n' α := by
    by_contra hcon
    push_neg at hcon
    have hmul : (gridAt i).d α * kIdx (gridAt i) n' α
        < (gridAt i).d α * kIdx (gridAt i) n α := (Nat.mul_lt_mul_left hd).mpr hcon
    omega
  have hsub : (gridAt i).d α * (kIdx (gridAt i) n' α - kIdx (gridAt i) n α) = n' - n := by
    rw [Nat.mul_sub]
    omega
  have hP₀ := P₀_le_sub_of_mem i hn hn' hlt
  have hMprod : (gridAt i).d α ^ 2 ≤ (gridAt i).Mprod :=
    Nat.le_of_dvd (gridAt i).Mprod_pos ((gridAt i).sq_d_dvd_Mprod α)
  have hP₀ge : (gridAt i).d α * (gridAt i).freezeQ ≤ (gridAt i).P₀ := by
    have h1 : (gridAt i).d α * (gridAt i).freezeQ
        ≤ (gridAt i).d α ^ 2 * (gridAt i).freezeQ := by
      have hsq : (gridAt i).d α ≤ (gridAt i).d α ^ 2 := Nat.le_self_pow (by norm_num) _
      exact Nat.mul_le_mul_right _ hsq
    calc (gridAt i).d α * (gridAt i).freezeQ
        ≤ (gridAt i).d α ^ 2 * (gridAt i).freezeQ := h1
      _ ≤ (gridAt i).Mprod * (gridAt i).freezeQ := Nat.mul_le_mul_right _ hMprod
      _ = (gridAt i).P₀ := rfl
  have hfq : kk i < (gridAt i).freezeQ :=
    lt_of_le_of_lt (kk_le_card_Idx i) (card_Idx_lt_freezeQ (gridAt i) (card_Idx_gridAt_pos i))
  have hgap : (gridAt i).d α * kk i
      ≤ (gridAt i).d α * (kIdx (gridAt i) n' α - kIdx (gridAt i) n α) := by
    rw [hsub]
    refine le_trans ?_ hP₀
    refine le_trans ?_ hP₀ge
    exact Nat.mul_le_mul_left _ (le_of_lt hfq)
  have hgap' : kk i ≤ kIdx (gridAt i) n' α - kIdx (gridAt i) n α :=
    le_of_mul_le_mul_left hgap hd
  omega

end NormalNumbers.G4.Sched
