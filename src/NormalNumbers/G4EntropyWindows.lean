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

/-! ### Cross-atom windows at the *same* sample time -/

/-- `d_α ≡ 1 (mod Q)`. -/
lemma d_mod_Q (G : GridParams) (α : G.Atom) : G.d α % G.Q = 1 :=
  mult_mod_Q G.B G.Q G.D₀ G.hQ α

/-- `t_α ≡ 0 (mod Q)`. -/
lemma t_mod_Q (G : GridParams) (α : G.Atom) : G.t α % G.Q = 0 := by
  show offset G.B G.Q α % G.Q = 0
  unfold offset
  exact Nat.mul_mod_right _ _

/-- **Every atom's orbit index is congruent to the sample time modulo `Q`.**  `t_α ≡ 0` and
`d_α ≡ 1` mod `Q`, so `n = t_α + d_α·k` gives `k ≡ n`. -/
lemma kIdx_mod_Q (G : GridParams) {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    kIdx G n α % G.Q = n % G.Q := by
  obtain ⟨hk, -⟩ := kIdx_spec G hn α
  have hd := d_mod_Q G α
  have ht := t_mod_Q G α
  conv_rhs => rw [hk]
  rw [Nat.add_mod, ht, Nat.mul_mod, hd, one_mul, Nat.mod_mod_of_dvd _ dvd_rfl]
  simp

/-- **At one sample time, distinct orbit indices are `Q` apart.**  So the windows of two
different atoms at the *same* sample time either coincide or are disjoint with an enormous
margin: any cross-atom collision must involve two *different* sample times. -/
theorem window_gap_same_time (i : ℕ) {n : ℕ} (hn : n ∈ PK i) (α β : (gridAt i).Atom)
    (hne : kIdx (gridAt i) n α < kIdx (gridAt i) n β) :
    2 * kIdx (gridAt i) n α + kk i ≤ 2 * kIdx (gridAt i) n β := by
  have hα := kIdx_mod_Q (gridAt i) hn α
  have hβ := kIdx_mod_Q (gridAt i) hn β
  have hQ : kk i < (gridAt i).Q := by
    have hgt : gridUmax (KK i) (N (KK i)) + KK i + N (KK i) + 2
        ≤ gridQ (KK i) (N (KK i)) := gridQ_gt _ _
    have hQeq : (gridAt i).Q = gridQ (KK i) (N (KK i)) := rfl
    have hkkK : kk i ≤ KK i := by unfold KK; omega
    omega
  have hgap : (gridAt i).Q ≤ kIdx (gridAt i) n β - kIdx (gridAt i) n α := by
    have hmod : kIdx (gridAt i) n α % (gridAt i).Q = kIdx (gridAt i) n β % (gridAt i).Q := by
      rw [hα, hβ]
    have hQpos : 0 < (gridAt i).Q := by have := G4.GridParams.hQ (gridAt i); omega
    have hdvd : (gridAt i).Q ∣ kIdx (gridAt i) n β - kIdx (gridAt i) n α := by
      have : kIdx (gridAt i) n α ≡ kIdx (gridAt i) n β [MOD (gridAt i).Q] := hmod
      exact (Nat.modEq_iff_dvd' (le_of_lt hne)).1 this
    exact Nat.le_of_dvd (by omega) hdvd
  omega

/-! ### The cross-atom, cross-time case, reduced to one congruence -/

/-- `kIdx_mod_Q` in `ZMod Q`. -/
lemma kIdx_cast_Q (G : GridParams) {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    ((kIdx G n α : ℕ) : ZMod G.Q) = (n : ZMod G.Q) := by
  have h : (kIdx G n α : ℕ) ≡ n [MOD G.Q] := kIdx_mod_Q G hn α
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h

/-- **The remaining collision case is governed by a single congruence.**  Two windows at
different sample times and arbitrary atoms are disjoint as soon as `n − n'` avoids, modulo `Q`,
the `2·m_K` residues `±g` with `g < m_K`.

`kIdx_mod_Q` makes every orbit index congruent to its sample time mod `Q`, so a collision forces
`n − n' ≡ ±(index gap)` with the gap below `m_K`.  This is the exact arithmetic input a
*schedule-only* band read would need — a statement about the multiples of `P₀` modulo `Q`, with
no reference to `G₄`. -/
theorem windows_disjoint_of_mod (i : ℕ) {n n' : ℕ} (hn : n ∈ PK i) (hn' : n' ∈ PK i)
    (α β : (gridAt i).Atom)
    (hsep : ∀ g : ℕ, g < kk i →
      ((n : ZMod (gridAt i).Q) - (n' : ZMod (gridAt i).Q) ≠ (g : ZMod (gridAt i).Q)) ∧
      ((n' : ZMod (gridAt i).Q) - (n : ZMod (gridAt i).Q) ≠ (g : ZMod (gridAt i).Q))) :
    2 * kIdx (gridAt i) n α + kk i ≤ 2 * kIdx (gridAt i) n' β ∨
      2 * kIdx (gridAt i) n' β + kk i ≤ 2 * kIdx (gridAt i) n α := by
  classical
  set k : ℕ := kIdx (gridAt i) n α with hk
  set k' : ℕ := kIdx (gridAt i) n' β with hk'
  have hkn := kIdx_cast_Q (gridAt i) hn α
  have hk'n := kIdx_cast_Q (gridAt i) hn' β
  by_contra hcon
  push_neg at hcon
  obtain ⟨hA, hB⟩ := hcon
  rcases Nat.le_total k' k with hkk | hkk
  · have hgap : k - k' < kk i := by omega
    have hcast : ((k - k' : ℕ) : ZMod (gridAt i).Q)
        = (n : ZMod (gridAt i).Q) - (n' : ZMod (gridAt i).Q) := by
      rw [Nat.cast_sub hkk, hkn, hk'n]
    exact (hsep (k - k') hgap).1 hcast.symm
  · have hgap : k' - k < kk i := by omega
    have hcast : ((k' - k : ℕ) : ZMod (gridAt i).Q)
        = (n' : ZMod (gridAt i).Q) - (n : ZMod (gridAt i).Q) := by
      rw [Nat.cast_sub hkk, hk'n, hkn]
    exact (hsep (k' - k) hgap).2 hcast.symm

end NormalNumbers.G4.Sched
