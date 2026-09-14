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

/-! ### `Q ∣ P₀`, and full window disjointness

The shifts satisfy `ρ_{α,j} ≡ j (mod Q)` (`shiftG_eq`), so two *different* atoms at the *same*
layer have shifts congruent mod `Q` — and `freezeQ` contains their distance as a factor.  Hence
`Q ∣ freezeQ ∣ P₀`, every sample time is congruent mod `Q`, and therefore **all** orbit indices
of **all** atoms at **all** sample times are congruent mod `Q`.  Since `Q ≫ m_K`, two sampled
windows either coincide or are disjoint.
-/

/-- `ρ_{α,j} ≡ ρ_{β,j} (mod Q)`: the shift only sees the layer, mod `Q`. -/
lemma rho_modEq (G : GridParams) (α β : G.Atom) (jj : Fin G.N) :
    G.ρ (α, jj) ≡ G.ρ (β, jj) [MOD G.Q] := by
  have hj : 1 ≤ layer G.K jj := by
    have := lt_layer G.K jj
    omega
  have h1 := shiftG_eq G.B G.Q G.D₀ α (G.hD α) hj
  have h2 := shiftG_eq G.B G.Q G.D₀ β (G.hD β) hj
  rw [Nat.modEq_iff_dvd]
  refine ⟨(proj G.B (layer G.K jj) β : ℤ) - (proj G.B (layer G.K jj) α : ℤ), ?_⟩
  show ((G.ρ (β, jj) : ℕ) : ℤ) - ((G.ρ (α, jj) : ℕ) : ℤ) = _
  have e1 : ((G.ρ (α, jj) : ℕ) : ℤ) = (layer G.K jj : ℤ)
      + G.Q * ((layer G.K jj : ℤ) * G.D₀ + proj G.B (layer G.K jj) α) := h1
  have e2 : ((G.ρ (β, jj) : ℕ) : ℤ) = (layer G.K jj : ℤ)
      + G.Q * ((layer G.K jj : ℤ) * G.D₀ + proj G.B (layer G.K jj) β) := h2
  rw [e1, e2]
  ring

/-- **`Q ∣ freezeQ`**: `freezeQ` contains the distance between two distinct atoms' shifts at one
layer, and `Q` divides that distance. -/
theorem Q_dvd_freezeQ (G : GridParams) (h2 : 2 ≤ Fintype.card G.Atom) (hN : 0 < G.N) :
    G.Q ∣ G.freezeQ := by
  classical
  obtain ⟨α, β, hαβ⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card G.Atom by omega)
  refine dvd_trans ?_ (G.dist_dvd_freezeQ (i := (α, ⟨0, hN⟩)) (i' := (β, ⟨0, hN⟩)) ?_)
  · have hmod := rho_modEq G α β ⟨0, hN⟩
    rcases Nat.le_total (G.ρ (α, ⟨0, hN⟩)) (G.ρ (β, ⟨0, hN⟩)) with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      exact (Nat.modEq_iff_dvd' h).1 hmod
    · rw [Nat.dist_eq_sub_of_le_right h]
      exact (Nat.modEq_iff_dvd' h).1 hmod.symm
  · intro hcon
    exact hαβ (congrArg Prod.fst hcon)

/-- **`Q ∣ P₀`.** -/
theorem Q_dvd_P₀ (G : GridParams) (h2 : 2 ≤ Fintype.card G.Atom) (hN : 0 < G.N) :
    G.Q ∣ G.P₀ :=
  dvd_trans (Q_dvd_freezeQ G h2 hN) G.freezeQ_dvd_P₀

/-- **All orbit indices, at all atoms and all sample times, are congruent mod `Q`.** -/
theorem kIdx_congr_Q (G : GridParams) (h2 : 2 ≤ Fintype.card G.Atom) (hN : 0 < G.N)
    {X n n' : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (hn' : n' ∈ apSample X G.P₀ G.b₀)
    (α β : G.Atom) : kIdx G n α ≡ kIdx G n' β [MOD G.Q] := by
  have h1 : kIdx G n α % G.Q = n % G.Q := kIdx_mod_Q G hn α
  have h2' : kIdx G n' β % G.Q = n' % G.Q := kIdx_mod_Q G hn' β
  have hb : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have hb' : n' % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn').2
  have hnn : n ≡ n' [MOD G.P₀] := by
    unfold Nat.ModEq
    rw [hb, hb']
  have : n ≡ n' [MOD G.Q] := hnn.of_dvd (Q_dvd_P₀ G h2 hN)
  show kIdx G n α % G.Q = kIdx G n' β % G.Q
  rw [h1, h2']
  exact this

lemma two_le_card_Atom (i : ℕ) : 2 ≤ Fintype.card (gridAt i).Atom := by
  rw [card_Atom_gridAt]
  have hK : 160000 ≤ KK i := KK_ge i
  have h1 : 2 ≤ KK i ^ 2 + 1 := by nlinarith
  calc 2 ≤ KK i ^ 2 + 1 := h1
    _ = (KK i ^ 2 + 1) ^ 1 := (pow_one _).symm
    _ ≤ (KK i ^ 2 + 1) ^ KK i := Nat.pow_le_pow_right (by omega) (by omega)

lemma N_pos_gridAt (i : ℕ) : 0 < (gridAt i).N := by
  show 0 < N (KK i)
  have := KK_ge i
  unfold N
  nlinarith

/-- **Every two sampled windows either coincide or are disjoint.**  This is the full
disjointness the same-atom (lap 65) and same-time (lap 93) cases only approximated: `Q ∣ P₀`
makes *all* orbit indices congruent mod `Q`, and `Q > m_K`. -/
theorem windows_eq_or_disjoint (i : ℕ) {n n' : ℕ} (hn : n ∈ PK i) (hn' : n' ∈ PK i)
    (α β : (gridAt i).Atom) :
    kIdx (gridAt i) n α = kIdx (gridAt i) n' β ∨
      2 * kIdx (gridAt i) n α + kk i ≤ 2 * kIdx (gridAt i) n' β ∨
      2 * kIdx (gridAt i) n' β + kk i ≤ 2 * kIdx (gridAt i) n α := by
  have hcong := kIdx_congr_Q (gridAt i) (two_le_card_Atom i) (N_pos_gridAt i) hn hn' α β
  have hQ : kk i < (gridAt i).Q := by
    have hgt : gridUmax (KK i) (N (KK i)) + KK i + N (KK i) + 2
        ≤ gridQ (KK i) (N (KK i)) := gridQ_gt _ _
    have hQeq : (gridAt i).Q = gridQ (KK i) (N (KK i)) := rfl
    have hkkK : kk i ≤ KK i := by unfold KK; omega
    omega
  rcases Nat.lt_trichotomy (kIdx (gridAt i) n α) (kIdx (gridAt i) n' β) with h | h | h
  · right; left
    have hdvd : (gridAt i).Q ∣ kIdx (gridAt i) n' β - kIdx (gridAt i) n α :=
      (Nat.modEq_iff_dvd' (le_of_lt h)).1 hcong
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · exact Or.inl h
  · right; right
    have hdvd : (gridAt i).Q ∣ kIdx (gridAt i) n α - kIdx (gridAt i) n' β :=
      (Nat.modEq_iff_dvd' (le_of_lt h)).1 hcong.symm
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-! ### Window multiplicity: two atoms share at most a `P₀`-sparse set of orbit indices

A window position `2k` can be produced by more than one atom only if the *same* `k` solves the
progression condition for both.  Two such `k` differ by a multiple of `P₀`: the conditions give
`P₀ ∣ d_α·(k − k')` and `P₀ ∣ d_β·(k − k')`, and `d_α`, `d_β` are coprime (`coprime_d`), so
`P₀ ∣ k − k'`.  So for each pair of atoms the shared indices are a single arithmetic progression
of modulus `P₀` — astronomically sparser than the `X/d` indices each atom uses.
-/

/-- `k` is *active* for `α` when the sample time it forces lies in the progression. -/
def ActiveIdx (G : GridParams) (α : G.Atom) (k : ℕ) : Prop :=
  (G.t α + G.d α * k) % G.P₀ = G.b₀

/-- **Two atoms' shared orbit indices are `P₀` apart.** -/
theorem shared_idx_apart (G : GridParams) {α β : G.Atom} (hαβ : α ≠ β) {k k' : ℕ}
    (hk : k' ≤ k) (h1 : ActiveIdx G α k) (h2 : ActiveIdx G β k)
    (h1' : ActiveIdx G α k') (h2' : ActiveIdx G β k') :
    k = k' ∨ G.P₀ ≤ k - k' := by
  classical
  set g : ℕ := k - k' with hg
  have hdα : G.P₀ ∣ G.d α * g := by
    have hmod : (G.t α + G.d α * k') ≡ (G.t α + G.d α * k) [MOD G.P₀] := by
      unfold Nat.ModEq
      rw [h1', h1]
    have hle : G.t α + G.d α * k' ≤ G.t α + G.d α * k := by
      have : G.d α * k' ≤ G.d α * k := Nat.mul_le_mul_left _ hk
      omega
    have hdvd := (Nat.modEq_iff_dvd' hle).1 hmod
    have heq : G.t α + G.d α * k - (G.t α + G.d α * k')
        = G.d α * g := by
      rw [hg, Nat.mul_sub]
      have : G.d α * k' ≤ G.d α * k := Nat.mul_le_mul_left _ hk
      omega
    rwa [heq] at hdvd
  have hdβ : G.P₀ ∣ G.d β * g := by
    have hmod : (G.t β + G.d β * k') ≡ (G.t β + G.d β * k) [MOD G.P₀] := by
      unfold Nat.ModEq
      rw [h2', h2]
    have hle : G.t β + G.d β * k' ≤ G.t β + G.d β * k := by
      have : G.d β * k' ≤ G.d β * k := Nat.mul_le_mul_left _ hk
      omega
    have hdvd := (Nat.modEq_iff_dvd' hle).1 hmod
    have heq : G.t β + G.d β * k - (G.t β + G.d β * k')
        = G.d β * g := by
      rw [hg, Nat.mul_sub]
      have : G.d β * k' ≤ G.d β * k := Nat.mul_le_mul_left _ hk
      omega
    rwa [heq] at hdvd
  have hgcd : G.P₀ ∣ Nat.gcd (G.d α * g) (G.d β * g) := Nat.dvd_gcd hdα hdβ
  have hrw : Nat.gcd (G.d α * g) (G.d β * g) = g := by
    rw [Nat.gcd_mul_right, (G.coprime_d hαβ : Nat.gcd (G.d α) (G.d β) = 1), one_mul]
  rw [hrw] at hgcd
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · left; omega
  · right
    exact Nat.le_of_dvd hpos hgcd

/-- Every sample time of the progression makes its own orbit index active. -/
lemma activeIdx_kIdx (G : GridParams) {X n : ℕ} (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    ActiveIdx G α (kIdx G n α) := by
  obtain ⟨hk, -⟩ := kIdx_spec G hn α
  show (G.t α + G.d α * kIdx G n α) % G.P₀ = G.b₀
  rw [← hk]
  exact (Finset.mem_filter.1 hn).2

open Classical in
/-- **The shared indices below `M` number at most `M/P₀ + 1`.** -/
theorem card_shared_le (G : GridParams) {α β : G.Atom} (hαβ : α ≠ β) (M : ℕ) :
    (((Finset.range M).filter (fun k => ActiveIdx G α k ∧ ActiveIdx G β k)).card)
      ≤ M / G.P₀ + 1 := by
  classical
  have hP₀ : 0 < G.P₀ := G.P₀_pos
  have hcard : (((Finset.range M).filter
      (fun k => ActiveIdx G α k ∧ ActiveIdx G β k)).card)
      ≤ (Finset.range (M / G.P₀ + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun k => k / G.P₀) ?_ ?_
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hk
      have h1 : k < M := hk.1
      have h2 : k / G.P₀ ≤ M / G.P₀ := Nat.div_le_div_right (le_of_lt h1)
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro k hk k' hk' heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hk hk'
      simp only at heq
      by_contra hne
      rcases Nat.lt_or_ge k k' with hlt | hge
      · have hsh := shared_idx_apart G hαβ (le_of_lt hlt) hk'.2.1 hk'.2.2 hk.2.1 hk.2.2
        rcases hsh with h | h
        · omega
        · have : k / G.P₀ + 1 ≤ k' / G.P₀ := by
            have hle : k + G.P₀ ≤ k' := by omega
            calc k / G.P₀ + 1 = (k + G.P₀) / G.P₀ := by rw [Nat.add_div_right _ hP₀]
              _ ≤ k' / G.P₀ := Nat.div_le_div_right hle
          omega
      · have hgt : k' < k := by omega
        have hsh := shared_idx_apart G hαβ (le_of_lt hgt) hk.2.1 hk.2.2 hk'.2.1 hk'.2.2
        rcases hsh with h | h
        · omega
        · have : k' / G.P₀ + 1 ≤ k / G.P₀ := by
            have hle : k' + G.P₀ ≤ k := by omega
            calc k' / G.P₀ + 1 = (k' + G.P₀) / G.P₀ := by rw [Nat.add_div_right _ hP₀]
              _ ≤ k / G.P₀ := Nat.div_le_div_right hle
          omega
  simpa using hcard

open Classical in
/-- **How many scale-`i` sample times give an `α`-window that some *other* atom `β` also
produces**: at most `X/P₀ + 1`, against the `|P_K| ≈ X/P₀` times `α` has in total — so a pair of
atoms collides on a vanishing fraction, `≈ 1/|P_K|`, of the sample. -/
theorem card_collide_pair_le (i : ℕ) {α β : (gridAt i).Atom} (hαβ : α ≠ β) :
    (((PK i).filter (fun n => ActiveIdx (gridAt i) β (kIdx (gridAt i) n α))).card)
      ≤ X (KK i) / (gridAt i).P₀ + 1 := by
  classical
  refine le_trans ?_ (card_shared_le (gridAt i) hαβ (X (KK i)))
  refine Finset.card_le_card_of_injOn (fun n => kIdx (gridAt i) n α) ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hn ⊢
    refine ⟨Finset.mem_range.2 ?_, activeIdx_kIdx (gridAt i) hn.1 α, hn.2⟩
    have hnX : n < X (KK i) := Finset.mem_range.1 (Finset.mem_filter.1 hn.1).1
    have hle : kIdx (gridAt i) n α ≤ n :=
      le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    omega
  · intro n hn n' hn' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hn hn'
    simp only at heq
    by_contra hne
    rcases Nat.lt_or_ge n n' with hlt | hge
    · have := window_gap_same_atom i α hn.1 hn'.1 hlt
      have hkk : 0 < kk i := by unfold kk; omega
      omega
    · have hgt : n' < n := by omega
      have := window_gap_same_atom i α hn'.1 hn.1 hgt
      have hkk : 0 < kk i := by unfold kk; omega
      omega

end NormalNumbers.G4.Sched
