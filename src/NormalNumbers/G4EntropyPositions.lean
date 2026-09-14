/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyLocality
import NormalNumbers.G4ScheduleGrid

/-!
# Entropy expedition §6: the sampled positions are ASTRONOMICALLY sparse

Second half of the attack on the brief's transfer target `T_E`.  `G4EntropyLocality` showed the
entropy hypothesis reads only the digits at `sampledPos G X m`.  This module counts that set.

The arithmetic input is already in `G4EntropySample.kIdx_spec`: every sampled orbit index
satisfies **`d_α ∣ kIdx G n α`** (the frozen multiplier residue).  Two steps turn that into
sparsity:

* `kIdx_pos` — the index is never `0`.  `kIdx = 0` forces `n = t_α`; but `n ≡ b₀ (mod P₀)` with
  `n = t_α < d_α² ≤ Mprod ≤ P₀` and `b₀ < P₀` forces `b₀ = t_α`, and then `b₀ ≡ t_β (mod d_β²)`
  with `t_α, t_β < d_β²` forces `t_α = t_β` for **every** `β`.  So a nonconstant offset `t`
  rules `kIdx = 0` out; `gridOf_t_nonconstant` supplies that (`gridV 0 = 0`, `gridV e₀ = B`).
* `kIdx_ge_d` — hence `kIdx = d_α · c` with `c ≥ 1`.

So every sampled position is `2·d_α·c + h` with `c ≥ 1` and `h < m`, and

  `|sampledPos ∩ [0,L)| ≤ ∑_α m·⌊L/(2 d_α)⌋ ≤ |Atom|·m·⌊L/(2 d_min)⌋`,

with `d_min = 1 + Q·D₀` for the implemented grid (`gridOf_dmin_le`).  Since `Q = (U+K+N+2)!`
and `D₀ = K·U` with `U ≥ B^K`, `d_min` dwarfs `|Atom|·m = (K²+1)^K·(K/4)`: the sampled
positions occupy a vanishing fraction of `[0,L)` **at every `L`**, and the scales with
`2 d_min > L` contribute nothing at all.

`T_E` would force the opposite (lower density `≥ 1/2`), which is what refutes it.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

variable (G : GridParams)

/-! ### The offset is smaller than every multiplier -/

/-- Every offset is below every multiplier: `t_α = Q·v_α ≤ Q·D₀ < 1 + Q(D₀ + u_β) = d_β`. -/
theorem t_lt_d' (α β : G.Atom) : G.t α < G.d β := by
  have hv : gridV G.B α ≤ G.D₀ := G.hD α
  have h : G.Q * gridV G.B α ≤ G.Q * (G.D₀ + gridU G.B β) :=
    Nat.mul_le_mul_left _ (le_trans hv (Nat.le_add_right _ _))
  show G.Q * gridV G.B α < 1 + G.Q * (G.D₀ + gridU G.B β)
  omega

lemma t_lt_sq_d (α β : G.Atom) : G.t α < G.d β ^ 2 := by
  have h1 := t_lt_d' G α β
  have h2 := G.d_pos β
  nlinarith

/-! ### The orbit index is a *positive* multiple of `d_α` -/

/-- If the offset `t` is nonconstant, no sample point sits at the base point of an atom, so
the orbit index never vanishes. -/
theorem kIdx_pos (hT : ∃ α β : G.Atom, G.t α ≠ G.t β) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) : 0 < kIdx G n α := by
  rcases Nat.eq_zero_or_pos (kIdx G n α) with h0 | h; swap
  · exact h
  exfalso
  -- `kIdx = 0` pins `n = t α`
  have hid := (kIdx_spec G hn α).1
  rw [h0, Nat.mul_zero, Nat.add_zero] at hid
  -- `t α < P₀`
  have hsq : G.d α ^ 2 ≤ G.Mprod := Nat.le_of_dvd G.Mprod_pos (G.sq_d_dvd_Mprod α)
  have hMP : G.Mprod ≤ G.P₀ := Nat.le_of_dvd G.P₀_pos G.Mprod_dvd_P₀
  have htP : G.t α < G.P₀ := lt_of_lt_of_le (t_lt_sq_d G α α) (le_trans hsq hMP)
  -- so `b₀ = t α`
  have hmod : n % G.P₀ = G.b₀ := (Finset.mem_filter.1 hn).2
  have hb : G.b₀ = G.t α := by
    rw [← hmod, hid, Nat.mod_eq_of_lt htP]
  -- hence `t` is constant
  obtain ⟨β, γ, hβγ⟩ := hT
  have key : ∀ δ : G.Atom, G.t α = G.t δ := by
    intro δ
    have h1 : G.b₀ ≡ G.t δ [MOD G.d δ ^ 2] := G.b₀_modEq δ
    rw [hb] at h1
    have h2 : G.t α % G.d δ ^ 2 = G.t α := Nat.mod_eq_of_lt (t_lt_sq_d G α δ)
    have h3 : G.t δ % G.d δ ^ 2 = G.t δ := Nat.mod_eq_of_lt (t_lt_sq_d G δ δ)
    unfold Nat.ModEq at h1
    rw [h2, h3] at h1
    exact h1
  exact hβγ (((key β).symm).trans (key γ))

/-- **The sparsity input**: every sampled orbit index is at least `d_α`. -/
theorem kIdx_ge_d (hT : ∃ α β : G.Atom, G.t α ≠ G.t β) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) : G.d α ≤ kIdx G n α :=
  Nat.le_of_dvd (kIdx_pos G hT hn α) (kIdx_spec G hn α).2

/-- The exact shape of a sampled index: `kIdx = d_α · c` with `c ≥ 1`. -/
theorem exists_kIdx_eq (hT : ∃ α β : G.Atom, G.t α ≠ G.t β) {X n : ℕ}
    (hn : n ∈ apSample X G.P₀ G.b₀) (α : G.Atom) :
    ∃ c, 1 ≤ c ∧ kIdx G n α = G.d α * c := by
  obtain ⟨c, hc⟩ := (kIdx_spec G hn α).2
  refine ⟨c, ?_, hc⟩
  rcases Nat.eq_zero_or_pos c with rfl | h
  · exfalso
    have hp := kIdx_pos G hT hn α
    rw [hc, Nat.mul_zero] at hp
    exact absurd hp (lt_irrefl 0)
  · exact h

/-! ### The count -/

/-- The positions contributed by one atom: `2 d_α c + h` with `1 ≤ c ≤ L/(2d_α)`, `h < m`. -/
private def column (α : G.Atom) (m L : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (L / (2 * G.d α))) ×ˢ Finset.range m).image
    (fun z => 2 * (G.d α * z.1) + z.2)

private lemma card_column_le (α : G.Atom) (m L : ℕ) :
    (column G α m L).card ≤ (L / (2 * G.d α)) * m := by
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_product, Nat.card_Icc]

/-- **The sampled positions below `L`, counted.**  Each atom can only contribute the
multiples of `2 d_α` (shifted by `h < m`), and never the multiple `0`. -/
theorem card_sampledPos_lt_le (hT : ∃ α β : G.Atom, G.t α ≠ G.t β) (X m L : ℕ) :
    ((sampledPos G X m).filter (fun j => j < L)).card
      ≤ ∑ α : G.Atom, (L / (2 * G.d α)) * m := by
  classical
  have hsub : (sampledPos G X m).filter (fun j => j < L)
      ⊆ Finset.univ.biUnion (fun α : G.Atom => column G α m L) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjs, hjL⟩ := hj
    obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos G).1 hjs
    obtain ⟨c, hc1, hc⟩ := exists_kIdx_eq G hT hn α
    refine Finset.mem_biUnion.2 ⟨α, Finset.mem_univ α, ?_⟩
    refine Finset.mem_image.2 ⟨(c, h), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hc1, ?_⟩, Finset.mem_range.2 hh⟩
      have hdpos : 0 < 2 * G.d α := by have := G.d_pos α; omega
      refine (Nat.le_div_iff_mul_le hdpos).2 ?_
      calc c * (2 * G.d α) = 2 * (G.d α * c) := by ring
        _ = 2 * kIdx G n α := by rw [hc]
        _ ≤ 2 * kIdx G n α + h := Nat.le_add_right _ _
        _ ≤ L := le_of_lt hjL
    · simp [hc]
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  exact Finset.sum_le_sum fun α _ => card_column_le G α m L

/-- The count against a uniform lower bound `dm ≤ d_α`. -/
theorem card_sampledPos_lt_le' (hT : ∃ α β : G.Atom, G.t α ≠ G.t β) (X m L : ℕ)
    {dm : ℕ} (hdm : 0 < dm) (hd : ∀ α : G.Atom, dm ≤ G.d α) :
    ((sampledPos G X m).filter (fun j => j < L)).card
      ≤ Fintype.card G.Atom * m * (L / (2 * dm)) := by
  refine le_trans (card_sampledPos_lt_le G hT X m L) ?_
  have hstep : ∀ α : G.Atom, (L / (2 * G.d α)) * m ≤ (L / (2 * dm)) * m := by
    intro α
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_left (by
      exact Nat.mul_le_mul_left 2 (hd α)) (by omega))
  refine le_trans (Finset.sum_le_sum fun α _ => hstep α) ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact le_of_eq (by ring)

/-! ### The implemented grid: `t` is nonconstant and `d_min = 1 + Q·D₀` -/

/-- The atom that is `1` in coordinate `0`. -/
private def e₀ (K : ℕ) (hK : 1 ≤ K) : Fin K → Fin (K ^ 2 + 1) :=
  fun i => if (i : ℕ) = 0 then ⟨1, by have : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
    else ⟨0, Nat.succ_pos _⟩

private lemma gridV_e₀ {K N : ℕ} (hK : 1 ≤ K) :
    gridV (gridB K N) (e₀ K hK) = gridB K N := by
  classical
  have h0 : (⟨0, hK⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
  have hz : ∀ i : Fin K, i ∈ (Finset.univ : Finset (Fin K)) → i ≠ (⟨0, hK⟩ : Fin K) →
      ((i : ℕ) + 1) * ((e₀ K hK i : ℕ)) * (gridB K N) ^ ((i : ℕ) + 1) = 0 := by
    intro i _ hi
    have hne : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    simp [e₀, hne]
  rw [gridV, Finset.sum_eq_single (⟨0, hK⟩ : Fin K) hz (fun hcon => absurd h0 hcon)]
  simp [e₀]

/-- **`t` is nonconstant for the implemented grid** — the input `kIdx_pos` needs. -/
theorem gridOf_t_nonconstant {K N : ℕ} (hK : 1 ≤ K) :
    ∃ α β : (gridOf K N hK).Atom, (gridOf K N hK).t α ≠ (gridOf K N hK).t β := by
  refine ⟨fun _ => ⟨0, Nat.succ_pos _⟩, e₀ K hK, ?_⟩
  have hQ : 0 < gridQ K N := lt_of_lt_of_le (by omega) (gridQ_gt K N)
  have hB : 0 < gridB K N := by unfold gridB; omega
  have h1 : (gridOf K N hK).t (fun _ => ⟨0, Nat.succ_pos _⟩) = 0 := by
    simp [GridParams.t, offset, gridV]
  have h2 : (gridOf K N hK).t (e₀ K hK) = gridQ K N * gridB K N := by
    show offset (gridB K N) (gridQ K N) (e₀ K hK) = _
    rw [offset, gridV_e₀ hK]
  rw [h1, h2]
  exact fun h => absurd h.symm (by positivity)

/-- **`d_min = 1 + Q·D₀`** for the implemented grid. -/
theorem gridOf_dmin_le {K N : ℕ} (hK : 1 ≤ K) (α : (gridOf K N hK).Atom) :
    1 + gridQ K N * gridD₀ K N ≤ (gridOf K N hK).d α := by
  show 1 + gridQ K N * gridD₀ K N
      ≤ 1 + gridQ K N * (gridD₀ K N + gridU (gridB K N) α)
  gcongr
  exact Nat.le_add_right _ _

/-- **The implemented grid's sampled positions below `L`.** -/
theorem card_sampledPos_gridOf_le {K N : ℕ} (hK : 1 ≤ K) (X m L : ℕ) :
    ((sampledPos (gridOf K N hK) X m).filter (fun j => j < L)).card
      ≤ (K ^ 2 + 1) ^ K * m * (L / (2 * (1 + gridQ K N * gridD₀ K N))) := by
  have hcard : Fintype.card (gridOf K N hK).Atom = (K ^ 2 + 1) ^ K := by
    show Fintype.card (Fin K → Fin (K ^ 2 + 1)) = (K ^ 2 + 1) ^ K
    simp
  rw [← hcard]
  exact card_sampledPos_lt_le' _ (gridOf_t_nonconstant hK) X m L (by omega)
    (gridOf_dmin_le hK)

end NormalNumbers.G4Entropy
