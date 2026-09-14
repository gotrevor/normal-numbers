/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyJointUniform

/-!
# The uniform `t`-wise bound at *unaligned* positions

`G4EntropyJointUniform` averaged over all vectors of **aligned** positions `jj s · ℓ`,
`jj ∈ [0,J)^t`.  The grid alignment was an artefact of `abs_avg_patPos_prob_opt`, whose family
of coordinates advances in steps of `ℓ`; it is not a feature of the arithmetic.

This module removes it.  Average over all vectors of **arbitrary** positions `pv ∈ [0,P)^t`.
Decompose `pv = d + j·1` with `min d = 0` (`sum_diag_decomp`), and then split the diagonal
parameter `j` by its residue mod `ℓ` (`sum_range_mod_decomp`): for each fixed `(d, r)` the
positions `d s + r + qℓ` form exactly an aligned family at the offset vector `pp s = d s + r`,
which is what `abs_alignedFamily_sub_le` controls.  There are `≤ t·P^{t−1}` diagonals and `ℓ`
residues, each contributing `≤ 2√(|B|Q·log 2·Δ)` with `Qℓ ≤ 2P`, so the average deviates by at
most

    `(t·P^{t−1}·ℓ / P^t) · 2√(|B|·(2P/ℓ)·log 2·Δ) / |B| = 2t√(2 log 2 · ℓ · Δ / (|B|·P))`

— the same bound as the aligned uniform average (there `J ≍ m/ℓ`, here `P ≍ m`), up to the
factor `√2`.  Removing the alignment is free.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The pattern read at an arbitrary vector of positions (no alignment). -/
def pvPat (m ℓ t : ℕ) (blk : B → Fin t → A) (b : B) (pv : Fin t → ℕ)
    (z : A → Fin (2 ^ m)) : Fin (2 ^ (ℓ * t)) :=
  packFin t ℓ (fun s => posAt m ℓ (pv s) (z (blk b s)))

lemma jjPat_eq_pvPat (m ℓ t : ℕ) (blk : B → Fin t → A) (b : B) (jj : Fin t → ℕ) :
    jjPat m ℓ t blk b jj = pvPat m ℓ t blk b (fun s => jj s * ℓ) := rfl

/-- `patPos` at an offset vector **is** `pvPat` at the shifted position vector. -/
lemma patPos_eq_pvPat (m ℓ t D : ℕ) (pp : Fin t → ℕ) (blk : B → Fin t → A)
    (c : B × Fin (D / ℓ)) : patPos m ℓ t D pp blk c
      = pvPat m ℓ t blk c.1 (fun s => pp s + (c.2 : ℕ) * ℓ) := rfl

/-- The block-aggregated pattern mass at a vector of positions. -/
noncomputable def pvAgg (m ℓ t : ℕ) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) (pv : Fin t → ℕ) : ℝ :=
  ∑ b : B, (L.map (pvPat m ℓ t blk b pv)).prob {w}

/-- **One aligned family.**  The `Q` position vectors `pp + q·ℓ·1` deviate, in total, from
`|B|·Q·2^{−ℓt}` by at most `2√(|B|Q·log 2·Δ)`. -/
theorem abs_alignedFamily_sub_le {m ℓ t Q : ℕ} (hℓ : 0 < ℓ) (ht : 0 < t) [Nonempty B]
    (pp : Fin t → ℕ) (hpp : ∀ s, pp s + Q * ℓ ≤ m)
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |(∑ q ∈ Finset.range Q, pvAgg m ℓ t blk L w (fun s => pp s + q * ℓ))
       - (Fintype.card B : ℝ) * (Q : ℝ) / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * Real.sqrt ((Fintype.card B : ℝ) * (Q : ℝ) * (Real.log 2 * Δ)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcB : (0 : ℝ) < (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := B)
  have hX0 : (0 : ℝ) ≤ Real.log 2 * Δ := by positivity
  rcases Nat.eq_zero_or_pos Q with rfl | hQ0
  · norm_num
  have hDl : Q * ℓ / ℓ = Q := Nat.mul_div_cancel _ hℓ
  have hℓD : ℓ ≤ Q * ℓ := by
    have h : 1 * ℓ ≤ Q * ℓ := Nat.mul_le_mul_right ℓ hQ0
    simpa using h
  have hDm : Q * ℓ ≤ m := le_trans (Nat.le_add_left _ _) (hpp ⟨0, ht⟩)
  have key := abs_avg_patPos_prob_opt (A := A) (B := B) (m := m) (ℓ := ℓ) (t := t) (D := Q * ℓ)
    hℓ hℓD ht hDm pp hpp blk hblk L w hΔ0 hΔ
  have hstep : ∀ b : B,
      (∑ q : Fin (Q * ℓ / ℓ),
          (L.map (patPos m ℓ t (Q * ℓ) pp blk (b, q))).prob {w})
        = ∑ q ∈ Finset.range Q,
            (L.map (pvPat m ℓ t blk b (fun s => pp s + q * ℓ))).prob {w} := by
    intro b
    have h1 : ∀ q : Fin (Q * ℓ / ℓ),
        (L.map (patPos m ℓ t (Q * ℓ) pp blk (b, q))).prob {w}
          = (fun k : ℕ => (L.map (pvPat m ℓ t blk b (fun s => pp s + k * ℓ))).prob {w})
              ((q : ℕ)) := fun q => rfl
    rw [Finset.sum_congr rfl (fun q _ => h1 q),
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (L.map (pvPat m ℓ t blk b (fun s => pp s + k * ℓ))).prob {w}), hDl]
  have hsum : (∑ c : B × Fin (Q * ℓ / ℓ),
        (L.map (patPos m ℓ t (Q * ℓ) pp blk c)).prob {w})
      = ∑ q ∈ Finset.range Q, pvAgg m ℓ t blk L w (fun s => pp s + q * ℓ) := by
    rw [Fintype.sum_prod_type]
    simp only [hstep, pvAgg]
    exact Finset.sum_comm
  have hcard : (Fintype.card (B × Fin (Q * ℓ / ℓ)) : ℝ) = (Fintype.card B : ℝ) * (Q : ℝ) := by
    simp [hDl]
  rw [hsum, hcard] at key
  set T := ∑ q ∈ Finset.range Q, pvAgg m ℓ t blk L w (fun s => pp s + q * ℓ) with hT
  have hcR : (0 : ℝ) < (Fintype.card B : ℝ) * (Q : ℝ) := by
    have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
    positivity
  have hid : T - (Fintype.card B : ℝ) * (Q : ℝ) / (2 : ℝ) ^ (ℓ * t)
      = ((Fintype.card B : ℝ) * (Q : ℝ))
          * (T / ((Fintype.card B : ℝ) * (Q : ℝ)) - 1 / (2 : ℝ) ^ (ℓ * t)) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hcR]
  refine le_trans (mul_le_mul_of_nonneg_left key hcR.le) ?_
  have hXe : Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * ((Q * ℓ : ℕ) : ℝ))
      = (Real.log 2 * Δ) / ((Fintype.card B : ℝ) * (Q : ℝ)) := by
    have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
    push_cast
    field_simp
  rw [hXe]
  have e1 : (Fintype.card B : ℝ) * (Q : ℝ)
      * (2 * Real.sqrt (Real.log 2 * Δ / ((Fintype.card B : ℝ) * (Q : ℝ))))
      = 2 * Real.sqrt (((Fintype.card B : ℝ) * (Q : ℝ)) * (Real.log 2 * Δ)) := by
    rw [← mul_sqrt_div_self hcR hX0]; ring
  rw [e1]

/-! ### Splitting a range by residue mod `ℓ` -/

/-- The number of `q` with `r + qℓ < R`. -/
def cntRes (R ℓ r : ℕ) : ℕ := (R - r + (ℓ - 1)) / ℓ

lemma lt_cntRes_iff {R ℓ r q : ℕ} (hℓ : 0 < ℓ) : q < cntRes R ℓ r ↔ r + q * ℓ < R := by
  rw [cntRes, ← Nat.succ_le_iff, Nat.le_div_iff_mul_le hℓ]
  have h1 : Nat.succ q * ℓ = q * ℓ + ℓ := Nat.succ_mul q ℓ
  obtain ⟨X, hX⟩ : ∃ X, q * ℓ = X := ⟨_, rfl⟩
  rw [hX] at h1 ⊢
  omega

/-- **The residue decomposition** of a range: `j < R` is `r + qℓ` with `r < ℓ` uniquely. -/
theorem sum_range_mod_decomp (R ℓ : ℕ) (hℓ : 0 < ℓ) (g : ℕ → ℝ) :
    ∑ j ∈ Finset.range R, g j
      = ∑ r ∈ Finset.range ℓ, ∑ q ∈ Finset.range (cntRes R ℓ r), g (r + q * ℓ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun j => j % ℓ)
      (fun j _ => Finset.mem_range.2 (Nat.mod_lt _ hℓ)) g]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  refine (Finset.sum_nbij' (i := fun q => r + q * ℓ) (j := fun j => j / ℓ) ?_ ?_ ?_ ?_ ?_).symm
  · intro q hq
    rw [Finset.mem_range] at hq
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨(lt_cntRes_iff hℓ).1 hq, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_range, lt_cntRes_iff hℓ, ← hj.2, Nat.mod_add_div']
    exact hj.1
  · intro q hq
    rw [Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt hr, zero_add]
  · intro j hj
    rw [Finset.mem_filter] at hj
    rw [← hj.2, Nat.mod_add_div']
  · intro q hq
    rfl

/-! ### The uniform average over all position vectors -/

/-- **The uniform pattern frequency at unaligned positions**: the average over blocks and over
*all* vectors of positions in `[0, P)^t`. -/
noncomputable def uniPosFreq (m ℓ t P : ℕ) (blk : B → Fin t → A)
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) : ℝ :=
  (∑ b : B, ∑ pv : Fin t → Fin P,
      (L.map (pvPat m ℓ t blk b (fun s => ((pv s : ℕ))))).prob {w})
    / ((Fintype.card B : ℝ) * (P : ℝ) ^ t)

/-- **The uniform bound at unaligned positions.**  Averaged over *all* `P^t` vectors of
positions, the `ℓt`-bit pattern frequency deviates from `2^{−ℓt}` by at most
`2t√(2 log 2 · ℓ Δ / (|B|·P))`.

TODO(lap 47): schedule instance and digit rendering. -/
theorem abs_uniPosFreq_sub_le {m ℓ t P : ℕ} (hℓ : 0 < ℓ) (ht : 0 < t) (hℓP : ℓ ≤ P)
    (hPm : P + ℓ ≤ m + 1) [Nonempty B]
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |uniPosFreq m ℓ t P blk L w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * (t : ℝ)
          * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (P : ℝ))) := by
  sorry

end NormalNumbers.G4Entropy
