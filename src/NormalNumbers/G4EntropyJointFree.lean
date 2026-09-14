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

/-- `a·√X = √(a²X)` for `a ≥ 0`. -/
lemma mul_sqrt_eq {a X : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X) :
    a * Real.sqrt X = Real.sqrt (a ^ 2 * X) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]

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
`2t√(2 log 2 · ℓ Δ / (|B|·P))` — the aligned uniform bound (`abs_uniPatFreq_sub_le`, where
`J ≍ m/ℓ` gives `2t√(log 2 · ℓΔ/(|B|m))`) up to the factor `√2`.  Dropping the alignment is
free.

TODO(lap 47): schedule instance and digit rendering. -/
theorem abs_uniPosFreq_sub_le {m ℓ t P : ℕ} (hℓ : 0 < ℓ) (ht : 0 < t) (hℓP : ℓ ≤ P)
    (hPm : P + ℓ ≤ m + 1) [Nonempty B]
    (blk : B → Fin t → A) (hblk : Function.Injective (fun p : B × Fin t => blk p.1 p.2))
    (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ (ℓ * t))) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) :
    |uniPosFreq m ℓ t P blk L w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * (t : ℝ)
          * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (P : ℝ))) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcB : (0 : ℝ) < (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := B)
  have hPpos : 0 < P := lt_of_lt_of_le hℓ hℓP
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hX0 : (0 : ℝ) ≤ Real.log 2 * Δ := by positivity
  have hden : (0 : ℝ) < (Fintype.card B : ℝ) * (P : ℝ) ^ t := by positivity
  have hcP : (0 : ℝ) < (Fintype.card B : ℝ) * (P : ℝ) := by positivity
  set C : ℝ :=
    2 * Real.sqrt ((Fintype.card B : ℝ) * (2 * (P : ℝ) / (ℓ : ℝ)) * (Real.log 2 * Δ)) with hCdef
  have hY0 : (0 : ℝ) ≤ (Fintype.card B : ℝ) * (2 * (P : ℝ) / (ℓ : ℝ)) * (Real.log 2 * Δ) := by
    positivity
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  -- the bound for one (diagonal, residue) pair
  have hpair : ∀ d ∈ diagSet t P, ∀ r ∈ Finset.range ℓ,
      |(∑ q ∈ Finset.range (cntRes (P - (Finset.univ.sup fun s => ((d s : ℕ)))) ℓ r),
          pvAgg m ℓ t blk L w (fun s => (d s : ℕ) + (r + q * ℓ)))
        - (Fintype.card B : ℝ)
            * ((cntRes (P - (Finset.univ.sup fun s => ((d s : ℕ)))) ℓ r : ℕ) : ℝ)
            / (2 : ℝ) ^ (ℓ * t)| ≤ C := by
    intro d _ r hr
    rw [Finset.mem_range] at hr
    have hSP : (Finset.univ.sup fun s => ((d s : ℕ))) < P := sup_coe_lt hPpos d
    have hdS : ∀ s, (d s : ℕ) ≤ (Finset.univ.sup fun s => ((d s : ℕ))) := fun s =>
      Finset.le_sup (f := fun s => ((d s : ℕ))) (Finset.mem_univ s)
    set S := (Finset.univ.sup fun s => ((d s : ℕ))) with hS
    set Q := cntRes (P - S) ℓ r with hQ
    have hQb : Q * ℓ + r + 1 ≤ (P - S) + ℓ := by
      rcases Nat.eq_zero_or_pos Q with h0 | hQ0
      · rw [h0]; omega
      · obtain ⟨Q', hQ'⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        have hlt := (lt_cntRes_iff (R := P - S) (ℓ := ℓ) (r := r) (q := Q') hℓ).1
          (by rw [← hQ, hQ']; omega)
        have he : Q * ℓ = Q' * ℓ + ℓ := by rw [hQ']; ring
        omega
    have hpp : ∀ s, ((d s : ℕ) + r) + Q * ℓ ≤ m := by
      intro s
      have h1 := hdS s
      obtain ⟨Y, hY⟩ : ∃ Y, Q * ℓ = Y := ⟨_, rfl⟩
      rw [hY] at hQb ⊢
      omega
    have key := abs_alignedFamily_sub_le (A := A) (B := B) (m := m) (ℓ := ℓ) (t := t) (Q := Q)
      hℓ ht (fun s => (d s : ℕ) + r) hpp blk hblk L w hΔ0 hΔ
    have harg : ∀ q : ℕ, (fun s => ((d s : ℕ) + r) + q * ℓ)
        = (fun s : Fin t => (d s : ℕ) + (r + q * ℓ)) := by
      intro q; funext s; ring
    simp only [harg] at key
    refine key.trans ?_
    rw [hCdef]
    have hQnat : Q * ℓ ≤ 2 * P := by
      obtain ⟨Y, hY⟩ : ∃ Y, Q * ℓ = Y := ⟨_, rfl⟩
      rw [hY] at hQb ⊢
      omega
    have hQle : (Q : ℝ) * (ℓ : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQnat
    have hQdiv : (Q : ℝ) ≤ 2 * (P : ℝ) / (ℓ : ℝ) := by
      rw [le_div_iff₀ hℓR]; exact hQle
    have hmono : (Fintype.card B : ℝ) * (Q : ℝ) * (Real.log 2 * Δ)
        ≤ (Fintype.card B : ℝ) * (2 * (P : ℝ) / (ℓ : ℝ)) * (Real.log 2 * Δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQdiv hcB.le) hX0
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)
  -- the numerator, decomposed over diagonals and residues
  have hN1 : (∑ b : B, ∑ pv : Fin t → Fin P,
        (L.map (pvPat m ℓ t blk b (fun s => ((pv s : ℕ))))).prob {w})
      = ∑ d ∈ diagSet t P,
          ∑ j ∈ Finset.range (P - (Finset.univ.sup fun s => ((d s : ℕ)))),
            pvAgg m ℓ t blk L w (fun s => (d s : ℕ) + j) := by
    rw [Finset.sum_comm]
    exact sum_diag_decomp ht (pvAgg m ℓ t blk L w)
  have hN : (∑ b : B, ∑ pv : Fin t → Fin P,
        (L.map (pvPat m ℓ t blk b (fun s => ((pv s : ℕ))))).prob {w})
      = ∑ d ∈ diagSet t P, ∑ r ∈ Finset.range ℓ,
          ∑ q ∈ Finset.range (cntRes (P - (Finset.univ.sup fun s => ((d s : ℕ)))) ℓ r),
            pvAgg m ℓ t blk L w (fun s => (d s : ℕ) + (r + q * ℓ)) := by
    rw [hN1]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact sum_range_mod_decomp _ ℓ hℓ
      (fun j => pvAgg m ℓ t blk L w (fun s => (d s : ℕ) + j))
  -- the diagonals' lengths total `P^t`, and each splits into its residue counts
  have hcount : ∑ d ∈ diagSet t P,
      ((P - (Finset.univ.sup fun s => ((d s : ℕ))) : ℕ) : ℝ) = (P : ℝ) ^ t := by
    have h := sum_diag_decomp (t := t) (J := P) ht (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Finset.card_range] at h
    rw [← h]
    push_cast
    ring
  have hcount2 : ∀ R : ℕ, (R : ℝ) = ∑ r ∈ Finset.range ℓ, ((cntRes R ℓ r : ℕ) : ℝ) := by
    intro R
    have h := sum_range_mod_decomp R ℓ hℓ (fun _ => (1 : ℝ))
    simpa using h
  have hsplit : (Fintype.card B : ℝ) * (P : ℝ) ^ t / (2 : ℝ) ^ (ℓ * t)
      = ∑ d ∈ diagSet t P, ∑ r ∈ Finset.range ℓ, (Fintype.card B : ℝ)
          * ((cntRes (P - (Finset.univ.sup fun s => ((d s : ℕ)))) ℓ r : ℕ) : ℝ)
          / (2 : ℝ) ^ (ℓ * t) := by
    rw [← hcount, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hcount2 (P - (Finset.univ.sup fun s => ((d s : ℕ)))), Finset.mul_sum, Finset.sum_div]
  have hdev : |(∑ b : B, ∑ pv : Fin t → Fin P,
        (L.map (pvPat m ℓ t blk b (fun s => ((pv s : ℕ))))).prob {w})
      - (Fintype.card B : ℝ) * (P : ℝ) ^ t / (2 : ℝ) ^ (ℓ * t)|
      ≤ ((diagSet t P).card : ℝ) * ((ℓ : ℝ) * C) := by
    rw [hN, hsplit, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ ((ℓ : ℝ) * C) ?_) ?_
    · intro d hd
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ C (fun r hr => hpair d hd r hr)) ?_
      rw [Finset.card_range, nsmul_eq_mul]
    · rw [nsmul_eq_mul]
  -- divide
  have huni : uniPosFreq m ℓ t P blk L w - 1 / (2 : ℝ) ^ (ℓ * t)
      = ((∑ b : B, ∑ pv : Fin t → Fin P,
            (L.map (pvPat m ℓ t blk b (fun s => ((pv s : ℕ))))).prob {w})
          - (Fintype.card B : ℝ) * (P : ℝ) ^ t / (2 : ℝ) ^ (ℓ * t))
        / ((Fintype.card B : ℝ) * (P : ℝ) ^ t) := by
    rw [uniPosFreq]
    field_simp
  rw [huni, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine le_trans hdev ?_
  have hcardle : ((diagSet t P).card : ℝ) ≤ (t : ℝ) * (P : ℝ) ^ (t - 1) := by
    exact_mod_cast card_diagSet_le t P
  refine le_trans (mul_le_mul_of_nonneg_right hcardle (by positivity)) ?_
  -- the arithmetic
  have eC : (ℓ : ℝ) * C
      = 2 * Real.sqrt (2 * (ℓ : ℝ) * ((Fintype.card B : ℝ) * (P : ℝ)) * (Real.log 2 * Δ)) := by
    rw [hCdef]
    have h1 : (ℓ : ℝ)
        * (2 * Real.sqrt ((Fintype.card B : ℝ) * (2 * (P : ℝ) / (ℓ : ℝ)) * (Real.log 2 * Δ)))
        = 2 * ((ℓ : ℝ)
            * Real.sqrt ((Fintype.card B : ℝ) * (2 * (P : ℝ) / (ℓ : ℝ)) * (Real.log 2 * Δ))) := by
      ring
    rw [h1, mul_sqrt_eq hℓR.le hY0]
    congr 2
    field_simp
  have hP1 : (P : ℝ) ^ (t - 1) * (P : ℝ) = (P : ℝ) ^ t := by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    simp [pow_succ]
  have hkey : ((Fintype.card B : ℝ) * (P : ℝ))
      * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (P : ℝ)))
      = Real.sqrt (((Fintype.card B : ℝ) * (P : ℝ)) * (2 * Real.log 2 * (ℓ : ℝ) * Δ)) :=
    mul_sqrt_div_self hcP (by positivity)
  rw [eC]
  calc (t : ℝ) * (P : ℝ) ^ (t - 1)
        * (2 * Real.sqrt (2 * (ℓ : ℝ) * ((Fintype.card B : ℝ) * (P : ℝ)) * (Real.log 2 * Δ)))
      = Real.sqrt (((Fintype.card B : ℝ) * (P : ℝ)) * (2 * Real.log 2 * (ℓ : ℝ) * Δ))
          * (2 * (t : ℝ) * (P : ℝ) ^ (t - 1)) := by
        rw [show ((Fintype.card B : ℝ) * (P : ℝ)) * (2 * Real.log 2 * (ℓ : ℝ) * Δ)
            = 2 * (ℓ : ℝ) * ((Fintype.card B : ℝ) * (P : ℝ)) * (Real.log 2 * Δ) from by ring]
        ring
    _ ≤ 2 * (t : ℝ)
          * Real.sqrt (2 * Real.log 2 * (ℓ : ℝ) * Δ / ((Fintype.card B : ℝ) * (P : ℝ)))
          * ((Fintype.card B : ℝ) * (P : ℝ) ^ t) :=
        le_of_eq (by rw [← hkey, ← hP1]; ring)

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4Entropy

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Unpacking the unaligned pattern coordinate into its `t` component blocks. -/
lemma pvPat_eq_pack_iff (m ℓ t : ℕ) (blk : B → Fin t → A) (b : B) (pv : Fin t → ℕ)
    (z : A → Fin (2 ^ m)) (u : Fin t → Fin (2 ^ ℓ)) :
    pvPat m ℓ t blk b pv z = packFin t ℓ u
      ↔ ∀ s : Fin t, posAt m ℓ (pv s) (z (blk b s)) = u s := by
  constructor
  · intro h s
    exact congrFun ((packFin t ℓ).injective h) s
  · intro h
    exact congrArg (packFin t ℓ) (funext h)

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The schedule instance: every vector of *unrestricted* sampled positions -/

/-- **The free sampled-pattern frequency**: averaged over the blocks and over *all* vectors of
positions in `[0, m_K − ℓ + 1)^t` — every position at which an `ℓ`-window fits inside the
sampled window, with no alignment condition. -/
noncomputable def freeFreq (i ℓ t : ℕ) (x : ℝ) (w : Fin (2 ^ (ℓ * t))) : ℝ :=
  uniPosFreq (kk i) ℓ t (kk i - ℓ + 1) (blkSched i t) (jointLawAt i x) w

/-- **The free capacity inequality.** -/
theorem abs_freeFreq_sub_le_of_deficit (i ℓ t : ℕ) (hℓ : 0 < ℓ) (ht : 0 < t)
    (hfit : 2 * ℓ ≤ kk i) (hcard : 2 * t ≤ Fintype.card (gridAt i).Atom)
    (x : ℝ) (w : Fin (2 ^ (ℓ * t))) {δ : ℝ} (hδ : 0 < δ)
    (hdef : ((kk i : ℝ) - δ) * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂) :
    |freeFreq i ℓ t x w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * (t : ℝ) * Real.sqrt (8 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ / (kk i : ℝ)) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < Fintype.card (gridAt i).Atom := by omega
  have hnb : 0 < nblk i t := nblk_pos ht (by omega)
  haveI : Nonempty (Fin (nblk i t)) := Fin.pos_iff_nonempty.1 hnb
  have hk0 : 0 < kk i := by omega
  have hℓP : ℓ ≤ kk i - ℓ + 1 := by omega
  have hPm : (kk i - ℓ + 1) + ℓ ≤ kk i + 1 := by omega
  have hCR : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by exact_mod_cast hC
  have hΔ0 : (0 : ℝ) < δ * (Fintype.card (gridAt i).Atom : ℝ) := by positivity
  have hΔ : (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - δ * (Fintype.card (gridAt i).Atom : ℝ) ≤ (jointLawAt i x).H₂ := by
    rw [← sub_mul]; exact hdef
  have hmain := abs_uniPosFreq_sub_le (A := (gridAt i).Atom) (B := Fin (nblk i t))
    (m := kk i) (ℓ := ℓ) (t := t) (P := kk i - ℓ + 1) hℓ ht hℓP hPm (blkSched i t)
    (blkSched_injective i t) (jointLawAt i x) w hΔ0 hΔ
  rw [freeFreq]
  refine hmain.trans ?_
  have hcf : (Fintype.card (Fin (nblk i t)) : ℝ) = ((nblk i t : ℕ) : ℝ) := by
    rw [Fintype.card_fin]
  have hbR : (0 : ℝ) < ((nblk i t : ℕ) : ℝ) := by exact_mod_cast hnb
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hkR : (0 : ℝ) < (kk i : ℝ) := by exact_mod_cast hk0
  have hPpos : 0 < kk i - ℓ + 1 := by omega
  have hPR : (0 : ℝ) < ((kk i - ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast hPpos
  have hlb : (Fintype.card (gridAt i).Atom : ℝ) ≤ 2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ) := by
    have hnat : Fintype.card (gridAt i).Atom ≤ 2 * t * nblk i t := by
      have h1 : t * nblk i t + Fintype.card (gridAt i).Atom % t
          = Fintype.card (gridAt i).Atom := by
        rw [nblk]; exact Nat.div_add_mod _ _
      have h2 : Fintype.card (gridAt i).Atom % t < t := Nat.mod_lt _ ht
      have h4 : t ≤ t * nblk i t := Nat.le_mul_of_pos_right t hnb
      have h5 : 2 * t * nblk i t = 2 * (t * nblk i t) := by ring
      omega
    exact_mod_cast hnat
  have hPlb : (kk i : ℝ) ≤ 2 * ((kk i - ℓ + 1 : ℕ) : ℝ) := by
    have : kk i ≤ 2 * (kk i - ℓ + 1) := by omega
    exact_mod_cast this
  have hstep : 2 * Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ))
      / ((Fintype.card (Fin (nblk i t)) : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ))
      ≤ 8 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ / (kk i : ℝ) := by
    rw [hcf, div_le_div_iff₀ (by positivity) hkR]
    have h1 : 2 * Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ))
        ≤ 2 * Real.log 2 * (ℓ : ℝ) * (δ * (2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ))) := by
      have h := mul_le_mul_of_nonneg_left hlb hδ.le
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : 2 * Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ))
          * (kk i : ℝ)
        ≤ 2 * Real.log 2 * (ℓ : ℝ) * (δ * (2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ)))
            * (2 * ((kk i - ℓ + 1 : ℕ) : ℝ)) :=
      mul_le_mul h1 hPlb hkR.le (by positivity)
    calc 2 * Real.log 2 * (ℓ : ℝ) * (δ * (Fintype.card (gridAt i).Atom : ℝ)) * (kk i : ℝ)
        ≤ 2 * Real.log 2 * (ℓ : ℝ) * (δ * (2 * (t : ℝ) * ((nblk i t : ℕ) : ℝ)))
            * (2 * ((kk i - ℓ + 1 : ℕ) : ℝ)) := h2
      _ = 8 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * δ
            * (((nblk i t : ℕ) : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by ring
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by positivity)

/-- **The free capacity bound for `G₄`.** -/
theorem abs_freeFreq_sub_le_primeLambertFour (i ℓ t : ℕ) (hℓ : 0 < ℓ) (ht : 0 < t)
    (hfit : 2 * ℓ ≤ kk i) (hcard : 2 * t ≤ Fintype.card (gridAt i).Atom)
    (w : Fin (2 ^ (ℓ * t))) :
    |freeFreq i ℓ t (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ (ℓ * t)|
      ≤ 2 * (t : ℝ) * Real.sqrt (1600 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by positivity
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hcardA : (Fintype.card (gridAt i).Atom : ℝ) = (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    rw [card_Atom_gridAt i]
  have hdef : ((kk i : ℝ) - 50 * Real.sqrt (KK i)) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ := by
    rw [hcardA, sub_mul]
    exact hE1.le
  refine (abs_freeFreq_sub_le_of_deficit i ℓ t hℓ ht hfit hcard _ w hδ hdef).trans ?_
  have hk0 : (0 : ℝ) < (kk i : ℝ) := by
    have : 0 < kk i := by unfold kk; omega
    exact_mod_cast this
  have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
    rw [Real.mul_self_sqrt hKpos.le]
    unfold KK; push_cast; ring
  have hstep : 8 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * (50 * Real.sqrt (KK i)) / (kk i : ℝ)
      ≤ 1600 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) / Real.sqrt (KK i) := by
    rw [div_le_div_iff₀ hk0 hS0]
    have hid : 8 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * (50 * Real.sqrt (KK i))
        * Real.sqrt ((KK i : ℕ) : ℝ)
        = 1600 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) * (kk i : ℝ) := by
      linear_combination (400 * Real.log 2 * (ℓ : ℝ) * (t : ℝ)) * hsq
    rw [hid]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by positivity)

/-- **The free frequency theorem.** -/
theorem tendsto_freeFreq_primeLambertFour (ℓ t : ℕ) (hℓ : 0 < ℓ) (ht : 0 < t)
    (w : ∀ i, Fin (2 ^ (ℓ * t))) :
    Tendsto (fun i => freeFreq i ℓ t (primeLambertAtBase 4) (w i) - 1 / (2 : ℝ) ^ (ℓ * t))
      atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinner : Tendsto (fun i => 1600 * Real.log 2 * (ℓ : ℝ) * (t : ℝ) / Real.sqrt (KK i))
      atTop (nhds 0) := by
    have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
    exact hsqrt.const_div_atTop _
  have hsq : Tendsto (fun i => 2 * (t : ℝ) * Real.sqrt (1600 * Real.log 2 * (ℓ : ℝ) * (t : ℝ)
      / Real.sqrt (KK i))) atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this.const_mul (2 * (t : ℝ))
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [eventually_ge_atTop (2 * ℓ), eventually_ge_atTop (2 * t)] with i h1 h2
  have hfit : 2 * ℓ ≤ kk i := by unfold kk; omega
  have hcard : 2 * t ≤ Fintype.card (gridAt i).Atom := by
    have := KK_le_card_Atom i
    have hKi : i ≤ KK i := by unfold KK kk; omega
    omega
  simpa [Real.norm_eq_abs] using
    abs_freeFreq_sub_le_primeLambertFour i ℓ t hℓ ht hfit hcard (w i)

/-! ### The digit rendering at unrestricted positions -/

open Classical in
/-- **The count rendering.** -/
theorem freeFreq_eq_count (i ℓ t : ℕ) (x : ℝ) (w : Fin (2 ^ (ℓ * t))) :
    freeFreq i ℓ t x w
      = (∑ b : Fin (nblk i t), ∑ pv : Fin t → Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              pvPat (kk i) ℓ t (blkSched i t) b (fun s => ((pv s : ℕ)))
                (ZVec (gridAt i) (kk i) x n) = w).card : ℝ))
        / (((PK i).card : ℝ)
            * ((Fintype.card (Fin (nblk i t)) : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ) ^ t)) := by
  classical
  have hp : ∀ (b : Fin (nblk i t)) (pv : Fin t → Fin (kk i - ℓ + 1)),
      ((jointLawAt i x).map
          (pvPat (kk i) ℓ t (blkSched i t) b (fun s => ((pv s : ℕ))))).prob {w}
        = (((PK i).filter fun n =>
              pvPat (kk i) ℓ t (blkSched i t) b (fun s => ((pv s : ℕ)))
                (ZVec (gridAt i) (kk i) x n) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro b pv
    rw [FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  have hsum : (∑ b : Fin (nblk i t), ∑ pv : Fin t → Fin (kk i - ℓ + 1),
        ((jointLawAt i x).map
          (pvPat (kk i) ℓ t (blkSched i t) b (fun s => ((pv s : ℕ))))).prob {w})
      = (∑ b : Fin (nblk i t), ∑ pv : Fin t → Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              pvPat (kk i) ℓ t (blkSched i t) b (fun s => ((pv s : ℕ)))
                (ZVec (gridAt i) (kk i) x n) = w).card : ℝ)) / ((PK i).card : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun pv _ => hp b pv
  rw [freeFreq, uniPosFreq, hsum, div_div]

open Classical in
/-- **The digit rendering.**  The event is: for every `s < t`, the `ℓ` binary digits of `x`
beginning at position `2·kIdx(n, blkSched b s) + pv s` spell the `s`-th component word — each
window's position chosen **freely and independently, with no alignment**, and the average taken
over all `(m_K − ℓ + 1)^t` such choices. -/
theorem freeFreq_eq_digits (i ℓ t : ℕ) (hℓ : 0 < ℓ) (hfit : ℓ ≤ kk i) (x : ℝ)
    (u : Fin t → Fin (2 ^ ℓ)) :
    freeFreq i ℓ t x (packFin t ℓ u)
      = (∑ b : Fin (nblk i t), ∑ pv : Fin t → Fin (kk i - ℓ + 1),
            (((PK i).filter fun n => ∀ s : Fin t,
              blockVal (Int.fract x)
                (2 * kIdx (gridAt i) n (blkSched i t b s) + (pv s : ℕ)) ℓ
                  = (u s : ℕ)).card : ℝ))
        / (((PK i).card : ℝ)
            * ((Fintype.card (Fin (nblk i t)) : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ) ^ t)) := by
  classical
  rw [freeFreq_eq_count i ℓ t x (packFin t ℓ u)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun pv _ => ?_
  congr 2
  have hfitp : ∀ s : Fin t, (pv s : ℕ) + ℓ ≤ kk i := by
    intro s
    have := (pv s).isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [pvPat_eq_pack_iff]
  have hZ : ∀ s : Fin t, ZVec (gridAt i) (kk i) x n (blkSched i t b s)
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n (blkSched i t b s)) (kk i),
          blockVal_lt _ _ _⟩ :=
    fun s => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n (blkSched i t b s))
  constructor
  · intro h s
    have hs := h s
    rw [hZ s, posAt_blockVal _ _ _ _ _ (hfitp s)] at hs
    exact congrArg Fin.val hs
  · intro h s
    rw [hZ s, posAt_blockVal _ _ _ _ _ (hfitp s)]
    exact Fin.ext (h s)

open Classical in
/-- **THE ENDPOINT, over every vector of unrestricted sampled positions.**  For every `t`, every
`ℓ`, and any binary words `v₀,…,v_{t−1}` of length `ℓ`, the proportion of triples `(n, b, pv)` —
`pv` ranging over **all** vectors of positions in `[0, m_K − ℓ + 1)^t`, with no alignment
condition whatsoever — at which, simultaneously for every `s < t`, the word `v s` occurs in the
binary expansion of `G₄` at position `2·kIdx(n, blkSched b s) + pv s`, tends to `2^{−ℓt}`.

This is the strongest form of the decorrelation statement this arithmetic supports: it drops
both the common-diagonal restriction of `tendsto_occursCountJoint_primeLambertFour` and the
`ℓ`-grid alignment of `tendsto_occursCountJointUniform_primeLambertFour`.

It is a statement about the *sampled* positions only, and is **not** a normality claim. -/
theorem tendsto_occursCountJointFree_primeLambertFour (t ℓ : ℕ) (ht : 0 < t) (hℓ : 0 < ℓ)
    (v : Fin t → List ℕ) (hlen : ∀ s, (v s).length = ℓ)
    (hv : ∀ s : Fin t, ∀ j, ∀ h : j < (v s).length, (v s)[j] < 2) :
    Tendsto (fun i =>
      (∑ b : Fin (nblk i t), ∑ pv : Fin t → Fin (kk i - ℓ + 1),
          (((PK i).filter fun n => ∀ s : Fin t,
            OccursAt 2 (primeLambertAtBase 4) (v s)
              (2 * kIdx (gridAt i) n (blkSched i t b s) + (pv s : ℕ))).card : ℝ))
        / (((PK i).card : ℝ)
            * ((Fintype.card (Fin (nblk i t)) : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ) ^ t)))
      atTop (nhds (1 / (2 : ℝ) ^ (ℓ * t))) := by
  classical
  set u : Fin t → Fin (2 ^ ℓ) := fun s =>
    ⟨wordVal (v s), by
      have := wordVal_lt (hv s)
      rw [hlen s] at this
      exact this⟩ with hu
  have hmain : Tendsto
      (fun i => freeFreq i ℓ t (primeLambertAtBase 4) (packFin t ℓ u))
      atTop (nhds (1 / (2 : ℝ) ^ (ℓ * t))) := by
    have := tendsto_freeFreq_primeLambertFour ℓ t hℓ ht (fun _ => packFin t ℓ u)
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ) / (2 : ℝ) ^ (ℓ * t)) atTop
        (nhds (1 / (2 : ℝ) ^ (ℓ * t))) := tendsto_const_nhds
    simpa using this.add hlim
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop ℓ] with i hi
  have hfit : ℓ ≤ kk i := by unfold kk; omega
  rw [freeFreq_eq_digits i ℓ t hℓ hfit _ u]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun pv _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  constructor
  · intro h s
    have hb := blockVal_eq_wordVal_iff (y := primeLambertAtBase 4)
      (p := 2 * kIdx (gridAt i) n (blkSched i t b s) + (pv s : ℕ)) (hv s)
    rw [hlen s] at hb
    exact hb.1 (h s)
  · intro h s
    have hb := blockVal_eq_wordVal_iff (y := primeLambertAtBase 4)
      (p := 2 * kIdx (gridAt i) n (blkSched i t b s) + (pv s : ℕ)) (hv s)
    rw [hlen s] at hb
    exact hb.2 (h s)

end NormalNumbers.G4.Sched
