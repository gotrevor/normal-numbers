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
