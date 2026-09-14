/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWord
import NormalNumbers.G4EntropyTransfer

/-!
# Brief §5, done right: the sampled-window word frequencies of `G₄`

Lap 15 recorded §5 negatively, but what it proved (`entropy_rate_not_control_bit`) is that a
near-maximal entropy rate does not pin the frequency of a word at a **fixed offset** inside the
sampled window — the uniform law on the leading-bit-zero half has rate `(m−1)/m` and kills the
leading bit.  Normality counts a word's occurrences **averaged over the offsets**, and on that
very witness the averaged `1`-frequency is `(m−1)/(2m) → 1/2`, i.e. correct.

Entropy *does* control the averaged frequency, and this module proves it for `G₄`.

* `abs_avg_block_prob_sub_le` — abstract: a joint law within `Δ` of the maximal entropy
  `m·|A|` on `A → Fin (2^m)` has its `ℓ`-block word probabilities averaging to within
  `2 log 2·(|A|ℓ + Δ)/(2tN) + t/2` of `2^{−ℓ}`, for every `t > 0`.  Gibbs + subadditivity
  (`G4EntropyGibbs`) + the Hellinger bound (`G4EntropyPinsker`) + AM-GM (`G4EntropyWord`).
* `abs_blockFreq_sub_le` — at the implemented schedule, with `Δ` supplied by `entropy_E1`:

      `|blockFreq i ℓ G₄ w − 2^{−ℓ}| ≤ log 2·(ℓ + 50√K)/(t·(m_K/ℓ + 1)) + t/2`.

* `tendsto_blockFreq_primeLambertFour` — **the theorem**: for every fixed binary word `w`,

      `blockFreq i ℓ G₄ w → 2^{−|w|}`.

`blockFreq i ℓ x w` is the honest count: the density, over one uniform `n ∈ P_K`, over the grid
atoms `α`, and over the `m_K/ℓ + 1` block positions `j`, of the event that the `j`-th `ℓ`-block
of the window of `x` at digit position `2·kIdx(n,α)` spells `w` (`map_empirical_p` turns each
marginal's mass into that count, and `blkAt_blockVal` says the block IS the `ℓ`-bit window of
`x` at `2·kIdx + jℓ`).

**This is not a normality claim and does not imply one.**  The positions read here have density
zero (laps 9–22 of the expedition), and `not_T_E` exhibits a non-normal number with literally
the same joint law at every scale — hence with literally these same block frequencies.  What is
new is that the expedition's entropy theorem is not merely a richness statement: it pins every
finite word's frequency on the sampled system, which `isDisjunctive_two` (occurrence only) does
not.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

/-! ### The abstract averaged-frequency bound -/

/-- **Abstract form.**  A joint entropy within `Δ` of the maximum forces the `ℓ`-block word
probabilities, averaged over all coordinates and block positions, to within
`2 log 2 (|A|ℓ + Δ)/(2tN) + t/2` of `2^{−ℓ}`, for every `t > 0`. -/
theorem abs_avg_block_prob_sub_le {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    {m ℓ : ℕ} (hℓ : 0 < ℓ) (L : FinLaw (A → Fin (2 ^ m))) (w : Fin (2 ^ ℓ)) {Δ t : ℝ}
    (hΔ : (m : ℝ) * (Fintype.card A : ℝ) - Δ ≤ L.H₂) (ht : 0 < t) :
    |(∑ c : A × Fin (m / ℓ + 1), (L.map (blkCoord m ℓ c)).prob {w})
        / (Fintype.card (A × Fin (m / ℓ + 1)) : ℝ) - 1 / (2 : ℝ) ^ ℓ|
      ≤ (2 * Real.log 2 * ((Fintype.card A : ℝ) * (ℓ : ℝ) + Δ))
          / (2 * t * (Fintype.card (A × Fin (m / ℓ + 1)) : ℝ)) + t / 2 := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hι : 0 < Fintype.card (A × Fin (m / ℓ + 1)) := Fintype.card_pos
  refine abs_avg_sub_le hι
    (fun c => (L.map (blkCoord m ℓ c)).prob {w})
    (fun c => 2 * Real.log 2 * ((ℓ : ℝ) - (L.map (blkCoord m ℓ c)).H₂))
    (1 / (2 : ℝ) ^ ℓ)
    (2 * Real.log 2 * ((Fintype.card A : ℝ) * (ℓ : ℝ) + Δ)) t ?_ ?_ ?_ ht
  · intro c
    have h := H₂_le_of_block (L.map (blkCoord m ℓ c))
    nlinarith [hlog2, h]
  · intro c
    exact abs_prob_singleton_sub_le hℓ _ w
  · have hsum := sum_block_deficit_le (A := A) (ℓ := ℓ) hℓ L hΔ
    rw [← Finset.mul_sum]
    nlinarith [hlog2, hsum]

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The sampled block frequency of a word -/

/-- **The frequency of the word `w` among the `ℓ`-blocks of the scale-`i` sampled windows.**

Averaged over one uniform `n ∈ P_K`, over the grid atoms `α`, and over the `m_K/ℓ + 1` block
positions `j`.  By `map_empirical_p` and `blkAt_blockVal` this is exactly the density of the
triples `(n, α, j)` for which the `ℓ` binary digits of `x` at positions
`2·kIdx(n,α) + jℓ, …, +jℓ+ℓ−1` spell `w`. -/
noncomputable def blockFreq (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) : ℝ :=
  (∑ c : (gridAt i).Atom × Fin (kk i / ℓ + 1),
      ((jointLawAt i x).map (blkCoord (kk i) ℓ c)).prob {w})
    / (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ + 1)) : ℝ)

/-- **The quantitative statement.**  `entropy_E1`'s deficit `50√K·H_K` against the maximal
`m_K·H_K` gives, for every `t > 0`,

    `|blockFreq i ℓ G₄ w − 2^{−ℓ}| ≤ log 2·(ℓ + 50√K)/(t·(m_K/ℓ + 1)) + t/2`. -/
theorem abs_blockFreq_sub_le (i ℓ : ℕ) (hℓ : 0 < ℓ) (w : Fin (2 ^ ℓ)) {t : ℝ} (ht : 0 < t) :
    |blockFreq i ℓ (primeLambertAtBase 4) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ Real.log 2 * ((ℓ : ℝ) + 50 * Real.sqrt (KK i))
          / (t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ)) + t / 2 := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hE1 := entropy_E1 (K := KK i) (k₄ := kk i) rfl (KK_ge i)
  have hcard : (Fintype.card (gridAt i).Atom : ℝ) = (((KK i ^ 2 + 1) ^ KK i : ℕ) : ℝ) := by
    rw [card_Atom_gridAt i]
  have hcard0 : (0 : ℝ) < (Fintype.card (gridAt i).Atom : ℝ) := by
    rw [hcard]
    have : 0 < (KK i ^ 2 + 1) ^ KK i := Nat.pow_pos (by omega)
    exact_mod_cast this
  have hΔ : (kk i : ℝ) * (Fintype.card (gridAt i).Atom : ℝ)
      - 50 * Real.sqrt (KK i) * (Fintype.card (gridAt i).Atom : ℝ)
      ≤ (jointLawAt i (primeLambertAtBase 4)).H₂ := by
    rw [hcard]
    exact hE1.le
  have hmain := abs_avg_block_prob_sub_le (A := (gridAt i).Atom) (m := kk i) (ℓ := ℓ)
    hℓ (jointLawAt i (primeLambertAtBase 4)) w hΔ ht
  refine hmain.trans_eq ?_
  congr 1
  have hprod : (Fintype.card ((gridAt i).Atom × Fin (kk i / ℓ + 1)) : ℝ)
      = (Fintype.card (gridAt i).Atom : ℝ) * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) := by
    simp [Fintype.card_prod]
  rw [hprod]
  have hD0 : (0 : ℝ) < (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) := by positivity
  field_simp

/-! ### The limit -/

private lemma tendsto_freq_error (ℓ : ℕ) (hℓ : 0 < ℓ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun i => Real.log 2 * ((ℓ : ℝ) + 50 * Real.sqrt (KK i))
      / (t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ))) atTop (nhds 0) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  refine squeeze_zero
    (g := fun i => (4 * Real.log 2 * (ℓ : ℝ) ^ 2 / t) / (KK i : ℝ)
      + (200 * Real.log 2 * (ℓ : ℝ) / t) / Real.sqrt (KK i))
    (fun i => ?_) (fun i => ?_) ?_
  · have h1 : (0 : ℝ) ≤ Real.log 2 * ((ℓ : ℝ) + 50 * Real.sqrt (KK i)) := by
      have := Real.sqrt_nonneg ((KK i : ℕ) : ℝ)
      nlinarith [hlog2]
    have h2 : (0 : ℝ) < t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) := by positivity
    exact div_nonneg h1 h2.le
  · have hKpos : (0 : ℝ) < (KK i : ℝ) := by
      have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
      linarith
    set S : ℝ := Real.sqrt ((KK i : ℕ) : ℝ) with hSdef
    have hS0 : 0 < S := Real.sqrt_pos.2 hKpos
    have hKS : (KK i : ℝ) = S * S := (Real.mul_self_sqrt hKpos.le).symm
    have hnum : (0 : ℝ) ≤ Real.log 2 * ((ℓ : ℝ) + 50 * S) := by nlinarith [hlog2, hS0]
    -- the block count `m_K/ℓ + 1` exceeds `K/(4ℓ)`
    have hDlb : (KK i : ℝ) / (4 * (ℓ : ℝ)) ≤ (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) := by
      have hnat : kk i < (kk i / ℓ + 1) * ℓ := by
        have h1 := Nat.div_add_mod (kk i) ℓ
        have h2 : kk i % ℓ < ℓ := Nat.mod_lt _ hℓ
        have h3 : (kk i / ℓ + 1) * ℓ = ℓ * (kk i / ℓ) + ℓ := by ring
        omega
      have hR : (kk i : ℝ) < (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) * (ℓ : ℝ) := by
        exact_mod_cast hnat
      have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
      rw [hkk4, div_le_iff₀ (by positivity)]
      linarith
    have hpos1 : (0 : ℝ) < t * ((KK i : ℝ) / (4 * (ℓ : ℝ))) := by positivity
    have hmono : t * ((KK i : ℝ) / (4 * (ℓ : ℝ)))
        ≤ t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hDlb ht.le
    calc Real.log 2 * ((ℓ : ℝ) + 50 * S) / (t * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ))
        ≤ Real.log 2 * ((ℓ : ℝ) + 50 * S) / (t * ((KK i : ℝ) / (4 * (ℓ : ℝ)))) :=
          div_le_div_of_nonneg_left hnum hpos1 hmono
      _ = (4 * Real.log 2 * (ℓ : ℝ) ^ 2 / t) / (KK i : ℝ)
            + (200 * Real.log 2 * (ℓ : ℝ) / t) / S := by
          rw [hKS]
          field_simp
          ring
  · have h1 : Tendsto (fun i => (4 * Real.log 2 * (ℓ : ℝ) ^ 2 / t) / (KK i : ℝ))
        atTop (nhds 0) := tendsto_KK_atTop.const_div_atTop _
    have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
    have h2 : Tendsto (fun i => (200 * Real.log 2 * (ℓ : ℝ) / t) / Real.sqrt (KK i))
        atTop (nhds 0) := hsqrt.const_div_atTop _
    simpa using h1.add h2

/-- **The theorem.**  For every fixed binary word `w`, the frequency of `w` among the
`ℓ`-aligned blocks of the sampled windows of `G₄ = ∑_p 1/(4^p − 1)` tends to `2^{−ℓ}`.

Unconditional, and strictly stronger on this system than `isDisjunctive_two`, which gives
occurrence but no frequency.  **Not** a normality statement: the sampled positions have density
zero, and `not_T_E`'s witness has exactly these same block frequencies. -/
theorem tendsto_blockFreq_primeLambertFour (ℓ : ℕ) (hℓ : 0 < ℓ) (w : Fin (2 ^ ℓ)) :
    Tendsto (fun i => blockFreq i ℓ (primeLambertAtBase 4) w) atTop
      (nhds (1 / (2 : ℝ) ^ ℓ)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have ht : (0 : ℝ) < η / 2 := by linarith
  have herr := tendsto_freq_error ℓ hℓ ht
  rw [Metric.tendsto_atTop] at herr
  obtain ⟨N, hN⟩ := herr (η / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  have h1 := abs_blockFreq_sub_le i ℓ hℓ w ht
  have h2 := hN i hi
  rw [Real.dist_eq, sub_zero] at h2
  have h3 : Real.log 2 * ((ℓ : ℝ) + 50 * Real.sqrt (KK i))
      / ((η / 2) * (((kk i / ℓ : ℕ) + 1 : ℕ) : ℝ)) < η / 2 :=
    lt_of_abs_lt h2
  rw [Real.dist_eq]
  linarith [h1, h3]

end NormalNumbers.G4.Sched
