/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyFamily

/-!
# Entropy expedition §6, positive branch: the whole admissible class, across all scales

Lap 11 (`Sched.not_dense_of_scale`) closed the averaging repair at a *fixed* scale: every grid
with scale parameters `(Q_K, D₀_K, U_K)` has its multipliers in one progression of `U+1` values,
so any family at that scale reads at most `L/8` of every prefix.

What remains is the brief's direction 2: use *different scales*.  Across scales the multipliers
really do move, so a genuinely new estimate is needed.  This module supplies it.

The per-scale weight is

  `w(K,N) = (U+1)·m / (2·(1 + Q·D₀))`,  `U = gridUmax K N`, `Q = gridQ K N`, `D₀ = K·U`,

and the two facts that close the question are

* `weight_le_inv_pow`: `w(K,N) ≤ (4(K+N))^{-K}` — because `Q ≥ U`, `D₀ = K U`, `m ≤ K` give
  `w ≤ 1/U`, and `U ≥ B^K ≥ (4(K+N))^K` for `K ≥ 2`;
* `sum_weight_le`: `Σ_{K ≥ 2} Σ_{M ≥ 2} (4M)^{-K} ≤ 1/8` — a double geometric/`1/M²` series.

Hence **no family of admissible samplers, over any set of scales, reads half the digit
positions**, and by `G4EntropyBarrier` no statement about any such sample can imply normality.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4

variable {ι : Type*} [DecidableEq ι]

/-! ### Counting across a finite set of scales -/

/-- The multiplier lower bound at scale `(K,N)`. -/
def scaleDmin (K N : ℕ) : ℕ := 1 + gridQ K N * gridD₀ K N

lemma scaleDmin_pos (K N : ℕ) : 0 < scaleDmin K N := by unfold scaleDmin; omega

/-- **The count across scales.**  Every position read below `L` by a family of grids, each
carrying the schedule's parameters at one of the scales in `S`, is counted by the multiplier
progressions of those scales — with no reference to the family. -/
theorem card_filter_le_of_scales (S : Finset ℕ) (nn mm XX : ℕ → ℕ)
    (F : Finset ι) (G : ι → GridParams) (sc : ι → ℕ)
    (U' : ℕ → Prop) [DecidablePred U'] {L : ℕ}
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hsc : ∀ ν ∈ F, sc ν ∈ S)
    (hQ : ∀ ν ∈ F, (G ν).Q = gridQ (sc ν) (nn (sc ν)))
    (hD₀ : ∀ ν ∈ F, (G ν).D₀ = gridD₀ (sc ν) (nn (sc ν)))
    (hU : ∀ ν ∈ F, (G ν).U = gridUmax (sc ν) (nn (sc ν)))
    (hcov : ∀ j, j < L → U' j →
      ∃ ν ∈ F, j ∈ sampledPos (G ν) (XX (sc ν)) (mm (sc ν))) :
    ((Finset.range L).filter U').card
      ≤ ∑ K ∈ S, (gridUmax K (nn K) + 1) * ((L / (2 * scaleDmin K (nn K))) * mm K) := by
  classical
  have hsub : (Finset.range L).filter U' ⊆
      S.biUnion (fun K => (multSet (gridQ K (nn K)) (gridD₀ K (nn K))
        (gridUmax K (nn K))).biUnion (fun d => periodCol d (mm K) L)) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨ν, hν, hjν⟩ := hcov j hj.1 hj.2
    obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (G ν)).1 hjν
    obtain ⟨c, hc1, hc⟩ := exists_kIdx_eq (G ν) (hT ν hν) hn α
    have hd : (G ν).d α ∈ multSet (gridQ (sc ν) (nn (sc ν))) (gridD₀ (sc ν) (nn (sc ν)))
        (gridUmax (sc ν) (nn (sc ν))) := by
      have := d_mem_multSet (G ν) α
      rwa [hQ ν hν, hD₀ ν hν, hU ν hν] at this
    refine Finset.mem_biUnion.2 ⟨sc ν, hsc ν hν, Finset.mem_biUnion.2 ⟨(G ν).d α, hd, ?_⟩⟩
    rw [hc] at hj ⊢
    exact mem_periodCol ((G ν).d_pos α) hc1 hh hj.1
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_sum fun K _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun d _ => card_periodCol_le d (mm K) L)) ?_
  have hstep : ∀ d ∈ multSet (gridQ K (nn K)) (gridD₀ K (nn K)) (gridUmax K (nn K)),
      (L / (2 * d)) * mm K ≤ (L / (2 * scaleDmin K (nn K))) * mm K := by
    intro d hd
    refine Nat.mul_le_mul_right _ (Nat.div_le_div_left ?_
      (by have := scaleDmin_pos K (nn K); omega))
    exact Nat.mul_le_mul_left 2 (le_of_mem_multSet hd)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_multSet_le _ _ _)

/-! ### The density weight of a scale, and its sum over all scales -/

/-- The fraction of positions the scale-`K` samplers can read. -/
noncomputable def scaleWeight (nn mm : ℕ → ℕ) (K : ℕ) : ℝ :=
  ((gridUmax K (nn K) : ℝ) + 1) * (mm K : ℝ) / (2 * (scaleDmin K (nn K) : ℝ))

lemma scaleWeight_nonneg (nn mm : ℕ → ℕ) (K : ℕ) : 0 ≤ scaleWeight nn mm K := by
  unfold scaleWeight
  have h : (0 : ℝ) < 2 * (scaleDmin K (nn K) : ℝ) := by
    have := scaleDmin_pos K (nn K)
    have : (0 : ℝ) < (scaleDmin K (nn K) : ℝ) := by exact_mod_cast this
    linarith
  positivity

lemma four_le_gridB {K N : ℕ} (hK : 2 ≤ K) : 4 ≤ gridB K N := by
  unfold gridB
  nlinarith

/-- **The per-scale weight bound**: a scale-`K` sampler family reads at most `4^{-K}` of the
positions.  The three inputs are `Q ≥ U`, `D₀ = K·U` and `U ≥ B^K ≥ 4^K`. -/
lemma scaleWeight_le (nn mm : ℕ → ℕ) {K : ℕ} (hK : 2 ≤ K) (hm : mm K ≤ K) :
    scaleWeight nn mm K ≤ 1 / (4 : ℝ) ^ K := by
  set N := nn K with hN
  set U := gridUmax K N with hU
  have hK1 : 1 ≤ K := by omega
  have h4U : (4 : ℕ) ^ K ≤ U := by
    calc (4 : ℕ) ^ K ≤ gridB K N ^ K := Nat.pow_le_pow_left (four_le_gridB hK) K
      _ ≤ U := NormalNumbers.G4.Sched.pow_le_gridUmax hK1
  have hU2 : 2 ≤ U := by
    have : (4 : ℕ) ^ 1 ≤ 4 ^ K := Nat.pow_le_pow_right (by omega) hK1
    simp only [pow_one] at this
    omega
  have hQU : U ≤ gridQ K N := by have := gridQ_gt K N; omega
  have hD₀ : gridD₀ K N = K * U := rfl
  -- reals
  have hUR : (2 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU2
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hmR : (mm K : ℝ) ≤ (K : ℝ) := by exact_mod_cast hm
  have hdm : (K : ℝ) * (U : ℝ) * (U : ℝ) ≤ (scaleDmin K N : ℝ) := by
    have hnat : K * U * U ≤ scaleDmin K N := by
      unfold scaleDmin
      rw [hD₀]
      have : U * (K * U) ≤ gridQ K N * (K * U) := Nat.mul_le_mul_right _ hQU
      calc K * U * U = U * (K * U) := by ring
        _ ≤ gridQ K N * (K * U) := this
        _ ≤ 1 + gridQ K N * (K * U) := by omega
    exact_mod_cast hnat
  have hdmpos : (0 : ℝ) < 2 * (scaleDmin K N : ℝ) := by
    have h := scaleDmin_pos K N
    have : (0 : ℝ) < (scaleDmin K N : ℝ) := by exact_mod_cast h
    linarith
  have hstep : scaleWeight nn mm K ≤ 1 / (U : ℝ) := by
    unfold scaleWeight
    rw [div_le_div_iff₀ hdmpos (by linarith)]
    have hUpos : (0 : ℝ) ≤ (U : ℝ) := by linarith
    have hKpos : (0 : ℝ) ≤ (K : ℝ) := by linarith
    have hA : ((U : ℝ) + 1) * (mm K : ℝ) * (U : ℝ) ≤ ((U : ℝ) + 1) * (K : ℝ) * (U : ℝ) := by
      have h0 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (U : ℝ) + 1) hUpos)
        (by linarith : (0:ℝ) ≤ (K : ℝ) - (mm K : ℝ))
      linarith [h0]
    have hB : ((U : ℝ) + 1) * (K : ℝ) * (U : ℝ) ≤ 2 * ((K : ℝ) * (U : ℝ) * (U : ℝ)) := by
      have h0 := mul_nonneg (mul_nonneg hKpos hUpos) (by linarith : (0:ℝ) ≤ (U : ℝ) - 1)
      linarith [h0]
    linarith
  refine le_trans hstep ?_
  have h4 : (4 : ℝ) ^ K ≤ (U : ℝ) := by exact_mod_cast h4U
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ K := by positivity
  exact one_div_le_one_div_of_le h4pos h4

/-- **The sum over all scales**: distinct scales `K ≥ 2` contribute at most `1/12` in total. -/
lemma sum_inv_four_pow_le (S : Finset ℕ) (hS : ∀ K ∈ S, 2 ≤ K) :
    ∑ K ∈ S, 1 / (4 : ℝ) ^ K ≤ 1 / 12 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, ∀ K ∈ S, K - 2 < n := by
    refine ⟨(S.sup id) + 1, fun K hK => ?_⟩
    have : K ≤ S.sup id := Finset.le_sup (f := id) hK
    omega
  have hinj : ∀ x ∈ S, ∀ y ∈ S, x - 2 = y - 2 → x = y := by
    intro x hx y hy h
    have := hS x hx; have := hS y hy; omega
  have hrw : ∑ K ∈ S, 1 / (4 : ℝ) ^ K
      = ∑ j ∈ S.image (fun K => K - 2), (1 / 16) * (1 / (4 : ℝ) ^ j) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun K hK => ?_
    have h2 : 2 ≤ K := hS K hK
    have : K = (K - 2) + 2 := by omega
    rw [this]
    rw [pow_add]
    norm_num
  rw [hrw]
  have hsub : S.image (fun K => K - 2) ⊆ Finset.range n := by
    intro j hj
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (hn K hK)
  have hnn : ∀ j ∈ Finset.range n, (0 : ℝ) ≤ (1 / 16) * (1 / (4 : ℝ) ^ j) := by
    intro j _; positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn j hj)) ?_
  have hgeom : ∑ j ∈ Finset.range n, (1 / (4 : ℝ) ^ j) ≤ 4 / 3 := by
    have hr : ∑ j ∈ Finset.range n, ((1 : ℝ) / 4) ^ j ≤ 4 / 3 := by
      have hsum : ∑ j ∈ Finset.range n, ((1 : ℝ) / 4) ^ j
          = (1 - (1 / 4 : ℝ) ^ n) / (1 - 1 / 4) := by
        rw [geom_sum_eq (by norm_num)]
        field_simp
        ring
      rw [hsum]
      have hpow : (0 : ℝ) < (1 / 4 : ℝ) ^ n := by positivity
      rw [div_le_iff₀ (by norm_num)]
      linarith
    calc ∑ j ∈ Finset.range n, (1 / (4 : ℝ) ^ j)
        = ∑ j ∈ Finset.range n, ((1 : ℝ) / 4) ^ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [div_pow]; norm_num
      _ ≤ 4 / 3 := hr
  rw [← Finset.mul_sum]
  linarith

/-- **The total weight of any set of distinct scales `K ≥ 2` is at most `1/12`.** -/
theorem sum_scaleWeight_le (nn mm : ℕ → ℕ) (S : Finset ℕ) (hS : ∀ K ∈ S, 2 ≤ K)
    (hm : ∀ K ∈ S, mm K ≤ K) :
    ∑ K ∈ S, scaleWeight nn mm K ≤ 1 / 12 :=
  le_trans (Finset.sum_le_sum fun K hK => scaleWeight_le nn mm (hS K hK) (hm K hK))
    (sum_inv_four_pow_le S hS)

/-! ### The conclusion: no admissible sampler family, over any scales, is dense -/

/-- **The density bound across all scales.**  Whatever the family, whatever the set of distinct
scales it uses, the digit positions it reads below `L` number at most `L/12`. -/
theorem card_le_of_scales (S : Finset ℕ) (nn mm XX : ℕ → ℕ)
    (F : Finset ι) (G : ι → GridParams) (sc : ι → ℕ)
    (U' : ℕ → Prop) [DecidablePred U'] {L : ℕ}
    (hS : ∀ K ∈ S, 2 ≤ K) (hmle : ∀ K ∈ S, mm K ≤ K)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hsc : ∀ ν ∈ F, sc ν ∈ S)
    (hQ : ∀ ν ∈ F, (G ν).Q = gridQ (sc ν) (nn (sc ν)))
    (hD₀ : ∀ ν ∈ F, (G ν).D₀ = gridD₀ (sc ν) (nn (sc ν)))
    (hU : ∀ ν ∈ F, (G ν).U = gridUmax (sc ν) (nn (sc ν)))
    (hcov : ∀ j, j < L → U' j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (XX (sc ν)) (mm (sc ν))) :
    ((((Finset.range L).filter U').card : ℝ)) ≤ (1 / 12) * L := by
  have hnat := card_filter_le_of_scales S nn mm XX F G sc U' hT hsc hQ hD₀ hU hcov
  have hcast : ((((Finset.range L).filter U').card : ℕ) : ℝ)
      ≤ ∑ K ∈ S, (((gridUmax K (nn K) + 1) * ((L / (2 * scaleDmin K (nn K))) * mm K) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hnat
  refine le_trans hcast ?_
  have hterm : ∀ K ∈ S,
      (((gridUmax K (nn K) + 1) * ((L / (2 * scaleDmin K (nn K))) * mm K) : ℕ) : ℝ)
        ≤ scaleWeight nn mm K * L := by
    intro K _
    have hdpos : (0 : ℝ) < 2 * (scaleDmin K (nn K) : ℝ) := by
      have h := scaleDmin_pos K (nn K)
      have : (0 : ℝ) < (scaleDmin K (nn K) : ℝ) := by exact_mod_cast h
      linarith
    have hdiv : (((L / (2 * scaleDmin K (nn K)) : ℕ)) : ℝ)
        ≤ (L : ℝ) / (2 * (scaleDmin K (nn K) : ℝ)) := by
      have := Nat.cast_div_le (α := ℝ) (m := L) (n := 2 * scaleDmin K (nn K))
      push_cast at this ⊢
      exact this
    have hU1 : (0 : ℝ) ≤ (gridUmax K (nn K) : ℝ) + 1 := by positivity
    have hm1 : (0 : ℝ) ≤ (mm K : ℝ) := Nat.cast_nonneg _
    push_cast
    unfold scaleWeight
    rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
    have hmul : ((gridUmax K (nn K) : ℝ) + 1) * ((((L / (2 * scaleDmin K (nn K)) : ℕ)) : ℝ)
        * (mm K : ℝ)) * (2 * (scaleDmin K (nn K) : ℝ))
          ≤ ((gridUmax K (nn K) : ℝ) + 1) * (((L : ℝ) / (2 * (scaleDmin K (nn K) : ℝ)))
        * (mm K : ℝ)) * (2 * (scaleDmin K (nn K) : ℝ)) := by
      have hstep : (((L / (2 * scaleDmin K (nn K)) : ℕ)) : ℝ) * (mm K : ℝ)
          ≤ ((L : ℝ) / (2 * (scaleDmin K (nn K) : ℝ))) * (mm K : ℝ) :=
        mul_le_mul_of_nonneg_right hdiv hm1
      have h2 : (0 : ℝ) ≤ 2 * (scaleDmin K (nn K) : ℝ) := le_of_lt hdpos
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hU1) h2
    refine le_trans hmul (le_of_eq ?_)
    have hne : (scaleDmin K (nn K) : ℝ) ≠ 0 := by
      have h := scaleDmin_pos K (nn K)
      have : (0 : ℝ) < (scaleDmin K (nn K) : ℝ) := by exact_mod_cast h
      exact ne_of_gt this
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (sum_scaleWeight_le nn mm S hS hmle) hL

/-- **No admissible sampler family, over any set of scales, reads half the positions.** -/
theorem not_dense_of_scales (S : Finset ℕ) (nn mm XX : ℕ → ℕ)
    (F : Finset ι) (G : ι → GridParams) (sc : ι → ℕ)
    (U' : ℕ → Prop) [DecidablePred U'] {L : ℕ} (hL : 0 < L)
    (hS : ∀ K ∈ S, 2 ≤ K) (hmle : ∀ K ∈ S, mm K ≤ K)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hsc : ∀ ν ∈ F, sc ν ∈ S)
    (hQ : ∀ ν ∈ F, (G ν).Q = gridQ (sc ν) (nn (sc ν)))
    (hD₀ : ∀ ν ∈ F, (G ν).D₀ = gridD₀ (sc ν) (nn (sc ν)))
    (hU : ∀ ν ∈ F, (G ν).U = gridUmax (sc ν) (nn (sc ν)))
    (hcov : ∀ j, j < L → U' j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (XX (sc ν)) (mm (sc ν))) :
    ¬ (L ≤ 2 * ((Finset.range L).filter U').card) := by
  intro hdense
  have h := card_le_of_scales S nn mm XX F G sc U' hS hmle hT hsc hQ hD₀ hU hcov
  have hdR : (L : ℝ) ≤ 2 * ((((Finset.range L).filter U').card : ℕ) : ℝ) := by
    exact_mod_cast hdense
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  linarith

end NormalNumbers.G4Entropy
