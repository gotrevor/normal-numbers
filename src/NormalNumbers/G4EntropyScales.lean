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

/-! ## The two-parameter family: many layer counts per scale

`not_dense_of_scales` fixes one layer count `nn K` per scale.  The full `GridParams` interface
allows a grid at scale `K` with any `N`, and then `B`, `U`, `Q`, `D₀` all change.  The weight of
the scale `(K,N)` is still at most `(4(K+N))^{-K}`, so what is needed is the convergent double
series

  `Σ_{K ≥ 2} Σ_{M ≥ 2} (4M)^{-K} ≤ Σ_{M ≥ 2} 2·(4M)^{-2} = Σ_{M ≥ 2} 1/(8M²) ≤ 1/8`.

Both halves are proved here: a geometric tail bound uniform in the ratio, and `Σ 1/M² ≤ 1` by
telescoping.  The conclusion `not_dense_of_scalePairs` removes the last restriction: **no family
of grids carrying the schedule's parameter functions, at any set of scales `(K,N)` whatsoever,
reads half of any prefix.**
-/

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4 Finset

/-- A geometric tail from exponent `2`, uniform in the ratio. -/
lemma sum_pow_Icc_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (T : Finset ℕ)
    (hT : ∀ K ∈ T, 2 ≤ K) : ∑ K ∈ T, r ^ K ≤ 2 * r ^ 2 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, ∀ K ∈ T, K - 2 < n := by
    refine ⟨(T.sup id) + 1, fun K hK => ?_⟩
    have : K ≤ T.sup id := Finset.le_sup (f := id) hK
    omega
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x - 2 = y - 2 → x = y := by
    intro x hx y hy h
    have := hT x hx; have := hT y hy; omega
  have hrw : ∑ K ∈ T, r ^ K = ∑ j ∈ T.image (fun K => K - 2), r ^ 2 * r ^ j := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun K hK => ?_
    have h2 : 2 ≤ K := hT K hK
    rw [← pow_add]
    congr 1
    omega
  rw [hrw]
  have hsub : T.image (fun K => K - 2) ⊆ Finset.range n := by
    intro j hj
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (hn K hK)
  have hnn : ∀ j ∈ Finset.range n, (0 : ℝ) ≤ r ^ 2 * r ^ j := by
    intro j _; positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn j hj)) ?_
  rw [← Finset.mul_sum]
  have hgeom : ∑ j ∈ Finset.range n, r ^ j ≤ 2 := by
    have hmul := geom_sum_mul r n
    have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, r ^ j :=
      Finset.sum_nonneg fun j _ => by positivity
    have hrn : (0 : ℝ) ≤ r ^ n := by positivity
    nlinarith [hmul, hS0, hrn]
  have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  nlinarith [hgeom, hr2]

/-- `Σ_{M=2}^{n} 1/M² ≤ 1 − 1/n`, by telescoping `1/M² ≤ 1/(M−1) − 1/M`. -/
lemma sum_inv_sq_le_aux : ∀ n : ℕ, 1 ≤ n →
    ∑ M ∈ Finset.Icc 2 n, (1 : ℝ) / (M : ℝ) ^ 2 ≤ 1 - 1 / (n : ℝ) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    have hIcc : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (n + 1) ∉ Finset.Icc 2 n := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hprev := ih hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1R : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
    have hkey : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      rw [div_sub_div _ _ (ne_of_gt hnR) (ne_of_gt hn1R), div_le_div_iff₀ (by positivity)
        (by positivity)]
      ring_nf
      nlinarith
    push_cast
    linarith

lemma sum_inv_sq_le (n : ℕ) : ∑ M ∈ Finset.Icc 2 n, (1 : ℝ) / (M : ℝ) ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := sum_inv_sq_le_aux n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  linarith

/-- **The double series.**  Over any finite set of distinct pairs `(K,M)` with `K, M ≥ 2`,
`Σ (4M)^{-K} ≤ 1/8`. -/
theorem sum_double_le (T : Finset (ℕ × ℕ)) (hT : ∀ q ∈ T, 2 ≤ q.1 ∧ 2 ≤ q.2) :
    ∑ q ∈ T, 1 / ((4 * q.2 : ℝ)) ^ q.1 ≤ 1 / 8 := by
  classical
  set a := T.sup (fun q => q.1) with ha
  set b := T.sup (fun q => q.2) with hb
  have hsub : T ⊆ (Finset.Icc 2 a) ×ˢ (Finset.Icc 2 b) := by
    intro q hq
    refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨(hT q hq).1, ?_⟩,
      Finset.mem_Icc.2 ⟨(hT q hq).2, ?_⟩⟩
    · exact Finset.le_sup (f := fun q => q.1) hq
    · exact Finset.le_sup (f := fun q => q.2) hq
  have hnn : ∀ q ∈ (Finset.Icc 2 a) ×ˢ (Finset.Icc 2 b), (0 : ℝ) ≤ 1 / ((4 * q.2 : ℝ)) ^ q.1 := by
    intro q hq
    have h2 : 2 ≤ q.2 := (Finset.mem_Icc.1 (Finset.mem_product.1 hq).2).1
    have : (0 : ℝ) ≤ (4 * q.2 : ℝ) := by positivity
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ => hnn q hq)) ?_
  rw [Finset.sum_product_right]
  have hinner : ∀ M ∈ Finset.Icc 2 b,
      ∑ K ∈ Finset.Icc 2 a, 1 / ((4 * M : ℝ)) ^ K ≤ (1 / 8) * (1 / (M : ℝ) ^ 2) := by
    intro M hM
    have hM2 : 2 ≤ M := (Finset.mem_Icc.1 hM).1
    have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    set r : ℝ := 1 / (4 * M) with hr
    have hr0 : 0 ≤ r := by rw [hr]; positivity
    have hrle : r ≤ 1 / 2 := by
      rw [hr, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hrw : ∀ K : ℕ, 1 / ((4 * M : ℝ)) ^ K = r ^ K := by
      intro K; rw [hr, div_pow, one_pow]
    simp only [hrw]
    refine le_trans (sum_pow_Icc_le hr0 hrle _ (fun K hK => (Finset.mem_Icc.1 hK).1)) ?_
    rw [hr]
    have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
    refine le_of_eq ?_
    field_simp
    ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  have := sum_inv_sq_le b
  linarith

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4 Finset

variable {ι : Type*} [DecidableEq ι]

/-! ### Counting over an arbitrary set of scale pairs `(K,N)` -/

/-- The count across a finite set of scale *pairs*. -/
theorem card_filter_le_of_scalePairs (S : Finset (ℕ × ℕ)) (mm XX : ℕ × ℕ → ℕ)
    (F : Finset ι) (G : ι → GridParams) (sc : ι → ℕ × ℕ)
    (U' : ℕ → Prop) [DecidablePred U'] {L : ℕ}
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hsc : ∀ ν ∈ F, sc ν ∈ S)
    (hQ : ∀ ν ∈ F, (G ν).Q = gridQ (sc ν).1 (sc ν).2)
    (hD₀ : ∀ ν ∈ F, (G ν).D₀ = gridD₀ (sc ν).1 (sc ν).2)
    (hU : ∀ ν ∈ F, (G ν).U = gridUmax (sc ν).1 (sc ν).2)
    (hcov : ∀ j, j < L → U' j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (XX (sc ν)) (mm (sc ν))) :
    ((Finset.range L).filter U').card
      ≤ ∑ p ∈ S, (gridUmax p.1 p.2 + 1) * ((L / (2 * scaleDmin p.1 p.2)) * mm p) := by
  classical
  have hsub : (Finset.range L).filter U' ⊆
      S.biUnion (fun p => (multSet (gridQ p.1 p.2) (gridD₀ p.1 p.2)
        (gridUmax p.1 p.2)).biUnion (fun d => periodCol d (mm p) L)) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨ν, hν, hjν⟩ := hcov j hj.1 hj.2
    obtain ⟨n, hn, α, h, hh, rfl⟩ := (mem_sampledPos (G ν)).1 hjν
    obtain ⟨c, hc1, hc⟩ := exists_kIdx_eq (G ν) (hT ν hν) hn α
    have hd : (G ν).d α ∈ multSet (gridQ (sc ν).1 (sc ν).2) (gridD₀ (sc ν).1 (sc ν).2)
        (gridUmax (sc ν).1 (sc ν).2) := by
      have := d_mem_multSet (G ν) α
      rwa [hQ ν hν, hD₀ ν hν, hU ν hν] at this
    refine Finset.mem_biUnion.2 ⟨sc ν, hsc ν hν, Finset.mem_biUnion.2 ⟨(G ν).d α, hd, ?_⟩⟩
    rw [hc] at hj ⊢
    exact mem_periodCol ((G ν).d_pos α) hc1 hh hj.1
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_sum fun p _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun d _ => card_periodCol_le d (mm p) L)) ?_
  have hstep : ∀ d ∈ multSet (gridQ p.1 p.2) (gridD₀ p.1 p.2) (gridUmax p.1 p.2),
      (L / (2 * d)) * mm p ≤ (L / (2 * scaleDmin p.1 p.2)) * mm p := by
    intro d hd
    refine Nat.mul_le_mul_right _ (Nat.div_le_div_left ?_
      (by have := scaleDmin_pos p.1 p.2; omega))
    exact Nat.mul_le_mul_left 2 (le_of_mem_multSet hd)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_multSet_le _ _ _)

/-! ### The weight of a scale pair -/

/-- The weight of the scale pair `(K,N)`. -/
noncomputable def pairWeight (mm : ℕ × ℕ → ℕ) (p : ℕ × ℕ) : ℝ :=
  ((gridUmax p.1 p.2 : ℝ) + 1) * (mm p : ℝ) / (2 * (scaleDmin p.1 p.2 : ℝ))

lemma four_mul_le_gridB {K N : ℕ} (hK : 2 ≤ K) : 4 * (K + N) ≤ gridB K N := by
  unfold gridB
  have h4 : 4 ≤ K ^ 2 := by nlinarith
  have := Nat.mul_le_mul_right (K + N) h4
  omega

/-- **The per-pair weight bound**: `w(K,N) ≤ (4(K+N))^{-K}`. -/
lemma pairWeight_le (mm : ℕ × ℕ → ℕ) {p : ℕ × ℕ} (hK : 2 ≤ p.1) (hm : mm p ≤ p.1) :
    pairWeight mm p ≤ 1 / ((4 * (p.1 + p.2) : ℝ)) ^ p.1 := by
  obtain ⟨K, N⟩ := p
  simp only at hK hm ⊢
  set U := gridUmax K N with hU
  have hK1 : 1 ≤ K := by omega
  have h4U : (4 * (K + N)) ^ K ≤ U := by
    calc (4 * (K + N)) ^ K ≤ gridB K N ^ K := Nat.pow_le_pow_left (four_mul_le_gridB hK) K
      _ ≤ U := NormalNumbers.G4.Sched.pow_le_gridUmax hK1
  have hU2 : 2 ≤ U := by
    have h1 : 8 ^ 1 ≤ (4 * (K + N)) ^ K := by
      refine le_trans (Nat.pow_le_pow_left (by omega) 1) (Nat.pow_le_pow_right (by omega) hK1)
    simp only [pow_one] at h1
    omega
  have hQU : U ≤ gridQ K N := by have := gridQ_gt K N; omega
  have hD₀ : gridD₀ K N = K * U := rfl
  have hUR : (2 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU2
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hmR : ((mm (K, N) : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hm
  have hdm : (K : ℝ) * (U : ℝ) * (U : ℝ) ≤ (scaleDmin K N : ℝ) := by
    have hnat : K * U * U ≤ scaleDmin K N := by
      unfold scaleDmin
      rw [hD₀]
      have h : U * (K * U) ≤ gridQ K N * (K * U) := Nat.mul_le_mul_right _ hQU
      calc K * U * U = U * (K * U) := by ring
        _ ≤ gridQ K N * (K * U) := h
        _ ≤ 1 + gridQ K N * (K * U) := by omega
    exact_mod_cast hnat
  have hdmpos : (0 : ℝ) < 2 * (scaleDmin K N : ℝ) := by
    have h := scaleDmin_pos K N
    have : (0 : ℝ) < (scaleDmin K N : ℝ) := by exact_mod_cast h
    linarith
  have hstep : pairWeight mm (K, N) ≤ 1 / (U : ℝ) := by
    unfold pairWeight
    simp only
    rw [div_le_div_iff₀ hdmpos (by linarith)]
    have hUpos : (0 : ℝ) ≤ (U : ℝ) := by linarith
    have hKpos : (0 : ℝ) ≤ (K : ℝ) := by linarith
    have hA : ((U : ℝ) + 1) * ((mm (K, N) : ℕ) : ℝ) * (U : ℝ)
        ≤ ((U : ℝ) + 1) * (K : ℝ) * (U : ℝ) := by
      have h0 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (U : ℝ) + 1) hUpos)
        (by linarith : (0:ℝ) ≤ (K : ℝ) - ((mm (K, N) : ℕ) : ℝ))
      linarith [h0]
    have hB : ((U : ℝ) + 1) * (K : ℝ) * (U : ℝ) ≤ 2 * ((K : ℝ) * (U : ℝ) * (U : ℝ)) := by
      have h0 := mul_nonneg (mul_nonneg hKpos hUpos) (by linarith : (0:ℝ) ≤ (U : ℝ) - 1)
      linarith [h0]
    linarith
  refine le_trans hstep ?_
  have h4 : ((4 * (K + N) : ℝ)) ^ K ≤ (U : ℝ) := by exact_mod_cast h4U
  have h4pos : (0 : ℝ) < ((4 * (K + N) : ℝ)) ^ K := by
    have : (0 : ℝ) < (4 * (K + N) : ℝ) := by
      have h1 : (2 : ℝ) ≤ (K : ℝ) := hKR
      have h2 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      linarith
    positivity
  exact one_div_le_one_div_of_le h4pos h4

/-- **The total weight of any set of distinct scale pairs is at most `1/8`.** -/
theorem sum_pairWeight_le (mm : ℕ × ℕ → ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, 2 ≤ p.1) (hm : ∀ p ∈ S, mm p ≤ p.1) :
    ∑ p ∈ S, pairWeight mm p ≤ 1 / 8 := by
  classical
  refine le_trans (Finset.sum_le_sum fun p hp => pairWeight_le mm (hS p hp) (hm p hp)) ?_
  have hinj : ∀ x ∈ S, ∀ y ∈ S, (x.1, x.1 + x.2) = (y.1, y.1 + y.2) → x = y := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext h1 (by omega)
  have hrw : ∑ p ∈ S, 1 / ((4 * (p.1 + p.2) : ℝ)) ^ p.1
      = ∑ q ∈ S.image (fun p => (p.1, p.1 + p.2)), 1 / ((4 * q.2 : ℝ)) ^ q.1 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    ring_nf
  rw [hrw]
  refine sum_double_le _ (fun q hq => ?_)
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
  have := hS p hp
  exact ⟨by simpa using this, by simp; omega⟩

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4 Finset

variable {ι : Type*} [DecidableEq ι]

/-- **The density bound over arbitrary scale pairs.**  Whatever the family, whatever set of
distinct scales `(K,N)` with `K ≥ 2` it uses, and whatever block lengths `mm p ≤ K`, the digit
positions it reads below `L` number at most `L/8`. -/
theorem card_le_of_scalePairs (S : Finset (ℕ × ℕ)) (mm XX : ℕ × ℕ → ℕ)
    (F : Finset ι) (G : ι → GridParams) (sc : ι → ℕ × ℕ)
    (U' : ℕ → Prop) [DecidablePred U'] {L : ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p.1) (hmle : ∀ p ∈ S, mm p ≤ p.1)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hsc : ∀ ν ∈ F, sc ν ∈ S)
    (hQ : ∀ ν ∈ F, (G ν).Q = gridQ (sc ν).1 (sc ν).2)
    (hD₀ : ∀ ν ∈ F, (G ν).D₀ = gridD₀ (sc ν).1 (sc ν).2)
    (hU : ∀ ν ∈ F, (G ν).U = gridUmax (sc ν).1 (sc ν).2)
    (hcov : ∀ j, j < L → U' j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (XX (sc ν)) (mm (sc ν))) :
    ((((Finset.range L).filter U').card : ℝ)) ≤ (1 / 8) * L := by
  have hnat := card_filter_le_of_scalePairs S mm XX F G sc U' hT hsc hQ hD₀ hU hcov
  have hcast : ((((Finset.range L).filter U').card : ℕ) : ℝ)
      ≤ ∑ p ∈ S,
        (((gridUmax p.1 p.2 + 1) * ((L / (2 * scaleDmin p.1 p.2)) * mm p) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hnat
  refine le_trans hcast ?_
  have hterm : ∀ p ∈ S,
      (((gridUmax p.1 p.2 + 1) * ((L / (2 * scaleDmin p.1 p.2)) * mm p) : ℕ) : ℝ)
        ≤ pairWeight mm p * L := by
    intro p _
    have hdpos : (0 : ℝ) < 2 * (scaleDmin p.1 p.2 : ℝ) := by
      have h := scaleDmin_pos p.1 p.2
      have : (0 : ℝ) < (scaleDmin p.1 p.2 : ℝ) := by exact_mod_cast h
      linarith
    have hdiv : (((L / (2 * scaleDmin p.1 p.2) : ℕ)) : ℝ)
        ≤ (L : ℝ) / (2 * (scaleDmin p.1 p.2 : ℝ)) := by
      have := Nat.cast_div_le (α := ℝ) (m := L) (n := 2 * scaleDmin p.1 p.2)
      push_cast at this ⊢
      exact this
    have hU1 : (0 : ℝ) ≤ (gridUmax p.1 p.2 : ℝ) + 1 := by positivity
    have hm1 : (0 : ℝ) ≤ (mm p : ℝ) := Nat.cast_nonneg _
    push_cast
    unfold pairWeight
    rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
    have hmul : ((gridUmax p.1 p.2 : ℝ) + 1) * ((((L / (2 * scaleDmin p.1 p.2) : ℕ)) : ℝ)
        * (mm p : ℝ)) * (2 * (scaleDmin p.1 p.2 : ℝ))
          ≤ ((gridUmax p.1 p.2 : ℝ) + 1) * (((L : ℝ) / (2 * (scaleDmin p.1 p.2 : ℝ)))
        * (mm p : ℝ)) * (2 * (scaleDmin p.1 p.2 : ℝ)) := by
      have hstep : (((L / (2 * scaleDmin p.1 p.2) : ℕ)) : ℝ) * (mm p : ℝ)
          ≤ ((L : ℝ) / (2 * (scaleDmin p.1 p.2 : ℝ))) * (mm p : ℝ) :=
        mul_le_mul_of_nonneg_right hdiv hm1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hU1) (le_of_lt hdpos)
    refine le_trans hmul (le_of_eq ?_)
    have hne : (scaleDmin p.1 p.2 : ℝ) ≠ 0 := by
      have h := scaleDmin_pos p.1 p.2
      have : (0 : ℝ) < (scaleDmin p.1 p.2 : ℝ) := by exact_mod_cast h
      exact ne_of_gt this
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_pairWeight_le mm S hS hmle) (Nat.cast_nonneg _)

/-- **The final form of the §6 negative answer.**  No family of grids carrying the schedule's
parameter functions — at any set of scales `(K,N)`, of any size, with any frozen residues,
atoms, translations, sample ranges or block lengths `≤ K` — reads half of any prefix of the
digit positions.  With `G4EntropyBarrier`, no statement about any such sample can imply
ordinary binary normality. -/
theorem not_dense_of_scalePairs (S : Finset (ℕ × ℕ)) (mm XX : ℕ × ℕ → ℕ)
    (F : Finset ι) (G : ι → GridParams) (sc : ι → ℕ × ℕ)
    (U' : ℕ → Prop) [DecidablePred U'] {L : ℕ} (hL : 0 < L)
    (hS : ∀ p ∈ S, 2 ≤ p.1) (hmle : ∀ p ∈ S, mm p ≤ p.1)
    (hT : ∀ ν ∈ F, ∃ α β : (G ν).Atom, (G ν).t α ≠ (G ν).t β)
    (hsc : ∀ ν ∈ F, sc ν ∈ S)
    (hQ : ∀ ν ∈ F, (G ν).Q = gridQ (sc ν).1 (sc ν).2)
    (hD₀ : ∀ ν ∈ F, (G ν).D₀ = gridD₀ (sc ν).1 (sc ν).2)
    (hU : ∀ ν ∈ F, (G ν).U = gridUmax (sc ν).1 (sc ν).2)
    (hcov : ∀ j, j < L → U' j → ∃ ν ∈ F, j ∈ sampledPos (G ν) (XX (sc ν)) (mm (sc ν))) :
    ¬ (L ≤ 2 * ((Finset.range L).filter U').card) := by
  intro hdense
  have h := card_le_of_scalePairs S mm XX F G sc U' hS hmle hT hsc hQ hD₀ hU hcov
  have hdR : (L : ℝ) ≤ 2 * ((((Finset.range L).filter U').card : ℕ) : ℝ) := by
    exact_mod_cast hdense
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  linarith

end NormalNumbers.G4Entropy

/-! ## The obstruction is intrinsic to freezing

Every negative result above traces to one comparison: the multipliers satisfy
`d_α ≥ 1 + Q·D₀` while the sample's alphabet has size `H_K·m_K = (K²+1)^K·m`.  A sampler with
any hope of reading a positive fraction of the digit positions would need its *period* `2 d_min`
to be comparable to its *alphabet* `H·m` — say `2 d_min ≤ C·H·m` for a fixed `C`.

That is impossible.  `GridParams` forces `Q ≥ U` and `D₀ = K·U` (the freezing modulus must beat
every `u_α`), and `U ≥ B^K ≥ K^{3K}`, so `2 d_min ≥ 2K·K^{6K}` while `C·H·m ≤ K^{3K+2}` once
`C ≤ K`.  The gap is `K^{3K}`, not a constant: **no admissible scale is readable**, and the
sparsity of the sample is a consequence of the freezing construction itself, not of any choice
made inside it.
-/

namespace NormalNumbers.G4Entropy

open NormalNumbers NormalNumbers.G4 Finset

lemma cube_le_gridB (K N : ℕ) : K ^ 3 ≤ gridB K N := by
  unfold gridB
  have : K ^ 2 * K ≤ K ^ 2 * (K + N) := Nat.mul_le_mul_left _ (by omega)
  calc K ^ 3 = K ^ 2 * K := by ring
    _ ≤ K ^ 2 * (K + N) := this
    _ ≤ K ^ 2 * (K + N) + 1 := by omega

/-- **No admissible scale is readable.**  For every constant `C` and every scale `K ≥ max(C,4)`,
the sample's period `2 d_min` exceeds `C` times its alphabet `H_K·m`, whatever the layer count
`N` and whatever the block length `m ≤ K`. -/
theorem not_readable_scale {C K N m : ℕ} (hK : 4 ≤ K) (hCK : C ≤ K) (hm : m ≤ K) :
    C * ((K ^ 2 + 1) ^ K * m) < 2 * scaleDmin K N := by
  have hK1 : 1 ≤ K := by omega
  have hK2 : 2 ≤ K := by omega
  set U := gridUmax K N with hU
  -- lower bound on the period
  have hBU : gridB K N ^ K ≤ U := NormalNumbers.G4.Sched.pow_le_gridUmax hK1
  have hcube : (K ^ 3) ^ K ≤ gridB K N ^ K := Nat.pow_le_pow_left (cube_le_gridB K N) K
  have hKU : K ^ (3 * K) ≤ U := by
    calc K ^ (3 * K) = (K ^ 3) ^ K := by rw [← pow_mul]
      _ ≤ gridB K N ^ K := hcube
      _ ≤ U := hBU
  have hQU : U ≤ gridQ K N := by have := gridQ_gt K N; omega
  have hD₀ : gridD₀ K N = K * U := rfl
  have hper : K * (U * U) ≤ scaleDmin K N := by
    unfold scaleDmin
    rw [hD₀]
    have h : U * (K * U) ≤ gridQ K N * (K * U) := Nat.mul_le_mul_right _ hQU
    calc K * (U * U) = U * (K * U) := by ring
      _ ≤ gridQ K N * (K * U) := h
      _ ≤ 1 + gridQ K N * (K * U) := by omega
  have hUU : K ^ (6 * K) ≤ U * U := by
    have : K ^ (3 * K) * K ^ (3 * K) ≤ U * U := Nat.mul_le_mul hKU hKU
    calc K ^ (6 * K) = K ^ (3 * K) * K ^ (3 * K) := by rw [← pow_add]; ring_nf
      _ ≤ U * U := this
  have hlow : K ^ (6 * K + 1) ≤ scaleDmin K N := by
    refine le_trans ?_ hper
    calc K ^ (6 * K + 1) = K * K ^ (6 * K) := by rw [pow_succ]; ring
      _ ≤ K * (U * U) := Nat.mul_le_mul_left _ hUU
  -- upper bound on the alphabet
  have halph : C * ((K ^ 2 + 1) ^ K * m) ≤ K ^ (3 * K + 2) := by
    have h1 : (K ^ 2 + 1) ^ K ≤ (2 * K ^ 2) ^ K := by
      refine Nat.pow_le_pow_left ?_ K
      nlinarith [Nat.one_le_pow 2 K (by omega : 0 < K)]
    have h2 : (2 * K ^ 2) ^ K = 2 ^ K * K ^ (2 * K) := by
      rw [mul_pow, ← pow_mul]
    have h3 : (2 : ℕ) ^ K ≤ K ^ K := Nat.pow_le_pow_left hK2 K
    have h4 : (K ^ 2 + 1) ^ K ≤ K ^ (3 * K) := by
      calc (K ^ 2 + 1) ^ K ≤ (2 * K ^ 2) ^ K := h1
        _ = 2 ^ K * K ^ (2 * K) := h2
        _ ≤ K ^ K * K ^ (2 * K) := Nat.mul_le_mul_right _ h3
        _ = K ^ (3 * K) := by rw [← pow_add]; ring_nf
    calc C * ((K ^ 2 + 1) ^ K * m) ≤ K * (K ^ (3 * K) * K) :=
          Nat.mul_le_mul hCK (Nat.mul_le_mul h4 hm)
      _ = K ^ (3 * K + 2) := by ring
  have hmono : K ^ (3 * K + 2) ≤ K ^ (6 * K + 1) :=
    Nat.pow_le_pow_right hK1 (by omega)
  have hpos : 0 < K ^ (6 * K + 1) := pow_pos (by omega) _
  omega

/-- The readable-scale property, named for the record: a scale whose sampling *period* is
comparable to its alphabet.  `not_readable_scale` says it is empty for `K ≥ max(C,4)`. -/
def ReadableScale (C K N m : ℕ) : Prop := 2 * scaleDmin K N ≤ C * ((K ^ 2 + 1) ^ K * m)

theorem not_readableScale {C K N m : ℕ} (hK : 4 ≤ K) (hCK : C ≤ K) (hm : m ≤ K) :
    ¬ ReadableScale C K N m := by
  intro h
  exact absurd h (not_le.2 (not_readable_scale hK hCK hm))

end NormalNumbers.G4Entropy
