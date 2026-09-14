/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyGranule
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropy expedition — restricting the *sample times*, and the cost of doing so

`FinLaw.H₂_restrictCoords_ge` prices a restriction in the **coordinate** direction.  This module
prices the other direction — restricting the empirical law to a sub-collection `S` of the sample
times — which is what a granule of a certified chunk actually is.

The mechanism is the mixture bound: an empirical law over `P` is the `σ`-mixture of the
empirical laws over `S` and `P \ S`, with `σ = |S|/|P|`, and

    `H₂(mixture) ≤ σ·H₂(L_S) + (1−σ)·H₂(L_{P∖S}) + 1`

(the extra bit is the binary entropy of `σ`).  With `H₂(L_{P∖S}) ≤ log₂|Ω| = m` this gives

    `H₂(L_S) ≥ m − (δ + 1)/σ`   whenever   `H₂(L) ≥ m − δ`.

So a sub-range of the sample times of relative size `σ` inflates the deficit by `1/σ` exactly
as a sub-collection of coordinates does: **a certified granule must contain at least a
`≈ δ/m`-fraction of the sample times.**  Together with `granule_exceeds_previous_scale` this
turns lap 62's reading into a theorem: no certified granule at scale `i+1` is small enough to
sit inside the digits scale `i` produced.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

/-! ### `negMulLog` is subadditive -/

lemma negMulLog_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.negMulLog (u + v) ≤ Real.negMulLog u + Real.negMulLog v := by
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · simp [← hu0]
  rcases eq_or_lt_of_le hv with hv0 | hv0
  · simp [← hv0]
  have hlu : Real.log u ≤ Real.log (u + v) := Real.log_le_log hu0 (by linarith)
  have hlv : Real.log v ≤ Real.log (u + v) := Real.log_le_log hv0 (by linarith)
  simp only [Real.negMulLog]
  nlinarith [hlu, hlv, hu0.le, hv0.le]

namespace FinLaw

variable {Ω : Type*} [Fintype Ω]

/-- The `σ`-mixture of two laws. -/
noncomputable def mix (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (L₁ L₂ : FinLaw Ω) : FinLaw Ω where
  p ω := σ * L₁.p ω + (1 - σ) * L₂.p ω
  nonneg ω := by
    have := L₁.nonneg ω
    have := L₂.nonneg ω
    have : (0 : ℝ) ≤ 1 - σ := by linarith
    positivity
  sum_p := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, L₁.sum_p, L₂.sum_p]
    ring

/-- **The mixture bound.**  Mixing two laws can create at most one extra bit of entropy beyond
the average of theirs. -/
theorem H₂_mix_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (L₁ L₂ : FinLaw Ω) :
    (mix σ hσ0 hσ1 L₁ L₂).H₂ ≤ σ * L₁.H₂ + (1 - σ) * L₂.H₂ + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ ω : Ω, Real.negMulLog (σ * L₁.p ω + (1 - σ) * L₂.p ω)
      ≤ (L₁.p ω * Real.negMulLog σ + σ * Real.negMulLog (L₁.p ω))
        + (L₂.p ω * Real.negMulLog (1 - σ) + (1 - σ) * Real.negMulLog (L₂.p ω)) := by
    intro ω
    have h1 : (0 : ℝ) ≤ σ * L₁.p ω := mul_nonneg hσ0 (L₁.nonneg ω)
    have h2 : (0 : ℝ) ≤ (1 - σ) * L₂.p ω := mul_nonneg (by linarith) (L₂.nonneg ω)
    refine (negMulLog_add_le h1 h2).trans ?_
    rw [Real.negMulLog_mul σ (L₁.p ω), Real.negMulLog_mul (1 - σ) (L₂.p ω)]
  have hsum : ∑ ω, Real.negMulLog ((mix σ hσ0 hσ1 L₁ L₂).p ω)
      ≤ Real.negMulLog σ + σ * (∑ ω, Real.negMulLog (L₁.p ω))
        + (Real.negMulLog (1 - σ) + (1 - σ) * (∑ ω, Real.negMulLog (L₂.p ω))) := by
    refine (Finset.sum_le_sum fun ω _ => hterm ω).trans ?_
    rw [Finset.sum_add_distrib]
    have e1 : ∑ ω, (L₁.p ω * Real.negMulLog σ + σ * Real.negMulLog (L₁.p ω))
        = Real.negMulLog σ + σ * (∑ ω, Real.negMulLog (L₁.p ω)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, L₁.sum_p, ← Finset.mul_sum, one_mul]
    have e2 : ∑ ω, (L₂.p ω * Real.negMulLog (1 - σ) + (1 - σ) * Real.negMulLog (L₂.p ω))
        = Real.negMulLog (1 - σ) + (1 - σ) * (∑ ω, Real.negMulLog (L₂.p ω)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, L₂.sum_p, ← Finset.mul_sum, one_mul]
    rw [e1, e2]
  have hbin : Real.negMulLog σ + Real.negMulLog (1 - σ) ≤ Real.log 2 := by
    have := Real.binEntropy_le_log_two (p := σ)
    rwa [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at this
  rw [H₂, H₂, H₂, div_le_iff₀ hlog2]
  have hd1 : σ * ((∑ ω, Real.negMulLog (L₁.p ω)) / Real.log 2) * Real.log 2
      = σ * (∑ ω, Real.negMulLog (L₁.p ω)) := by field_simp
  have hd2 : (1 - σ) * ((∑ ω, Real.negMulLog (L₂.p ω)) / Real.log 2) * Real.log 2
      = (1 - σ) * (∑ ω, Real.negMulLog (L₂.p ω)) := by field_simp
  nlinarith [hsum, hbin, hd1, hd2]

/-- **The deficit of a part of a mixture.**  If the mixture has deficit `δ` against `M` and the
other part has entropy at most `M`, the `σ`-part has deficit at most `(δ+1)/σ`. -/
theorem H₂_of_mix_part_ge {σ M δ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (L₁ L₂ : FinLaw Ω)
    (hL₂ : L₂.H₂ ≤ M) (hmix : M - δ ≤ (mix σ hσ0.le hσ1 L₁ L₂).H₂) :
    M - (δ + 1) / σ ≤ L₁.H₂ := by
  have h := H₂_mix_le hσ0.le hσ1 L₁ L₂
  have hstep : M - δ ≤ σ * L₁.H₂ + (1 - σ) * M + 1 := by
    nlinarith [hL₂, h, hmix, sub_nonneg.2 hσ1]
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hσ0]
  nlinarith [hstep]

end FinLaw

/-! ### The empirical law over a sub-collection of sample times -/

open Classical in
/-- **An empirical law is the mixture of its restriction and its complement.** -/
theorem empirical_eq_mix {ι Ω : Type*} [Fintype Ω] {P S : Finset ι} (hP : P.Nonempty)
    (hS : S.Nonempty) (hT : (P \ S).Nonempty) (hSP : S ⊆ P) (f : ι → Ω) :
    empirical P hP f
      = FinLaw.mix ((S.card : ℝ) / (P.card : ℝ))
          (by positivity)
          (by
            rw [div_le_one (by exact_mod_cast Finset.card_pos.2 hP)]
            exact_mod_cast Finset.card_le_card hSP)
          (empirical S hS f) (empirical (P \ S) hT f) := by
  classical
  refine FinLaw.ext' (funext fun ω => ?_)
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hP
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hS
  have hTpos : (0 : ℝ) < ((P \ S).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hT
  have hcards : (S.card : ℝ) + ((P \ S).card : ℝ) = (P.card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card hSP
    have : S.card + (P \ S).card = P.card := by omega
    exact_mod_cast this
  have hsplit : (P.filter fun i => f i = ω).card
      = (S.filter fun i => f i = ω).card + ((P \ S).filter fun i => f i = ω).card := by
    have hdisj : Disjoint (S.filter fun i => f i = ω) ((P \ S).filter fun i => f i = ω) := by
      refine Finset.disjoint_left.2 fun i hi hi' => ?_
      have h1 := (Finset.mem_filter.1 hi).1
      have h2 := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hi').1).2
      exact h2 h1
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hi, hf⟩
      by_cases h : i ∈ S
      · exact Or.inl ⟨h, hf⟩
      · exact Or.inr ⟨⟨hi, h⟩, hf⟩
    · rintro (⟨h, hf⟩ | ⟨⟨h, -⟩, hf⟩)
      · exact ⟨hSP h, hf⟩
      · exact ⟨h, hf⟩
  show ((P.filter fun i => f i = ω).card : ℝ) / (P.card : ℝ) = _
  show _ = (S.card : ℝ) / (P.card : ℝ) * (((S.filter fun i => f i = ω).card : ℝ) / (S.card : ℝ))
      + (1 - (S.card : ℝ) / (P.card : ℝ))
        * ((((P \ S).filter fun i => f i = ω).card : ℝ) / ((P \ S).card : ℝ))
  have h1 : (1 : ℝ) - (S.card : ℝ) / (P.card : ℝ) = ((P \ S).card : ℝ) / (P.card : ℝ) := by
    field_simp
    linarith [hcards]
  rw [h1]
  have hsplitR : ((P.filter fun i => f i = ω).card : ℝ)
      = ((S.filter fun i => f i = ω).card : ℝ) + (((P \ S).filter fun i => f i = ω).card : ℝ) := by
    exact_mod_cast hsplit
  rw [hsplitR]
  field_simp

open Classical in
/-- **The cost of restricting the sample times.**  If the full empirical law has deficit `δ`
against a ceiling `M` that also caps the complementary law, then the restriction to `S` has
deficit at most `(δ+1)/σ`, `σ = |S|/|P|`.

The extra bit is the binary entropy of `σ`; apart from it this is exactly the coordinate-side
statement `H₂_restrictCoords_ge`. -/
theorem H₂_empirical_restrict_ge {ι Ω : Type*} [Fintype Ω] {P S : Finset ι} (hP : P.Nonempty)
    (hS : S.Nonempty) (hSP : S ⊆ P) (f : ι → Ω) {M δ : ℝ}
    (hceil : ∀ (T : Finset ι) (hT : T.Nonempty), (empirical T hT f).H₂ ≤ M)
    (hdef : M - δ ≤ (empirical P hP f).H₂) :
    M - (δ + 1) / ((S.card : ℝ) / (P.card : ℝ)) ≤ (empirical S hS f).H₂ := by
  classical
  rcases Finset.eq_empty_or_nonempty (P \ S) with hempty | hT
  · -- `S = P`, so `σ = 1` and there is nothing to pay
    have hPS : P ⊆ S := by
      intro i hi
      by_contra h
      have : i ∈ P \ S := Finset.mem_sdiff.2 ⟨hi, h⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty i)
    have hPeq : P = S := Finset.Subset.antisymm hPS hSP
    subst hPeq
    have hσ : (P.card : ℝ) / (P.card : ℝ) = 1 := by
      have : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hP
      field_simp
    rw [hσ, div_one]
    have : (empirical P hP f).H₂ = (empirical P hS f).H₂ := by rfl
    linarith [hdef, this]
  · have hPpos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hP
    have hSpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hS
    have hσ0 : (0 : ℝ) < (S.card : ℝ) / (P.card : ℝ) := by positivity
    have hσ1 : (S.card : ℝ) / (P.card : ℝ) ≤ 1 := by
      rw [div_le_one hPpos]
      exact_mod_cast Finset.card_le_card hSP
    have hmixeq := empirical_eq_mix hP hS hT hSP f
    have hceil' : (empirical (P \ S) hT f).H₂ ≤ M := hceil _ hT
    refine FinLaw.H₂_of_mix_part_ge hσ0 hσ1 (empirical S hS f) (empirical (P \ S) hT f)
      hceil' ?_
    rw [← hmixeq]
    exact hdef

/-! ### The window form, and the vacuity threshold -/

open Classical in
/-- **Restricting the sample times of a window family.**  The alphabet ceiling is `m` bits, so
a sub-collection of relative size `σ` has deficit at most `(δ+1)/σ`. -/
theorem H₂_empirical_window_restrict_ge {ι : Type*} {m : ℕ} {P S : Finset ι} (hP : P.Nonempty)
    (hS : S.Nonempty) (hSP : S ⊆ P) (f : ι → Fin (2 ^ m)) {δ : ℝ}
    (hdef : (m : ℝ) - δ ≤ (empirical P hP f).H₂) :
    (m : ℝ) - (δ + 1) / ((S.card : ℝ) / (P.card : ℝ)) ≤ (empirical S hS f).H₂ := by
  classical
  refine H₂_empirical_restrict_ge hP hS hSP f (fun T hT => ?_) hdef
  have hcard : Fintype.card (Fin (2 ^ m)) = 2 ^ m := by simp
  have hpos : 0 < Fintype.card (Fin (2 ^ m)) := by rw [hcard]; exact Nat.two_pow_pos m
  have h := (empirical T hT f).H₂_le_logb_card hpos
  rwa [hcard, FinLaw.logb_two_pow] at h

/-- **The capture bound is vacuous below the granularity threshold.**  `|freq − 2^{−ℓ}| ≤ 1` is
free, so a bound of `1` or more says nothing. -/
theorem capture_bound_vacuous {m ℓ : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : (m : ℝ) - ℓ + 1 ≤ 4 * Real.log 2 * (ℓ : ℝ) * β) (hm : (0 : ℝ) < (m : ℝ) - ℓ + 1) :
    1 ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * β / ((m : ℝ) - ℓ + 1)) := by
  have hq : (1 : ℝ) / 4 ≤ Real.log 2 * (ℓ : ℝ) * β / ((m : ℝ) - ℓ + 1) := by
    rw [le_div_iff₀ hm]
    linarith
  have h := Real.sqrt_le_sqrt hq
  rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)] at h
  linarith

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

set_option maxHeartbeats 1000000 in
/-- **The certified granule at scale `i+1` already exceeds everything scale `i` produced.**

`S` is any sub-collection of scale-`(i+1)` sample times whose derived capture bound — the
capture inequality fed the restricted deficit `(δ+1)/σ` of `H₂_empirical_window_restrict_ge`,
`σ = |S|/|P|` — is **not vacuous**.  Then the digits `S` reads, `|S|·m_{i+1}`, already exceed
`|Atom_i|·|P_{K_i}|·m_i`: every atom, every sample time and every digit of scale `i`.

So a construction reading sampled digits in position order as a concatenation of certified
granules cannot have converging prefix frequencies: the first granule of the next scale wipes
out the history.  This is the theorem form of lap 62's reading, and it is independent of how
the granule is cut — by atoms, by sample times, or by both. -/
theorem certified_granule_exceeds_previous_scale (i ℓ : ℕ) (hℓ : 0 < ℓ)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ PK (i + 1)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnonvac : 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ)
        * ((δ + 1) / ((S.card : ℝ) / ((PK (i + 1)).card : ℝ)))
        / ((kk (i + 1) : ℝ) - ℓ + 1)) < 1) (hℓm : ℓ ≤ kk (i + 1)) :
    (Fintype.card (gridAt i).Atom : ℝ) * ((PK i).card : ℝ) * (kk i : ℝ)
      < (S.card : ℝ) * (kk (i + 1) : ℝ) := by
  have hPpos : (0 : ℝ) < ((PK (i + 1)).card : ℝ) := by
    exact_mod_cast PK_card_pos (i + 1)
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hSne
  have hmpos : (0 : ℝ) < (kk (i + 1) : ℝ) - ℓ + 1 := by
    have : (ℓ : ℝ) ≤ (kk (i + 1) : ℝ) := by exact_mod_cast hℓm
    linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = (S.card : ℝ) / ((PK (i + 1)).card : ℝ) := ⟨_, rfl⟩
  rw [← hσ] at hnonvac
  have hσpos : 0 < σ := by rw [hσ]; exact div_pos hSpos hPpos
  -- non-vacuity forces `σ` above the threshold
  have hnot : ¬ ((kk (i + 1) : ℝ) - ℓ + 1 ≤ 4 * Real.log 2 * (ℓ : ℝ) * ((δ + 1) / σ)) := by
    intro hsmall
    have := capture_bound_vacuous (m := kk (i + 1)) (ℓ := ℓ) (β := (δ + 1) / σ)
      (div_nonneg (by linarith) hσpos.le) hsmall hmpos
    linarith
  push_neg at hnot
  -- hence `σ · m > 1`
  have hq : (0 : ℝ) ≤ (δ + 1) / σ := div_nonneg (by linarith) hσpos.le
  have hconst : (2.76 : ℝ) ≤ 4 * Real.log 2 * (ℓ : ℝ) := by nlinarith [hlog2, hℓ1]
  have h2 : (2.76 : ℝ) * ((δ + 1) / σ) ≤ 4 * Real.log 2 * (ℓ : ℝ) * ((δ + 1) / σ) :=
    mul_le_mul_of_nonneg_right hconst hq
  have hone : (1 : ℝ) / σ ≤ (δ + 1) / σ :=
    div_le_div_of_nonneg_right (by linarith) hσpos.le
  have h5 : (2.76 : ℝ) / σ < (kk (i + 1) : ℝ) := by
    calc (2.76 : ℝ) / σ = 2.76 * (1 / σ) := by ring
      _ ≤ 2.76 * ((δ + 1) / σ) := by linarith
      _ ≤ 4 * Real.log 2 * (ℓ : ℝ) * ((δ + 1) / σ) := h2
      _ < (kk (i + 1) : ℝ) - ℓ + 1 := hnot
      _ ≤ (kk (i + 1) : ℝ) := by linarith
  rw [div_lt_iff₀ hσpos] at h5
  have hbig : (1 : ℝ) < σ * (kk (i + 1) : ℝ) := by nlinarith [h5]
  -- so `|S| · m > |P_{i+1}|`
  have hSm : ((PK (i + 1)).card : ℝ) < (S.card : ℝ) * (kk (i + 1) : ℝ) := by
    rw [hσ, div_mul_eq_mul_div, lt_div_iff₀ hPpos] at hbig
    linarith
  exact lt_trans (granule_exceeds_previous_scale i) hSm

/-- **The wall does not depend on the entropy quality.**  `certified_granule_exceeds_previous_scale`
is stated for *every* `δ ≥ 0`; here it is at `δ = 0`, i.e. for a sample of *exactly maximal*
entropy.  Even then the minimum certified granule at scale `i+1` — forced by the one bit the
mixture bound charges for splitting the sample times — already exceeds everything scale `i`
produced.

So no improvement of `entropy_E1`'s deficit `50√K`, however drastic, can break the wall: the
obstruction is the scale ladder's growth `X(K) = 2^{100·2^{m(K)}}`, not the quality of the
entropy estimate. -/
theorem wall_at_zero_deficit (i ℓ : ℕ) (hℓ : 0 < ℓ) (S : Finset ℕ) (hSne : S.Nonempty)
    (hS : S ⊆ PK (i + 1))
    (hnonvac : 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ)
        * ((0 + 1) / ((S.card : ℝ) / ((PK (i + 1)).card : ℝ)))
        / ((kk (i + 1) : ℝ) - ℓ + 1)) < 1) (hℓm : ℓ ≤ kk (i + 1)) :
    (Fintype.card (gridAt i).Atom : ℝ) * ((PK i).card : ℝ) * (kk i : ℝ)
      < (S.card : ℝ) * (kk (i + 1) : ℝ) :=
  certified_granule_exceeds_previous_scale i ℓ hℓ S hSne hS (δ := 0) le_rfl hnonvac hℓm

end NormalNumbers.G4.Sched
