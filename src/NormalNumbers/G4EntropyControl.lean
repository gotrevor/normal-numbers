/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyScales

/-!
# Entropy expedition §5: exactly which sampled frequencies the entropy controls

The brief asks to *state exactly which sampled frequencies entropy controls*.  The answer, made
precise here, is **none at any fixed word length** — and the reason is not a defect of the
estimates but of the quantity.

`uniformOn S` is the uniform law on a nonempty `S ⊆ Ω`, with `H₂ = log₂ |S|` exactly
(`H₂_uniformOn`).  Taking `S` to be half the alphabet of an `m`-bit block gives a law with

* entropy `m − 1`, hence **entropy rate `(m−1)/m → 1`** — asymptotically maximal, exactly the
  conclusion `entropy_E0`/`entropy_E1` deliver; and
* probability `0` of the event "the leading bit is `1`", whose uniform probability is `1/2`.

So `H₂/m → 1` does not imply that any fixed sampled word has its uniform frequency
(`entropy_rate_not_control_bit`, `exists_highEntropy_biased_seq`).  This is the finite-law core
of the brief's warning that the low-entropy typical-set shortcut is refuted by a mixture of a
fair process and an all-zero process.

What the sample entropy *does* control is richness, not frequency: `FinLaw.prob_infoSet_ge` and
`FinLaw.card_infoSet_le` (`G4EntropyInfo`) say the sampled vector spends most of its mass on a
set of at least `2^{(1−δ/2)·m·H}` values.  That statement is unaffected, and it is the honest
content of §5.
-/

open Finset

namespace NormalNumbers.G4Entropy

open NormalNumbers Real

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ### The uniform law on a subset -/

/-- The uniform law on a nonempty finite subset. -/
noncomputable def uniformOn (S : Finset Ω) (hS : S.Nonempty) : FinLaw Ω where
  p ω := if ω ∈ S then (1 : ℝ) / S.card else 0
  nonneg ω := by
    split
    · positivity
    · exact le_refl 0
  sum_p := by
    have hcard : (0 : ℝ) < (S.card : ℝ) := by
      have := Finset.card_pos.2 hS
      exact_mod_cast this
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    field_simp

@[simp] lemma uniformOn_p (S : Finset Ω) (hS : S.Nonempty) (ω : Ω) :
    (uniformOn S hS).p ω = if ω ∈ S then (1 : ℝ) / S.card else 0 := rfl

/-- **The entropy of the uniform law on `S` is exactly `log₂ |S|`.** -/
theorem H₂_uniformOn (S : Finset Ω) (hS : S.Nonempty) :
    (uniformOn S hS).H₂ = Real.logb 2 S.card := by
  have hcardN : 0 < S.card := Finset.card_pos.2 hS
  have hcard : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcardN
  have hterm : ∀ ω : Ω, Real.negMulLog ((uniformOn S hS).p ω)
      = if ω ∈ S then (1 / (S.card : ℝ)) * Real.log S.card else 0 := by
    intro ω
    rw [uniformOn_p]
    split
    · rw [Real.negMulLog, Real.log_div one_ne_zero (ne_of_gt hcard), Real.log_one]
      ring
    · simp [Real.negMulLog]
  have hsum : ∑ ω, Real.negMulLog ((uniformOn S hS).p ω) = Real.log S.card := by
    rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [FinLaw.H₂, hsum, Real.logb]

/-! ### A high-entropy law with a completely biased leading bit -/

/-- The `m`-bit blocks whose leading bit is `0` — the bottom half of the alphabet. -/
noncomputable def lowHalf (m : ℕ) : Finset (Fin (2 ^ m)) :=
  Finset.univ.filter (fun z => (z : ℕ) < 2 ^ (m - 1))

/-- The `m`-bit blocks whose leading bit is `1`. -/
noncomputable def highHalf (m : ℕ) : Finset (Fin (2 ^ m)) :=
  Finset.univ.filter (fun z => 2 ^ (m - 1) ≤ (z : ℕ))

lemma card_lowHalf {m : ℕ} (hm : 1 ≤ m) : (lowHalf m).card = 2 ^ (m - 1) := by
  classical
  have hle : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have himg : lowHalf m
      = Finset.map (Fin.castLEEmb hle) (Finset.univ : Finset (Fin (2 ^ (m - 1)))) := by
    ext z
    simp only [lowHalf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb, Function.Embedding.coeFn_mk]
    constructor
    · intro hz
      refine ⟨⟨(z : ℕ), hz⟩, ?_⟩
      simp
    · rintro ⟨w, -, rfl⟩
      simpa using w.isLt
  rw [himg, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma lowHalf_nonempty {m : ℕ} (hm : 1 ≤ m) : (lowHalf m).Nonempty := by
  rw [← Finset.card_pos, card_lowHalf hm]
  exact pow_pos (by omega) _

lemma prob_highHalf_uniformOn_lowHalf {m : ℕ} (hm : 1 ≤ m) :
    (uniformOn (lowHalf m) (lowHalf_nonempty hm)).prob (highHalf m) = 0 := by
  classical
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [uniformOn_p, if_neg]
  intro hlow
  rw [highHalf, Finset.mem_filter] at hz
  rw [lowHalf, Finset.mem_filter] at hlow
  omega

/-- **Entropy rate near `1` does not control a single sampled bit.**

The uniform law on the bottom half of the `m`-bit alphabet has entropy `m − 1` — rate
`(m−1)/m`, asymptotically maximal — yet gives the event "leading bit `= 1`" probability `0`,
against its uniform value `1/2`. -/
theorem entropy_rate_not_control_bit {m : ℕ} (hm : 1 ≤ m) :
    ∃ L : FinLaw (Fin (2 ^ m)), L.H₂ = (m : ℝ) - 1 ∧ L.prob (highHalf m) = 0 := by
  refine ⟨uniformOn (lowHalf m) (lowHalf_nonempty hm), ?_, prob_highHalf_uniformOn_lowHalf hm⟩
  rw [H₂_uniformOn, card_lowHalf hm]
  rw [show ((2 ^ (m - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (m - 1) by push_cast; ring]
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one]
  push_cast [Nat.cast_sub hm]
  ring

/-- The same as a sequence: entropy rate `→ 1` with a permanently dead leading bit. -/
theorem exists_highEntropy_biased_seq :
    ∃ L : ∀ i : ℕ, FinLaw (Fin (2 ^ (i + 1))),
      (∀ i, (L i).prob (highHalf (i + 1)) = 0) ∧
      Filter.Tendsto (fun i => (L i).H₂ / ((i : ℝ) + 1)) Filter.atTop (nhds 1) := by
  refine ⟨fun i => uniformOn (lowHalf (i + 1)) (lowHalf_nonempty (by omega)), fun i =>
    prob_highHalf_uniformOn_lowHalf (by omega), ?_⟩
  have hval : ∀ i : ℕ,
      (uniformOn (lowHalf (i + 1)) (lowHalf_nonempty (by omega))).H₂ / ((i : ℝ) + 1)
        = 1 - 1 / ((i : ℝ) + 1) := by
    intro i
    obtain ⟨L, hH, -⟩ := entropy_rate_not_control_bit (m := i + 1) (by omega)
    have hHrw : (uniformOn (lowHalf (i + 1)) (lowHalf_nonempty (by omega))).H₂
        = ((i : ℝ) + 1) - 1 := by
      rw [H₂_uniformOn, card_lowHalf (by omega : 1 ≤ i + 1)]
      simp only [Nat.add_sub_cancel]
      rw [show ((2 ^ i : ℕ) : ℝ) = (2 : ℝ) ^ i by push_cast; ring]
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one]
      push_cast
      ring
    rw [hHrw]
    have hne : ((i : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [Filter.tendsto_congr hval]
  have h1 : Filter.Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).sub h1
  simpa using this

end NormalNumbers.G4Entropy
