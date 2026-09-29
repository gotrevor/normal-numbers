/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7IooFreq

/-!
# S7-A: anchored targets escape the moving-target refutation

`not_gappedHitPrinciple` (lap 59) kills every soft treatment of a predictable family of short
intervals whose **location is free**.  This module isolates the family for which the refutation
does *not* apply, and proves the principle there.

## The observation

A transducer state acts on `(0,1)` by a **monotone** Möbius map.  So the pullback of an
output event of the form "the output point is `< c`" — i.e. "the next output digit is large",
which is exactly the tail cell `cellSet [] T` and hence exactly what `ImageTight` is about — is a
**downward-closed** subset of `(0,1)`, not an arbitrary interval.  Monotonicity anchors the target
to an endpoint, and an anchored target of small measure is *contained in a fixed interval*:

* `subset_Ioc_of_downwardClosed` — a downward-closed `A ⊆ (0,1)` with `|A| ≤ c` satisfies
  `A ⊆ (0,c]`.  (If some `t > c` lay in `A`, all of `(0,t)` would.)

Once every target of the family sits inside the *same* interval `(0,c)`, the moving target is gone
and lap 63's interval bound applies verbatim:

* `anchoredHitCount_le` / `anchoredHitFreq_le` — for a CF-normal `x` and any predictable family of
  endpoint-anchored targets with thresholds `u n ≤ c` and `v n ≥ 1 − c`,
  `freq{n : Gⁿx < u n ∨ Gⁿx > v n} ≤ 2c/log 2 + ε`.

## Why this is the route fact

The refutation and this theorem together say exactly which half of §7 Problem 1 is soft-reachable:

* the **tail-cell / large-digit** half — `ImageTight`, directive fact 2's bad states — has
  endpoint-anchored pullbacks, and is therefore reachable by measure alone;
* the **general word** half — a cylinder `I_w` sits in the interior of `(0,1)`, its pullback is not
  anchored, and `not_gappedHitPrinciple` applies.

So the two obligations of the §7 chain are not two instances of one difficulty: one of them is
soft after all, and it is the one the chain currently carries as a hypothesis.

## Guard rule

Content locator: `subset_Ioc_of_downwardClosed` is where monotonicity is spent, and it is false
without it — an arbitrary set of measure `c` is not inside `(0,c]`.  Degenerate case: `c ≥ 1`
makes `anchoredHitFreq_le` weaker than the trivial bound `1`.
-/

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- **Anchoring.**  A downward-closed subset of `(0,1)` of measure at most `c` lies in `(0,c]`. -/
theorem subset_Ioc_of_downwardClosed {A : Set ℝ} {c : ℝ}
    (hA : A ⊆ Set.Ioo (0:ℝ) 1)
    (hdown : ∀ t ∈ A, ∀ t' : ℝ, 0 < t' → t' < t → t' ∈ A)
    (hvol : volume A ≤ ENNReal.ofReal c) :
    A ⊆ Set.Ioc (0:ℝ) c := by
  intro t ht
  have ht0 : 0 < t := (hA ht).1
  refine ⟨ht0, ?_⟩
  by_contra hc
  push_neg at hc
  have hsub : Set.Ioo (0:ℝ) t ⊆ A := fun t' ht' => hdown t ht t' ht'.1 ht'.2
  have h1 : volume (Set.Ioo (0:ℝ) t) ≤ ENNReal.ofReal c :=
    le_trans (measure_mono hsub) hvol
  rw [Real.volume_Ioo, sub_zero] at h1
  by_cases hcneg : 0 ≤ c
  · have := (ENNReal.ofReal_le_ofReal_iff hcneg).1 h1
    linarith
  · have hz : ENNReal.ofReal c = 0 := ENNReal.ofReal_eq_zero.2 (by linarith [not_le.1 hcneg])
    rw [hz, le_zero_iff] at h1
    have := ENNReal.ofReal_eq_zero.1 h1
    linarith

/-- **Anchoring, mirrored.**  An upward-closed subset of `(0,1)` of measure at most `c` lies in
`[1−c,1)`. -/
theorem subset_Ico_of_upwardClosed {A : Set ℝ} {c : ℝ}
    (hA : A ⊆ Set.Ioo (0:ℝ) 1)
    (hup : ∀ t ∈ A, ∀ t' : ℝ, t' < 1 → t < t' → t' ∈ A)
    (hvol : volume A ≤ ENNReal.ofReal c) :
    A ⊆ Set.Ico (1 - c) 1 := by
  intro t ht
  have ht1 : t < 1 := (hA ht).2
  refine ⟨?_, ht1⟩
  by_contra hcon
  push_neg at hcon
  have hsub : Set.Ioo t 1 ⊆ A := fun t' ht' => hup t ht t' ht'.2 ht'.1
  have h1 : volume (Set.Ioo t 1) ≤ ENNReal.ofReal c :=
    le_trans (measure_mono hsub) hvol
  rw [Real.volume_Ioo] at h1
  by_cases hcneg : 0 ≤ c
  · have := (ENNReal.ofReal_le_ofReal_iff hcneg).1 h1
    linarith
  · have hz : ENNReal.ofReal c = 0 := ENNReal.ofReal_eq_zero.2 (by linarith [not_le.1 hcneg])
    rw [hz, le_zero_iff] at h1
    have := ENNReal.ofReal_eq_zero.1 h1
    linarith

/-- The number of times, before `p`, that the orbit falls below its own lower threshold or above
its own upper one.  The thresholds may depend on `n` however they like — that is the whole point:
predictability is free here. -/
noncomputable def anchoredHitCount (u v : ℕ → ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  ((Finset.range p).filter
    (fun n => gaussMap^[n] x < u n ∨ v n < gaussMap^[n] x)).card

theorem anchoredHitCount_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    {u v : ℕ → ℝ} {c : ℝ} (hu : ∀ n, u n ≤ c) (hv : ∀ n, 1 - c ≤ v n) (p : ℕ) :
    anchoredHitCount u v p x
      ≤ blockCount (Set.Ioo (0:ℝ) c) p x + blockCount (Set.Ioo (1 - c) 1) p x := by
  classical
  have hsplit : ∀ n ∈ Finset.range p,
      (if gaussMap^[n] x < u n ∨ v n < gaussMap^[n] x then (1:ℝ) else 0)
        ≤ blockIndic (Set.Ioo (0:ℝ) c) (gaussMap^[n] x)
          + blockIndic (Set.Ioo (1 - c) 1) (gaussMap^[n] x) := by
    intro n _
    obtain ⟨h0, h1⟩ := (irrational_orbit x hirr hmem n).2
    by_cases hcase : gaussMap^[n] x < u n ∨ v n < gaussMap^[n] x
    · rw [if_pos hcase]
      rcases hcase with hlt | hgt
      · have hin : gaussMap^[n] x ∈ Set.Ioo (0:ℝ) c := ⟨h0, lt_of_lt_of_le hlt (hu n)⟩
        have : blockIndic (Set.Ioo (0:ℝ) c) (gaussMap^[n] x) = 1 := by
          rw [blockIndic, Set.indicator_of_mem hin]; rfl
        rw [this]
        linarith [blockIndic_nonneg (Set.Ioo (1 - c) 1) (gaussMap^[n] x)]
      · have hin : gaussMap^[n] x ∈ Set.Ioo (1 - c) 1 :=
          ⟨lt_of_le_of_lt (hv n) hgt, h1⟩
        have : blockIndic (Set.Ioo (1 - c) 1) (gaussMap^[n] x) = 1 := by
          rw [blockIndic, Set.indicator_of_mem hin]; rfl
        rw [this]
        linarith [blockIndic_nonneg (Set.Ioo (0:ℝ) c) (gaussMap^[n] x)]
    · rw [if_neg hcase]
      linarith [blockIndic_nonneg (Set.Ioo (0:ℝ) c) (gaussMap^[n] x),
        blockIndic_nonneg (Set.Ioo (1 - c) 1) (gaussMap^[n] x)]
  have hcard : anchoredHitCount u v p x
      = ∑ n ∈ Finset.range p,
          (if gaussMap^[n] x < u n ∨ v n < gaussMap^[n] x then (1:ℝ) else 0) := by
    rw [anchoredHitCount, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp
  rw [hcard, blockCount_apply, blockCount_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hsplit

/-- **The anchored hit principle.**  Unlike `not_gappedHitPrinciple`'s free-location family, an
endpoint-anchored predictable family obeys the bound its measure suggests. -/
theorem anchoredHitFreq_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Set.Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {u v : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hu : ∀ n, u n ≤ c) (hv : ∀ n, 1 - c ≤ v n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, anchoredHitCount u v p x / (p:ℝ) ≤ 2 * c / Real.log 2 + ε := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := blockCount_Ioo_le' hirr hmem hx (show (0:ℝ) ≤ c from hc) (δ := ε / 8) (by linarith)
  have h2 := blockCount_Ioo_le' hirr hmem hx (show (1:ℝ) - c ≤ 1 by linarith) (δ := ε / 8)
    (by linarith)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with p hp1 hp2 hp0
  have hppos : (0:ℝ) < p := by exact_mod_cast hp0
  have hle := anchoredHitCount_le hirr hmem hu hv p
  have hdiv : anchoredHitCount u v p x / (p:ℝ)
      ≤ blockCount (Set.Ioo (0:ℝ) c) p x / (p:ℝ)
        + blockCount (Set.Ioo (1 - c) 1) p x / (p:ℝ) := by
    rw [← add_div]
    gcongr
  have hsimp : (1:ℝ) - (1 - c) = c := by ring
  rw [hsimp] at hp2
  have : (c - 0) / Real.log 2 = c / Real.log 2 := by ring_nf
  rw [this] at hp1
  have hdouble : 2 * c / Real.log 2 = c / Real.log 2 + c / Real.log 2 := by ring
  rw [hdouble]
  linarith [hdiv, hp1, hp2]

section Audit

#print axioms subset_Ioc_of_downwardClosed
#print axioms subset_Ico_of_upwardClosed
#print axioms anchoredHitCount_le
#print axioms anchoredHitFreq_le

end Audit

end NormalNumbers.VandeheyS7
