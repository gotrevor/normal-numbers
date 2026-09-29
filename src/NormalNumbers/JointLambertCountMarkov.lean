/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.JointLambertCountTail

/-!
# Markov at a fixed threshold, keeping the CARDINALITY

The qualitative proof extracts *one* candidate index whose discrepancy tail is small.  The
counting argument of `docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md` §4 must instead keep the
**cardinality** of the surviving set, because that cardinality is what becomes the count
`A(N)`.  This module is that step, and nothing else: an elementary Markov inequality on a
`Finset`, with the threshold `θ` **fixed** (the note's `2δ`, a constant of the fixed bases
and words — never a function of `N`).

* `card_bad_le` — `#{m ∈ S : θ < f m} ≤ E / θ` when `∑_{m∈S} f m ≤ E`.
* `card_good_ge` — hence `#{m ∈ S : f m ≤ θ} ≥ #S − E / θ`.
* `card_good_ge_half` — the form the assembly uses: if the total tail is at most half the
  candidate scale, at least half the candidates survive.

The good set is a genuine `Finset`, so `jointWordCount_ge_of_subset` can consume it.
-/

namespace NormalNumbers.JointLambert

open Finset

/-- **Markov, upper form.**  At most `E/θ` indices exceed the fixed threshold `θ`. -/
theorem card_bad_le {S : Finset ℕ} {f : ℕ → ℝ} {θ E : ℝ} (hθ : 0 < θ)
    (hf : ∀ m ∈ S, 0 ≤ f m) (hsum : ∑ m ∈ S, f m ≤ E) :
    (((S.filter (fun m => θ < f m)).card : ℕ) : ℝ) ≤ E / θ := by
  classical
  have hlow : θ * ((S.filter (fun m => θ < f m)).card : ℝ)
      ≤ ∑ m ∈ S.filter (fun m => θ < f m), f m := by
    rw [mul_comm, ← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ ?_
    intro m hm
    exact le_of_lt (Finset.mem_filter.mp hm).2
  have hsub : ∑ m ∈ S.filter (fun m => θ < f m), f m ≤ ∑ m ∈ S, f m := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro m hmS _
    exact hf m hmS
  rw [le_div_iff₀ hθ, mul_comm]
  linarith

/-- **Markov, good-set form.**  The surviving set is a `Finset` and its cardinality is at
least `#S − E/θ`. -/
theorem card_good_ge {S : Finset ℕ} {f : ℕ → ℝ} {θ E : ℝ} (hθ : 0 < θ)
    (hf : ∀ m ∈ S, 0 ≤ f m) (hsum : ∑ m ∈ S, f m ≤ E) :
    (S.card : ℝ) - E / θ ≤ (((S.filter (fun m => f m ≤ θ)).card : ℕ) : ℝ) := by
  classical
  have hsplit : (S.filter (fun m => f m ≤ θ)).card + (S.filter (fun m => ¬ (f m ≤ θ))).card
      = S.card := Finset.card_filter_add_card_filter_not (s := S) _
  have hcongr : S.filter (fun m => ¬ (f m ≤ θ)) = S.filter (fun m => θ < f m) := by
    refine Finset.filter_congr fun m _ => ?_
    simp [not_le]
  rw [hcongr] at hsplit
  have hbad := card_bad_le hθ hf hsum
  have hcast : ((S.filter (fun m => f m ≤ θ)).card : ℝ)
      + ((S.filter (fun m => θ < f m)).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
  linarith

/-- The assembly form: if the total tail is at most `θ · c / 2` and the candidate set has at
least `c` elements, at least `c / 2` survive. -/
theorem card_good_ge_half {S : Finset ℕ} {f : ℕ → ℝ} {θ E c : ℝ} (hθ : 0 < θ)
    (hf : ∀ m ∈ S, 0 ≤ f m) (hsum : ∑ m ∈ S, f m ≤ E)
    (hc : c ≤ (S.card : ℝ)) (hE : E ≤ θ * c / 2) :
    c / 2 ≤ (((S.filter (fun m => f m ≤ θ)).card : ℕ) : ℝ) := by
  have hmain := card_good_ge hθ hf hsum
  have hEθ : E / θ ≤ c / 2 := by
    rw [div_le_iff₀ hθ]
    linarith
  linarith

/-! ### Permanent boundary controls -/

/-- Empty candidate set: the bound is vacuous but true. -/
example {f : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ) :
    ((((∅ : Finset ℕ).filter (fun m => f m ≤ θ)).card : ℕ) : ℝ) = 0 := by simp

/-- Singleton control, threshold met: the single index survives. -/
example : (({0} : Finset ℕ).filter (fun m : ℕ => ((m : ℝ)) ≤ 1)).card = 1 := by
  classical
  rw [Finset.filter_singleton]
  norm_num

/-- Singleton control, threshold exceeded: nothing survives, and Markov's `E/θ = 1`
accounts for exactly the one lost index. -/
example : (({2} : Finset ℕ).filter (fun m : ℕ => ((m : ℝ)) ≤ 1)).card = 0 := by
  classical
  rw [Finset.filter_singleton]
  norm_num

end NormalNumbers.JointLambert
